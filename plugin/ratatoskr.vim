" Incremental parser generator that compiles to VimL at runtime for
" indentation, syntax highlighting, etc.
"
" Then use `listener_add()` and the autocmd events BufReadPost and BufUnload
"
" Have to have great error recovery...
"
" See:
" * https://pages.github-dev.cs.illinois.edu/cs421-haskell/web-su19/files/handouts/lr-parsing-tables.pdf
" * https://dl.acm.org.sci-hub.tw/citation.cfm?id=357066

scriptversion 3

" Action bit masks. super non optimal
" TODO add accept
" Count on ~10x more productions than symbols
" let [s:shift, s:reduce, s:error] = [0x8000, 0x4000, 0x2000] | lockvar s:shift s:reduce s:error

" Returns the parse tables for the specified LR(0) grammar.
"
" {grammar} is a List of the productions.
function! s:BuildTables(grammar, num_non_terminals, num_symbols, eof) abort
	let [nonterminals, terminals] = [range(a:num_non_terminals), range(a:num_non_terminals, a:num_symbols - 1)]

	" Returns whether the specified symbol is non-terminal.
	function! IsNonTerminal(symbol) abort closure
		call assert_true(type(a:symbol) == v:t_number
					\ && a:symbol >= 0 && a:symbol < a:num_symbols, 'Invalid symbol')
		return a:symbol < a:num_non_terminals " Non-terminal symbols are given the smaller id:s
	endfunction
	let IsTerminal = {symbol -> !IsNonTerminal(symbol)}

	" Returns the closure of the specified item set.
	"
	" Modifies the specifed list in-situ.
	function! Closure(item_set) abort closure
		let i = 0
		while i < len(a:item_set)
			let item = a:item_set[i]
			" If the item set contains an item with the cursor just to the left of some non-terminal N
			let N = get(item.production.rhs, item.cursor, -1)
			if N != -1 && IsNonTerminal(N)
				" Add to the item set all initial items for the N-productions of the grammar, recursively
				for production in a:grammar
					if production.lhs isnot# N | continue | endif
					let new_item = #{production: production, cursor: 0}
					if index(a:item_set, new_item) == -1 | call add(a:item_set, new_item) | endif " Only add if unique
				endfor
			endif
			let i += 1
		endwhile
		return a:item_set
	endfunction

	" Returns Goto(I, X) = Closure({A → aX•b | A -> a•Xb in I}).
	"
	" Modifies the specified list in-situ.
	let Goto = {item_set, x -> Closure(map(filter(item_set, {k, v -> get(v.production.rhs, v.cursor, -1) == x}),
				\ {k, v -> extend(v, #{cursor: v.cursor + 1})}))}

	" Create the DFA

	" Augment grammar with a production S' -> S, where S is the start symbol
	" To generate the first item set, take the closure of the item S' -> •S
	let S = 0 " Assume that the start state has id 0
	let initial_item_set = Closure([#{production: #{lhs: -1, rhs: [S, a:eof]}, cursor: 0}])
	" echomsg 'Initial item set: ' .. string(initial_item_set)
	let states = [initial_item_set] " Map from state index to associated closure
	let edges = []
	let n = 0
	while n < len(states)
		let state = states[n]
		call add(edges, [])
		for item in state
			let x = get(item.production.rhs, item.cursor, -1) " Symbol to the right of dot
			if x != -1
				let goto = Goto(deepcopy(state), x)
				let n_prime = index(states, goto)
				if n_prime == -1
					let n_prime = len(states)
					call add(states, goto)
				endif

				" Add an edge X from state n to goto(I, X) state
				call add(edges[n], {'symbol': x, 'to': n_prime})
			endif
		endfor

		let n += 1
	endwhile

	" Build parse tables
	let actions = [] " Row for each state, column for each terminal
	let goto = [] " Row for each state, column for each symbol

	let i = 0
	for state in states
		call add(actions, map(range(len(terminals)), '"error"'))
		call add(goto, map(range(a:num_symbols), -1))

		for edge in edges[i]
			if IsNonTerminal(edge.symbol)
				" Goto to that state
				let goto[i][edge.symbol] = edge.to
			else
				" Transition to another State using a Terminal Symbol is a shift to that State
				let actions[i][edge.symbol - a:num_non_terminals] = {'type': 'shift', 'next': edge.to}
			endif
		endfor

		" Given a final A-item for production P (A != S') fill corresponding
		" row with reduce action for P
		for item in state
			let A = item.production.lhs
			if item.cursor != len(item.production.rhs) || A == -1 | continue | endif

			for t in terminals
				let prev_action = actions[i][t - a:num_non_terminals]
				" Automatically fix Shift-Reduce Conflicts by not reducing when it would cause a conflict
				if type(prev_action) != v:t_string || prev_action != 'error' | continue | endif

				let actions[i][t - a:num_non_terminals] = {'type': 'reduce', 'lhs': A, 'arity': len(item.production.rhs)}
			endfor
		endfor

		" For every item set containing S' → w•eof, set accept in eof column
		for item in state
			if item.production.lhs == -1 && get(item.production.rhs, item.cursor, -1) == a:eof
				let actions[i][a:eof - a:num_non_terminals] = {'type': 'accept'}
				break
			endif
		endfor

		let i += 1
	endfor

	echomsg 'Actions'
	echomsg 'State | ' .. string(terminals)
	for n in range(len(actions))
		echomsg '' .. n .. ' | ' .. string(actions[n])
	endfor
	echomsg 'Goto'
	echomsg 'State | ' .. string(nonterminals) .. ' ' .. string(terminals)
	for n in range(len(goto))
		echomsg '' .. n .. ' | ' .. string(goto[n])
	endfor

	return #{ actions: actions, goto: goto, }
endfunction

" Converts string names for symbols in the grammar to numerical ids.
"
" Modifies the arguments in place.
function! s:ExtractSymbols(grammar) abort
	let extracted_symbols = {}
	let next_id = 0
	function ToId(x) abort closure
		let id = get(extracted_symbols, a:x, -1)
		if id == -1
			let id = next_id
			let extracted_symbols[a:x] = id
			let next_id += 1
		endif
		return id
	endfunction
	for production in a:grammar
		let production.lhs = ToId(production.lhs)
	endfor
	let num_non_terminals = next_id
	for production in a:grammar
		call map(production.rhs, {k, v -> ToId(v)})
	endfor

	let eof = next_id
	let num_symbols = next_id + 1

	return [a:grammar, extracted_symbols, num_non_terminals, num_symbols, eof]
endfunction

function! s:ReverseDict(dict) abort
	let result = {}
	for [k, v] in items(a:dict)
		let result[v] = k
	endfor
	return result
endfunction

" Constructs a language object from the specified grammar/regexes.
function! InitLanguage(grammar, regexes) abort
	let [grammar, symbol_map, num_non_terminals, num_symbols, eof] = s:ExtractSymbols(a:grammar)
	let num_terminals = num_symbols - num_non_terminals
	let symbol_to_name = s:ReverseDict(symbol_map)

	let tables = s:BuildTables(grammar, num_non_terminals, num_symbols, eof)

	" Build lexer regex pattern
	if len(a:regexes) isnot num_terminals - 1 | throw 'Bad number of terminal regexes' | endif
	let pattern = '\(' .. join(map(sort(items(a:regexes), {a, b -> symbol_map[a[0]] - symbol_map[b[0]]}),
				\ {i, v -> v[1]}), '\)\|\(') .. '\)'
	echom 'Lexer pattern: ' .. pattern

	let lexer = {}
	function lexer.new() closure
		let new = copy(self)
		let new.offset = 0 " Byte offset previously lexed
		let new.has_eof = 0
		return new
	endfunction
	function lexer.advance() closure
		if self.has_eof | return [eof, 0] | endif

		let [lnum, col, submatch] = searchpos(pattern, 'cepWz')
		if submatch <= 1
			echoerr 'Lexing: Invalid token'
		endif
		let byte = line2byte(lnum) - 1 + col
		silent execute "normal! 1\<Space>"
		let [bufnum, nlnum, ncol; rest] = getcurpos()
		" If cursor stayed in place it has reached EOF
		if nlnum == lnum && ncol == col | let self.has_eof = 1 | endif
		" If token at end of line: include EOL char
		if nlnum > lnum || ncol == col | let byte += 1 | endif

		let symbol = submatch - 2 + num_non_terminals
		echom 'Lexed symbol: ' .. symbol_to_name[symbol]
		let length = byte - self.offset
		echom 'Length: ' .. length
		let self.offset = byte
		return [symbol, length]
	endfunction

	return #{
				\ tables: tables, lexer: lexer,
				\ num_non_terminals: num_non_terminals,
				\ symbol_to_name: symbol_to_name,
				\ }
endfunction

function! Parse(lang) abort
	let save_cursor = getcurpos()
	try
		call cursor(1, 1)

		let actions = a:lang.tables.actions | let goto = a:lang.tables.goto
		let lexer = a:lang.lexer
		let num_non_terminals = a:lang.num_non_terminals

		" let lex = lexer.new('i=i+i;i')
		let lex = lexer.new()
		let bos = -1 " Symbol for bottom of stack
		let node = {'symbol': bos, 'state': 0}
		let [t, length] = lex.advance()

		while v:true
			let s = node.state

			let action = actions[s][t - num_non_terminals]

			echomsg 'Doing action: ' .. string(action)

			if type(action) == v:t_string && action == 'error'
				" Error
				echomsg 'Error: stack: ' .. string(node)
				throw 'Bad input'
			elseif action.type == 'accept'
				" Finished successfully
				echomsg 'Success: stack: ' .. string(node)
				break
			elseif action.type == 'shift'
				let node = #{symbol: t, state: action.next, predecessor: node, length: length}
				let [t, length] = lex.advance() " Scan the next input symbol into the lookahead buffer
			elseif action.type == 'reduce'
				let L = action.arity
				let parent = {'symbol': action.lhs, 'length': 0}
				let last_child = {}
				for i in range(L)
					let child = node
					let child.parent = parent
					let parent.length += child.length
					if last_child != {}
						let child.right_sibling = last_child
					endif
					let last_child = child

					let node = child.predecessor
				endfor
				let parent.first_child = child
				let parent.predecessor = node
				let parent.state = goto[node.state][action.lhs]
				let node = parent
			endif
		endwhile

		return node

		" Inc parse
		let stack = [] | let s = 0
		let la = node " Set lookahead to root of tree
		while v:true
			if IsTerminal(la.symbol)
				if la.has_changes()
					call relex(la) " TODO Do incremental lexing before incremental parsing. Possible?
					let la = ...
				else
					let action = actions[s][la.symbol]

					if type(action) == v:t_string && action == 'error'
						call recover()
					elseif action.type == 'accept'
						if la == eof | return | else | call recover() | endif
					elseif action.type == 'shift'
						call shift(action.next)
						let la = PopLookahead(la)
					elseif action.type == 'reduce'
						call reduce(r) " TODO
					endif
				endif
			else
				" This is a non-terminal lookahead
				if la.has_changes()
					let la = LeftBreakdown(la) " Split tree at changed points
				else
					" Reductions can only be processed with a terminal lookahead
					let NextTerminal = {la -> eof} " Legal since LR(0) grammar
					call PerformAllReductionsPossible(NextTerminal(la))
					if (shiftable(la))
						call shift(la)
						" Do not have to do right breakdown since LR(0) grammar
					else
						let la = LeftBreakdown()
					endif
				endif
			endif

			break
		endwhile
	finally | call setpos('.', save_cursor) | endtry
endfunction

" List of productions
let s:grammar = [
			\ {'lhs': 'S', 'rhs': ['S', ';', 'A']},
			\ {'lhs': 'S', 'rhs': ['A']},
			\ {'lhs': 'A', 'rhs': ['E']},
			\ {'lhs': 'A', 'rhs': ['i', '=', 'E']},
			\ {'lhs': 'E', 'rhs': ['E', '+', 'i']},
			\ {'lhs': 'E', 'rhs': ['i']},
			\ ]

let s:regexes = {
			\ ';': '\s*;\s*',
			\ '+': '\s*+\s*',
			\ '=': '\s*=\s*',
			\ 'i': '\s*\d\+\s*',
			\ }

let v:errors = []
let lang = InitLanguage(s:grammar, s:regexes)

function! s:EditRanges(node, edit) abort
	" If edit is entirely past this node
	if edit.start > node.length | return | endif

endfunction

function! s:Listener(bufnr, start, end, added, changes) abort
	echom 'lines ' .. a:start .. ' until ' .. a:end .. ' changed; added: ' .. a:added

	if type(b:node) == v:t_number && b:node == v:null | return | endif

	" Create appropriate edit structure
	let old_len = b:node.length
	let new_len = line2byte(line('$') + 1) - 1
	let new_end = line2byte(a:end + a:added) - 1
	" Inclusive start, exclusive end, all byte counts
	let edit = #{
				\ start: line2byte(a:start) - 1,
				\ new_end: new_end,
				\ old_end: new_end + (old_len - new_len),
				\ }
	echomsg edit
endfunction

function! ParseBuffer() abort
	let b:node = Parse(g:lang)

	if exists('b:listener_id') | call listener_remove(b:listener_id) | endif
	let b:listener_id = listener_add(funcref('s:Listener'))
endfunction

function! GetSyntaxNode(lnum, col) abort
	let byte = line2byte(a:lnum) - 1 + a:col
	let node = b:node
	let stack = [node]
	let offset = 0
	while has_key(node, 'first_child')
		let node = node.first_child
		while offset + node.length < byte
			let offset += node.length
			let node = node.right_sibling
		endwhile
		call add(stack, node)
	endwhile

	" return stack
	return map(stack, {i, v -> g:lang.symbol_to_name[v.symbol]})
endfunction

function! GetSyntaxNodeUnderCursor() abort
	return GetSyntaxNode(line('.'), col('.'))
endfunction

" On the topic of DS for storing node span information:
"
" Don't really want to store lnum since would have to update all when lines
" are added/removed
"
" For that reason just storing byte length is probably nicest

for error in v:errors | echoerr error | endfor
