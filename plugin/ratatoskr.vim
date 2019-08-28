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
" const [s:shift, s:reduce, s:error] = [0x8000, 0x4000, 0x2000]

" Returns the parse tables for the specified LR(0) grammar.
"
" {grammar} is a List of the productions.
function! s:BuildTables(grammar, num_non_terminals, num_symbols, eof) abort
	let [nonterminals, terminals] = [range(a:num_non_terminals), range(a:num_non_terminals, a:num_symbols - 1)]

	" Returns whether the specified symbol is nonterminal.
	function! IsNonTerminal(symbol) abort closure
		call assert_true(type(a:symbol) == v:t_number
					\ && a:symbol >= 0 && a:symbol < a:num_symbols, 'Invalid symbol')
		return a:symbol < a:num_non_terminals " Nonterminal symbols are given the smaller id:s
	endfunction
	let IsTerminal = {symbol -> !IsNonTerminal(symbol)}

	" Returns the closure of the specified item set.
	"
	" Modifies the specifed list in-situ.
	function! Closure(item_set) abort closure
		let i = 0
		while i < len(a:item_set)
			let item = a:item_set[i]
			" If the item set contains an item with the cursor just to the left of some nonterminal N
			let N = item.production.rhs->get(item.cursor, -1)
			if N != -1 && IsNonTerminal(N)
				" Add to the item set all initial items for the N-productions of the grammar, recursively
				for production in a:grammar
					if production.lhs isnot# N | continue | endif
					let new_item = #{production: production, cursor: 0}
					if a:item_set->index(new_item) == -1 | call add(a:item_set, new_item) | endif " Only add if unique
				endfor
			endif
			let i += 1
		endwhile
		return a:item_set
	endfunction

	" Returns Goto(I, X) = Closure({A → aX•b | A -> a•Xb in I}).
	"
	" Modifies the specified list in-situ.
	let Goto = {item_set, x -> item_set->filter({k, v -> v.production.rhs->get(v.cursor, -1) == x})
				\ ->map({k, v -> extend(v, #{cursor: v.cursor + 1})})->Closure()}

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
			let x = item.production.rhs->get(item.cursor, -1) " Symbol to the right of dot
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
			let goto[i][edge.symbol] = edge.to " Goto to that state
			if IsTerminal(edge.symbol)
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
			if item.production.lhs == -1 && item.production.rhs->get(item.cursor, -1) == a:eof
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
		let id = extracted_symbols->get(a:x, -1)
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
	let pattern = '\(' .. a:regexes->items()->sort({a, b -> symbol_map[a[0]] - symbol_map[b[0]]})
				\ ->map({i, v -> v[1]})->join('\)\|\(') .. '\)'
	echom 'Lexer pattern: ' .. pattern

	let lexer = {}
	function lexer.new() closure
		let new = copy(self)
		let new.offset = 0 " Byte offset previously lexed
		let new.has_eof = 0
		return new
	endfunction
	" Positions the cursor for lexing the node at the specified offset.
	function lexer.set_offset(offset)
		let self.offset = a:offset
		let lnum = byte2line(a:offset + 1)
		let col = a:offset + 2 - line2byte(lnum)
		call cursor(lnum, col)
		return [lnum, col]
	endfunction
	function lexer.advance() closure
		if self.has_eof | return [eof, 0] | endif

		" TODO Position cursor on char before and don't accept match at cursor
		" pos instead
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
		let length = byte - self.offset
		let self.offset = byte
		echom 'Lexed symbol: ' .. symbol_to_name[symbol] .. ', length: ' .. length
		return [symbol, length]
	endfunction

	return #{
				\ tables: tables, lexer: lexer,
				\ num_non_terminals: num_non_terminals, eof: eof,
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

" Adjust the byte lengths of the specified node given an edit.
"
" Should be done before re-parsing. The edit must be entirely contained inside
" node. {edit} may be modified in-place.
function! s:EditRanges(node, edit) abort
	" Validate edit range
	if a:edit.start < 0 || a:edit.old_end > a:node.length
		throw 'Edit is outside this node'
	endif

	let a:node.modified = 1
	" Enlarge according to edit length difference
	let a:node.length += a:edit.new_end - a:edit.old_end

	" Edit child ranges
	let child = get(a:node, 'first_child', v:null)
	while type(child) != v:t_string && child isnot# v:null
		let old_child_length = child.length " Store child len before it might change
		if a:edit.start <= child.length
			let child_edit = copy(a:edit)
			if child_edit.old_end > child.length | let child_edit.old_end = child.length | endif
			call s:EditRanges(child, child_edit) " Recurse

			let a:edit.new_end = 0 " Distribute all new len to first child
		else
			let a:edit.new_end -= child.length
		endif

		let a:edit.start -= old_child_length
		if a:edit.start < 0 | let a:edit.start = 0 | endif
		let a:edit.old_end -= old_child_length
		if a:edit.old_end <= 0 | break | endif

		let child = get(child, 'right_sibling', v:null)
	endwhile
endfunction

function! s:IncParse(lang, node) abort
	let save_cursor = getcurpos()
	try
		call cursor(1, 1)

		let actions = a:lang.tables.actions | let goto = a:lang.tables.goto
		let num_non_terminals = a:lang.num_non_terminals
		let eof = a:lang.eof
		let IsTerminal = {symbol -> symbol >= num_non_terminals}

		let lex = a:lang.lexer.new()
		" Initialize the parse stack to contain only bos
		let stack = #{stack: []}
		function stack.push(node) abort closure
			call extend(self.stack, [state, a:node])
		endfunction
		function stack.pop() abort closure
			let [state, node] = remove(self.stack, -2, -1)
			return node
		endfunction
		let root = #{symbol: -3}
		let bos = #{symbol: -1, length: 0, parent: root, right_sibling: a:node}
		let eos = #{symbol: a:lang.eof, length: 0, parent: root}
		let a:node.parent = root | let a:node.right_sibling = eos
		let root.first_child = bos
		let state = 0 | call stack.push(bos)

		" let la = PopLookahead(bos) " Set lookahead to root of tree
		let la = a:node
		let offset = 0 " Byte offset for lexing

		" Decompose a nonterminal lookahead.
		function! LeftBreakdown(la) abort closure
			return has_key(a:la, 'first_child') ? a:la.first_child : PopLookahead(a:la)
		endfunction
		" Pop right stack by traversing previous tree structure.
		function! PopLookahead(la) abort closure
			let node = a:la
			while !has_key(node, 'right_sibling')
				echom 'PopLookahead: node: ' .. node.symbol
				if !has_key(node, 'parent') | return eos | endif
				let node = node.parent
			endwhile
			return node.right_sibling
		endfunction

		" Shift a node onto the parse stack and update the current parse
		" state.
		function! Shift(node) abort closure
			call stack.push(a:node)
			let state = goto[state][a:node.symbol]
		endfunction

		" Remove any subtrees on top of parse stack with null yield, then
		" break down right edge of topmost subtree.
		function! RightBreakdown() abort closure
			while 1 " Replace top of stack with its children
				let node = stack.pop()
				" Does nothing when node is a terminal symbol
				if node->has_key('first_child')
					let child = node.first_child
					while 1
						call Shift(child)
						if !has_key(child, 'right_sibling') | break | endif
						let child = child.right_sibling
					endwhile
				endif
				if IsTerminal(node.symbol) | break | endif
			endwhile
			call Shift(node) " Leave final terminal symbol on top of stack
		endfunction

		function! Reduce(action) abort closure
			let L = action.arity
			let parent = #{symbol: action.lhs, length: 0} " TODO Reuse parent
			let last_child = {}
			" TODO Use last child to check for prev parent
			for i in range(L)
				let child = stack.pop()
				let child.parent = parent
				let parent.length += child.length
				if last_child != {}
					let child.right_sibling = last_child
				else
					if child->has_key('right_sibling') | unlet! child.right_sibling | endif
				endif
				let last_child = child
			endfor
			let parent.first_child = child
			let parent.modified = 0

			call stack.push(parent)
			let state = goto[state][action.lhs]
		endfunction

		" Relex a continuous region of modified nodes.
		function! Relex() abort closure
			let cur = lex.set_offset(offset)
			echom 'Relexing at ' .. string(cur)
			let diff = 0 " Cursor offset to start of the current lookahead
			let first = 1
			let node = la
			let cycles = 0

			" FIXME The control graph is needlessly complicated
			while 1
				let should_move_to_next = 1
				let [symbol, length] = lex.advance()

				" Check if node reuse is possible
				if symbol == node.symbol
					echom 'Reusing node! oldlen: ' .. node.length
					let diff += length - node.length
					let node.length = length " Update length
					let node.modified = 0
				else
					echom 'Could not reuse node: ' .. node.symbol
					" Either drop the old node or insert before, depending on if
					" we have moved past it
					let new_node = #{symbol: symbol, length: length}
					if diff >= node.length " Drop
						echom 'Dropping old node'
						let diff += length - node.length
						if node->has_key('parent') | let new_node.parent = node.parent | endif
						if node->has_key('right_sibling') | let new_node.right_sibling = node.right_sibling | endif
					else " Insert before
						echom 'Insert before'
						let diff += length
						let new_node.right_sibling = node
						if node->has_key('parent') | let new_node.parent = node.parent | endif
						let should_move_to_next = 0
					endif

					if first
						let la = new_node
					else
						let prev.right_sibling = new_node
						let node = new_node
					endif
				endif

				echom 'Diff is ' .. diff
				if diff == 0 | break | endif " If synced up, break
				let first = 0
				if should_move_to_next
					let prev = node
					if lex.has_eof
						echom 'Has eof!'
						let node = eos
					else
						" Move to the next terminal
						let node = PopLookahead(node)
						while !IsTerminal(node.symbol) | let node = LeftBreakdown(node) | endwhile
					endif
					let prev.right_sibling = node
				endif
				let cycles += 1
				if cycles > 5 | break | endif
			endwhile
		endfunction

		while 1
			echomsg 'La is ' .. g:lang.symbol_to_name[la.symbol] .. ', modified: ' .. la->get('modified', 0)
			if IsTerminal(la.symbol)
				if get(la, 'modified', 0)
					call Relex()
					echomsg ' After relex'
					let child = la
					while 1
						echomsg 'Child: ' .. g:lang.symbol_to_name[child.symbol] .. ' len: ' .. child.length
						if !has_key(child, 'right_sibling') | break | endif
						let child = child.right_sibling
					endwhile
				else
					let action = actions[state][la.symbol - num_non_terminals]
					echomsg 'Nondirty terminal: ' .. la.symbol .. ' Doing action: ' .. string(action)

					if type(action) == v:t_string && action == 'error'
						call Recover()
					elseif action.type == 'accept'
						if la is eos
							echom 'Parsed successfully!!'
							return
						else | call Recover() | endif
					elseif action.type == 'shift'
						call Shift(la)
						let offset += la.length
						let la = PopLookahead(la)
					elseif action.type == 'reduce'
						call Reduce(action)
					endif
				endif
			else " This is a nonterminal lookahead
				if get(la, 'modified', 0)
					let la = LeftBreakdown(la) " Split tree at changed points
				else
					" Perform all reductions possible
					" Reductions can only be processed with a terminal lookahead
					let next_terminal = eof " Legal since LR(0) grammar
					while 1
						let action = actions[state][next_terminal - num_non_terminals]
						if type(action) == v:t_dict && action.type == 'reduce'
							call Reduce(action)
						else | break | endif
					endwhile

					let shiftable = goto[state][la.symbol] isnot -1
					echom 'Shiftable nonterminal?: ' .. string(shiftable)
					if shiftable
						" Place lookahead on stack with its right-hand edge removed
						let offset += la.length
						call Shift(la) | call RightBreakdown() | let la = PopLookahead(la)
					else | let la = LeftBreakdown(la) | endif
				endif
			endif
		endwhile
	finally | call setpos('.', save_cursor) | endtry
endfunction

function! s:Listener(bufnr, start, end, added, changes) abort
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
	echomsg 'lines ' .. a:start .. ' until ' .. a:end .. ' changed; added: ' .. a:added
				\ .. ', edit: ' .. string(edit)

	if type(b:node) == v:t_number && b:node == v:null | return | endif
	call s:EditRanges(b:node, edit) " Adjust node ranges
endfunction

function! ParseBuffer() abort
	let b:node = Parse(g:lang)

	if exists('b:listener_id') | call listener_remove(b:listener_id) | endif
	let b:listener_id = listener_add(funcref('s:Listener'))

	return b:node
endfunction

function! IncParseBuffer() abort
	return s:IncParse(g:lang, b:node)
endfunction

function! GetSyntaxNode(lnum, col) abort
	let byte = line2byte(a:lnum) - 1 + a:col
	let node = b:node
	let stack = [node]
	let offset = 0
	echom 'Root len: ' .. node.length

	while has_key(node, 'first_child')
		" Output debug information
		echomsg 'Top level: -------'
		if has_key(node, 'first_child')
			let child = node.first_child
			while 1
				echomsg 'Child: ' .. g:lang.symbol_to_name[child.symbol] .. ' len: ' .. child.length
				if !has_key(child, 'right_sibling') | break | endif
				let child = child.right_sibling
			endwhile
		endif

		let node = node.first_child
		while offset + node.length < byte
			let offset += node.length
			let node = node.right_sibling
		endwhile
		call add(stack, node)
	endwhile

	" return stack
	return string(map(stack, {i, v -> g:lang.symbol_to_name[v.symbol]})) .. ', modified: ' .. node->get('modified', 0) .. ', length: ' .. node.length
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
