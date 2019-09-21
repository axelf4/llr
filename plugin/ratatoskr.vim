" Incremental parser generator that compiles to VimL at runtime for
" indentation, syntax highlighting, etc.
"
" Then use `listener_add()` and the autocmd events BufReadPost and BufUnload
"
" See:
" * https://pages.github-dev.cs.illinois.edu/cs421-haskell/web-su19/files/handouts/lr-parsing-tables.pdf
" * https://dl.acm.org.sci-hub.tw/citation.cfm?id=357066

scriptversion 3

" Action bit masks. super non optimal
" TODO add accept
" Count on ~10x more productions than symbols
" const [s:shift, s:reduce, s:error] = [0x8000, 0x4000, 0x2000]
const s:error_sym = -1 " The builtin nonterminal error symbol.

" Returns the parse tables for the specified LR(0) grammar.
"
" {grammar} is a List of the productions.
function! s:BuildTables(grammar, num_non_terminals, num_symbols, eof) abort
	let [nonterminals, terminals] = [range(a:num_non_terminals), range(a:num_non_terminals, a:num_symbols - 1)]

	" Returns whether the specified symbol is nonterminal.
	function! IsNonTerminal(symbol) abort closure
		if type(a:symbol) != v:t_number || a:symbol < 0 || a:symbol >= a:num_symbols
			throw 'Invalid symbol'
		endif
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
	let Goto = {item_set, x -> item_set->filter({_, v -> v.production.rhs->get(v.cursor, -1) == x})
				\ ->map({_, v -> extend(v, #{cursor: v.cursor + 1})})->Closure()}

	" Create the DFA
	" Augment grammar with a production S' -> S, where S is the start symbol
	" To generate the first item set, take the closure of the item S' -> •S
	let S = 0 " Assume that the start symbol has id 0
	let initial_item_set = Closure([#{production: #{lhs: -1, rhs: [S, a:eof]}, cursor: 0}])
	let states = [#{item_set: initial_item_set, edges: {}}]
	let n = 0
	while n < len(states)
		let state = states[n]

		for item in state.item_set
			let x = item.production.rhs->get(item.cursor, -1) " Symbol to the right of dot
			if x != -1
				let goto = Goto(deepcopy(state.item_set), x)
				" Check if state already exists
				let n_prime = -1
				for i in range(len(states))
					if states[i].item_set == goto
						let n_prime = i
						break
					endif
				endfor
				" Otherwise add new state
				if n_prime == -1
					let n_prime = len(states)
					call add(states, #{item_set: goto, edges: {}})
				endif

				let state.edges[x] = n_prime " Add an edge X from state n to goto(I, X) state
			endif
		endfor

		let n += 1
	endwhile

	" Dictionary containing all nonterminals that may produce epsilon.
	let nullable = {}
	" Compute which nonterminals are nullable (simple O(n^2) algo)
	let should_continue = 1
	while should_continue
		let should_continue = 0
		for production in a:grammar
			if nullable->has_key(production.lhs) | continue | endif
			let is_nullable = 1
			for X in production.rhs
				if !(IsNonTerminal(X) && nullable->has_key(X))
					let is_nullable = 0
					break
				endif
			endfor
			if is_nullable
				let should_continue = 1
				let nullable[production.lhs] = 1
			endif
		endfor
	endwhile
	let IsNullable = {A -> nullable->has_key(A)}

	" Build the LALR(1) lookahead sets from the LR(0) automata, based on:
	" DeRemer, F. L., and T. J. Pennelo: "Efficient Computation of LALR(1)
	" Lookahead Sets", ACM Transactions on Programming Languages and Systems,
	" Vol. 4, No. 4, Oct. 1982, pp. 615-649

	let X = [] " The set of nonterminal transitions of the LR(0) parser
	for i in range(len(states))
		let state = states[i]
		for transition_symbol in state.edges->keys()->map({_, v -> str2nr(v)})
					\ ->filter({_, v -> IsNonTerminal(v)})
			eval X->add(#{state: i, symbol: transition_symbol})
		endfor
	endfor

	function! ToSet(a) abort
		let result = {}
		for x in a:a
			if type(x) != v:t_string && type(x) != v:t_number | throw 'Bad type' | endif
			let result[x] = 1
		endfor
		return result
	endfunction

	" Direct read symbols.
	"
	" Returns the symbols as the keys of a Dictionary.
	let DR = {p, A -> states[states[p].edges[A]].edges->keys()->ToSet()}

	" (p, A) READS (r, C) iff p --A-> r --C-> and C =>* eps
	let reads = X->copy()->map({_, trans -> states[trans.state].edges[trans.symbol]})
				\ ->map({_, r -> states[r].edges->keys()->filter({_, C -> IsNullable(C)})
				\ 	->map({_, C -> X->index(#{state: r, symbol: str2nr(C)})})})

	" (p, A) INCLUDES (p', B) iff B -> L A T,  T =>* eps, and p' --L-> p
	let includes = repeat([[]], len(X))
	" (q, A -> w) LOOKBACK (p, A) iff p --w-> q
	let lookback = []
	function! CalcIncludesLookback() closure abort
		for i in range(X->len())
			let transition = X[i]
			let state = states[transition.state]
			let B = transition.symbol

			for item in state.item_set
				" Consider only start B-items
				if item.production.lhs != B || item.cursor != 0 | continue | endif

				" Run the state machine forward
				let j = transition.state
				for cursor in range(item.cursor, item.production.rhs->len() - 1)
					let t = item.production.rhs[cursor]

					if cursor != 0
						" If this (symbol, state) is a nonterminal transition
						let trans2 = X->index(#{state: j, symbol: t})
						if trans2 != -1
							let remainingNullable = range(cursor + 1, item.production.rhs->len() - 1)
										\ ->map({_, v -> item.production.rhs[v]})
										\ ->filter({_, v -> !has_key(nullable, v)})->empty()
							if remainingNullable
								eval includes[trans2]->add(i)
							endif
						endif
					endif

					let j = states[j].edges[t]
				endfor

				" At this point j is the final state
				eval lookback->add(#{q: j, production: item.production, transition: i})
			endfor
		endfor
	endfunction
	call CalcIncludesLookback()

	" Digraph
	function! Digraph(X, R, FP) abort
		let stack = []
		let F = repeat([{}], len(a:X)) " Function from X to initially empty sets
		let N = repeat([0], len(a:X))

		function! Traverse(i, x) closure abort
			eval stack->add(a:i)
			let d = stack->len()
			let N[a:i] = d
			let F[a:i] = a:FP(a:x.state, a:x.symbol)

			for j in a:R[i]
				if N[j] == 0 | call Traverse(j, a:X[j]) | endif
				if N[j] < N[a:i] | let N[a:i] = N[j] | endif
				eval F[a:i]->extend(F[j])
			endfor

			if N[a:i] == d
				while 1
					let N[stack[-1]] = 1/0
					let F[stack[-1]] = F[a:i]
					if stack->remove(-1) is# i | break | endif
				endwhile
			endif
		endfunction

		for i in range(len(a:X)) | if N[i] == 0 | call Traverse(i, a:X[i]) | endif | endfor

		return F
	endfunction

	let Read = Digraph(X, reads, DR)
	let ReadFunc = {p, A -> Read[X->index(#{state: p, symbol: A})]}
	let Follow = Digraph(X, includes, ReadFunc)

	" LA(q, A -> w) = U{Follow(p, A) | (q, A -> w) lookback (p, A)}
	function! LA(q, production) closure abort
		let result = {} " Start with empty set
		for lb in lookback
			if lb.q == a:q && lb.production == a:production
				eval result->extend(Follow[lb.transition])
			endif
		endfor
		return result->keys()->map({_, v -> str2nr(v)})
	endfunction

	" Build parse tables
	let actions = [] " Row for each state, column for each symbol
	let goto = [] " Row for each state, column for each symbol

	let i = 0
	for state in states
		call add(actions, map(range(a:num_symbols), '"error"'))
		call add(goto, map(range(a:num_symbols), -1))

		for [symbol, to] in state.edges->items()
			let goto[i][symbol] = to " Goto to that state
			let actions[i][symbol] = {'type': 'shift'}
		endfor

		" Given a final A-item for production P (A != S') fill corresponding
		" row with reduce action for P
		for item in state.item_set
			let A = item.production.lhs
			if item.cursor != len(item.production.rhs) || A == -1 | continue | endif

			for s in LA(i, item.production)
				let prev_action = actions[i][s]
				" Check for ambiguous grammar
				if type(prev_action) != v:t_string || prev_action != 'error'
					throw 'Shift/reduce or reduce/reduce conflict'
				endif

				let actions[i][s] = {'type': 'reduce', 'lhs': A, 'arity': len(item.production.rhs)}
			endfor
		endfor

		" For every item set containing S' → w•eof, set accept in eof column
		for item in state.item_set
			if item.production.lhs == -1 && item.production.rhs->get(item.cursor, -1) == a:eof
				let actions[i][a:eof] = {'type': 'accept'}
				break
			endif
		endfor

		let i += 1
	endfor

	echomsg 'Actions'
	echomsg 'State | ' .. string(nonterminals) .. ' ' .. string(terminals)
	for n in range(len(actions))
		echomsg '' .. n .. ' | ' .. string(actions[n])
	endfor
	echomsg 'Goto'
	echomsg 'State | ' .. string(nonterminals) .. ' ' .. string(terminals)
	for n in range(len(goto))
		echomsg '' .. n .. ' | ' .. string(goto[n])
	endfor

	return #{actions: actions, goto: goto}
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
		call map(production.rhs, {_, v -> ToId(v)})
	endfor

	let etoken = next_id | let eof = next_id + 1 | let num_symbols = next_id + 2
	return [a:grammar, extracted_symbols, num_non_terminals, num_symbols, etoken, eof]
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
	let [grammar, symbol_map, num_non_terminals, num_symbols, etoken, eof] = s:ExtractSymbols(a:grammar)
	let num_terminals = num_symbols - num_non_terminals
	let symbol_to_name = s:ReverseDict(symbol_map)
	let symbol_to_name[eof] = '$'
	let symbol_to_name[etoken] = "LEXERR"
	let symbol_to_name[s:error_sym] = 'ERR'

	let tables = s:BuildTables(grammar, num_non_terminals, num_symbols, eof)

	" Build lexer regex pattern
	if len(a:regexes) isnot num_terminals - 2 | throw 'Bad number of terminal regexes' | endif
	let pattern = '\%#\(' .. a:regexes->items()->sort({a, b -> symbol_map[a[0]] - symbol_map[b[0]]})
				\ ->map({_, v -> v[1]})->join('\)\|\(') .. '\)\|\(.\+\)'
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
		let byte = line2byte(lnum) - 1 + col
		let prev_lnum = line('.')
		silent execute "normal! 1\<Space>"
		if submatch <= 1 " No match
			if prev_lnum == line('$') | let self.has_eof = 1 | endif
			return [etoken, 1]
		endif
		let [bufnum, nlnum, ncol; rest] = getcurpos()
		" If cursor stayed in place it has reached EOF
		if nlnum == lnum && ncol == col | let self.has_eof = 1 | endif
		" If token at end of line: include EOL char
		if nlnum > lnum || ncol == col | let byte += 1 | endif

		let symbol = submatch - 2 + num_non_terminals
		let length = byte - self.offset
		let self.offset = byte
		return [symbol, length]
	endfunction

	return #{
				\ tables: tables, lexer: lexer,
				\ num_non_terminals: num_non_terminals, eof: eof, etoken: etoken,
				\ symbol_to_name: symbol_to_name,
				\ }
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

function! s:IncParse(lang, node) abort
	let save_cursor = getcurpos()
	try
		call cursor(1, 1)

		let actions = a:lang.tables.actions | let goto = a:lang.tables.goto
		let num_non_terminals = a:lang.num_non_terminals
		let eof = a:lang.eof | let etoken = a:lang.etoken
		let IsTerminal = {symbol -> symbol >= num_non_terminals}

		let lex = a:lang.lexer.new()
		" Initialize the parse stack to contain only bos
		let stack = #{stack: []} " Stores [beginning_state, node]
		function stack.push(node) abort closure
			call extend(self.stack, [state, a:node])
		endfunction
		function stack.pop() abort closure
			let [state, node] = remove(self.stack, -2, -1)
			return node
		endfunction
		function stack.size() abort
			return self.stack->len() / 2
		endfunction
		function stack.is_empty() abort
			return self.stack->empty()
		endfunction
		let eos = #{symbol: a:lang.eof, length: 0}
		let state = 0 | let la = a:node " Set lookahead to root of tree
		let verifying = 0
		let offset = 0 " Byte offset for lexing

		" Decompose a nonterminal lookahead.
		function! LeftBreakdown(la) abort closure
			return a:la->has_key('first_child') ? a:la.first_child : PopLookahead(a:la)
		endfunction
		" Pop right stack by traversing previous tree structure.
		function! PopLookahead(la) abort closure
			let node = a:la
			while !has_key(node, 'right_sibling')
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

		let IsTransparent = {symbol -> symbol == s:error_sym || symbol == etoken}

		function! Reduce(action) abort closure
			let L = action.arity
			let parent = #{symbol: action.lhs, length: 0} " TODO Reuse parent
			let last_child = {}
			while L > 0 || IsTransparent(stack.stack->get(-1, eos).symbol)
				let child = stack.pop()
				if !IsTransparent(child.symbol)
					let L -= 1
				endif
				let child.parent = parent
				let parent.length += child.length
				if last_child != {}
					let child.right_sibling = last_child
				else
					if child->has_key('right_sibling') | unlet! child.right_sibling | endif
					if child->has_key('parent')
						if child.parent->has_key('parent') | let parent.parent = child.parent.parent | endif
						if child.parent->has_key('right_sibling') | let parent.parent = child.parent.right_sibling | endif
					endif
				endif
				let last_child = child
			endwhile
			let parent.first_child = child
			let parent.modified = 0

			call stack.push(parent)
			let state = goto[state][action.lhs]
		endfunction

		" Relex a continuous region of modified nodes.
		function! Relex() abort closure
			let cur = lex.set_offset(offset)
			let node = la
			let diff = 0 " Cursor offset to start of the current lookahead
			let need_new_node = 0
			let first = 1

			while 1
				let [symbol, length] = lex.advance()
				let diff += length

				while 1
					if !need_new_node
						if symbol == node.symbol || diff < node.length || node.symbol == eof
							break
						endif
						let diff -= node.length
					endif

					" Drop overrun node by moving to the next terminal
					let node = PopLookahead(node)
					while !IsTerminal(node.symbol) | let node = LeftBreakdown(node) | endwhile
					let need_new_node = 0
				endwhile

				if symbol == eof
					let new_node = eos
				elseif symbol == node.symbol " If node reuse is possible
					let diff -= node.length
					let node.length = length | let node.modified = 0
					let need_new_node = 1
					let new_node = node
				else
					let new_node = #{symbol: symbol, length: length, right_sibling: node}
					if node->has_key('parent') | let new_node.parent = node.parent | endif
				endif
				if first | let la = new_node | else | let prev.right_sibling = new_node | endif

				if diff == 0 | break | endif " If synced up, break
				let first = 0 | let prev = new_node
			endwhile
		endfunction

		" Simple panic mode error recovery.
		"
		" Returns a truthy value if should accept.
		function! Recover() abort closure
			let i = 0
			while i < stack.size()
				let stack_state = stack.stack[-2 * (1 + i)] | let stack_node = stack.stack[-2 * i - 1]
				let i += 1
				if IsTransparent(stack_node.symbol) | continue | endif
				let action = actions[stack_state][la.symbol]
				if !(type(action) == v:t_string && action == 'error')
					" Pop stack nodes until can continue and wrap them in an error node
					let error_node = #{symbol: s:error_sym, length: 0}
					for node in range(i)->map({-> stack.pop()})
						let node.parent = error_node
						let error_node.length += node.length
						let error_node.first_child = node

						if exists('last_child')
							let node.right_sibling = last_child
						else
							if node->has_key('right_sibling') | unlet! node.right_sibling | endif
						endif
						let last_child = node
					endfor
					call stack.push(error_node)
					return
				endif
			endwhile

			if la.symbol == eof
				" Wrap everything in error node
				let error_node = #{symbol: s:error_sym, length: 0}
				let last_child = {}
				while !(stack.stack->empty())
					let child = stack.pop()
					let child.parent = error_node
					let error_node.length += child.length
					if last_child != {}
						let child.right_sibling = last_child
					else
						if child->has_key('right_sibling') | unlet! child.right_sibling | endif
					endif
					let last_child = child
				endwhile
				if exists('child') | let error_node.first_child = child | endif
				call stack.push(error_node)
				return 1
			endif

			" Wrap lookahead in error node and push to stack
			let error_node = #{symbol: s:error_sym, length: la.length, first_child: la}
			let la = PopLookahead(la) " Advance la before changing its parent/siblings!
			let error_node.first_child.parent = error_node
			if error_node.first_child->has_key('right_sibling') | unlet! error_node.first_child.right_sibling | endif
			call stack.push(error_node)
		endfunction

		while 1
			if la->get('modified', 0)
				if IsTerminal(la.symbol) | call Relex()
				else | let la = LeftBreakdown(la) | endif " Split at changed point
				continue
			endif

			let action = actions[state][la.symbol]
			if type(action) != v:t_string && action.type == 'shift'
				let verifying = !IsTerminal(la.symbol)
				call Shift(la)
				let offset += la.length
				let la = PopLookahead(la)
			elseif type(action) != v:t_string && action.type == 'reduce'
				call Reduce(action)
			elseif type(action) == v:t_string && action == 'error'
				if IsTerminal(la.symbol)
					if verifying
						call RightBreakdown() " Delayed breakdown
						let verifying = 0
					else | call Recover() | endif " Actual parse error
				else | let la = LeftBreakdown(la) | endif
			elseif type(action) != v:t_string && action.type == 'accept' && stack.size() is 1
						\ || Recover()
				break
			endif
		endwhile

		return stack.pop()
	finally | call setpos('.', save_cursor) | endtry
endfunction

" Adjust the byte lengths of the specified node given an edit.
"
" Should be done before re-parsing. The edit must be entirely contained inside
" node. {edit} may be modified in-place.
function! s:EditRanges(node, edit) abort
	let stack = [a:node, a:edit]

	while !empty(stack)
		let [node, edit] = stack->remove(-2, -1)
		let node.modified = 1
		" Enlarge according to edit length difference
		let node.length += edit.new_end - edit.old_end

		" Edit child ranges
		if node->has_key('first_child')
			let child = node.first_child
			while 1
				if edit.start <= child.length
					let child_edit = copy(edit)
					if child_edit.old_end > child.length | let child_edit.old_end = child.length | endif
					call add(stack, child) | call add(stack, child_edit)

					let edit.new_end = 0 " Distribute all new len to first child
				else
					let edit.new_end -= child.length
				endif

				let edit.old_end -= child.length
				if edit.old_end <= 0 | break | endif
				let edit.start -= child.length
				if edit.start < 0 | let edit.start = 0 | endif

				if !has_key(child, 'right_sibling') | break | endif
				let child = child.right_sibling
			endwhile
		endif
	endwhile
endfunction

function! s:Listener(bufnr, start, end, added, changes) abort
	if !exists('b:node') | return | endif

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

	call s:EditRanges(b:node, edit) " Adjust node ranges
	call IncParseBuffer()
endfunction

function! ResetTree() abort
	if exists('b:listener_id') | call listener_remove(b:listener_id) | endif
	let b:listener_id = listener_add(funcref('s:Listener'))

	let b:node = #{symbol: g:lang.etoken, length: line2byte(line('$') + 1) - 1,
				\ modified: 1}
endfunction

function! IncParseBuffer() abort
	let b:node = s:IncParse(g:lang, b:node)
	return b:node
endfunction

function! GetSyntaxNode(lnum, col) abort
	let byte = line2byte(a:lnum) - 1 + a:col
	let node = b:node
	let stack = [node]
	let offset = 0

	while node->has_key('first_child')
		" Output debug information
		echomsg 'Top level: -------'
		let child = node
		while 1
			echomsg 'Child: ' .. g:lang.symbol_to_name[child.symbol] .. ' len: ' .. child.length
			if !has_key(child, 'right_sibling') | break | endif
			let child = child.right_sibling
		endwhile

		let node = node.first_child
		while offset + node.length < byte
			let offset += node.length
			let node = node.right_sibling
		endwhile
		call add(stack, node)
	endwhile

	" return stack
	return string(map(stack, {_, v -> g:lang.symbol_to_name[v.symbol]})) .. ', modified: ' .. node->get('modified', 0) .. ', length: ' .. node.length
endfunction

function! GetSyntaxNodeUnderCursor() abort
	return GetSyntaxNode(line('.'), col('.'))
endfunction

function! PrintTree(node, depth) abort
	echom repeat(' ', 4 * a:depth) .. g:lang.symbol_to_name[a:node.symbol] .. a:node.length
	if a:node->has_key('first_child')
		call PrintTree(a:node.first_child, a:depth + 1)
	endif
	if a:node->has_key('right_sibling')
		call PrintTree(a:node.right_sibling, a:depth)
	endif
endfunction

for error in v:errors | echoerr error | endfor
