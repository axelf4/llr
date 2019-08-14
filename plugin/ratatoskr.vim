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

" Action bit masks. super non optimal
" TODO add accept
let [shift, reduce, error] = [0x8000, 0x4000, 0x2000] | lockvar shift reduce error

" Returns the parse tables for the specified LR(0) grammar.
function! s:BuildTables(grammar, num_non_terminals, num_symbols) abort
	let eof = a:num_symbols | let num_symbols = a:num_symbols + 1
	let [nonterminals, terminals] = [range(a:num_non_terminals), range(a:num_non_terminals, a:num_symbols)]

	" Returns whether the specified symbol is non-terminal.
	function! IsNonTerminal(symbol) abort closure
		call assert_true(type(a:symbol) == v:t_number
					\ && a:symbol >= 0 && a:symbol < num_symbols, 'Invalid symbol')
		return a:symbol < a:num_non_terminals " Non-terminal symbols are given the smaller id:s
	endfunction
	let IsTerminal = {symbol -> !IsNonTerminal(symbol)}

	let item = {}
	function! item.new(production, cursor) dict
		let new = copy(self)
		let new.production = a:production
		let new.cursor = a:cursor
		return new
	endfunction

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
					let new_item = {'production': production, 'cursor': 0}
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
				\ {k, v -> extend(v, {'cursor': v.cursor + 1})}))}

	" Create the DFA

	" Augment grammar with a production S' -> S, where S is the start symbol
	" To generate the first item set, take the closure of the item S' -> •S
	let initial_item_set = Closure([{'production': {'lhs': -1, 'rhs': [ToId('S')]}, 'cursor': 0}])
	" let initial_item_set = Closure([{'production': {'lhs': -1, 'rhs': [ToId('S'), eof]}, 'cursor': 0}])
	" echomsg 'Initial item set: ' . string(initial_item_set)
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
		call add(goto, map(range(num_symbols), -1))

		for edge in edges[i]
			if IsNonTerminal(edge.symbol)
				" Goto to that state
				let goto[i][edge.symbol] = edge.to
			else
				" Transition to another State using a Terminal Symbol is a shift to that State
				let actions[i][edge.symbol - a:num_non_terminals] = {'type': 'shift', 'next': edge.to}
			endif
		endfor

		" Do reductions
		for item in state
			" For every final A-item for production P in this state
			if item.cursor != len(item.production.rhs) | continue | endif
			let A = item.production.lhs
			if A != -1
				for t in terminals
					let prev_action = actions[i][t - a:num_non_terminals]

					" Automatically fixe Shift-Reduce Conflicts by not reducing when it would cause a conflict
					if type(prev_action) != v:t_string || prev_action != 'error' | continue | endif

					let actions[i][t - a:num_non_terminals] = {'type': 'reduce', 'lhs': A, 'arity': len(item.production.rhs)}
				endfor
			else
				if item == {'production': {'lhs': -1, 'rhs': [ToId('S')]}, 'cursor': 1}
					let actions[i][eof - a:num_non_terminals] = {'type': 'accept'}
				endif
			endif
		endfor

		let i += 1
	endfor

	echomsg 'Actions'
	echomsg 'State | ' . string(terminals)
	for n in range(len(actions))
		echomsg '' . n . ' | ' . string(actions[n])
	endfor
	echomsg 'Goto'
	echomsg 'State | ' . string(nonterminals) . ' ' . string(terminals)
	for n in range(len(goto))
		echomsg '' . n . ' | ' . string(goto[n])
	endfor

	return {
		\ 'actions': actions, 'goto': goto,
		\ 'num_non_terminals': a:num_non_terminals, 'num_symbols': num_symbols, 'eof': eof,
		\ }
endfunction

function! Parse() abort
	let regexes = [
				\ {'name': 'num', 'regex': '\d\+'},
				\ {'name': '+', 'regex': '+'},
				\ {'name': 'ws', 'regex': '\s\+'},
				\ ]

	" List of productions
	let grammar = [
				\ {'lhs': 'S', 'rhs': ['S', ';', 'A']},
				\ {'lhs': 'S', 'rhs': ['A']},
				\ {'lhs': 'A', 'rhs': ['E']},
				\ {'lhs': 'A', 'rhs': ['i', '=', 'E']},
				\ {'lhs': 'E', 'rhs': ['E', '+', 'i']},
				\ {'lhs': 'E', 'rhs': ['i']},
				\ ]
	echomsg grammar
	" Extract symbols
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
	for production in grammar
		let production.lhs = ToId(production.lhs)
	endfor
	let num_non_terminals = next_id
	for production in grammar
		call map(production.rhs, {k, v -> ToId(v)})
	endfor
	let num_symbols = next_id

	echom grammar
	echomsg 'Number of non-terminals: ' . num_non_terminals

	let parser = s:BuildTables(grammar, num_non_terminals, num_symbols)
	let actions = parser.actions | let goto = parser.goto
	let num_non_terminals = parser.num_non_terminals | let eof = parser.eof

	let lexer = {}
	function lexer.new(input) closure
		let new = copy(self)
		" Input list of symbols
		let new.input = map(str2list(a:input), {k, v -> ToId(nr2char(v))})
		let new.cur = 0
		return new
	endfunction
	function lexer.advance() closure
		let symbol = get(self.input, self.cur, eof)
		let col = self.cur
		let self.cur += 1
		return [symbol, col]
	endfunction

	let lex = lexer.new('i=i+i;i')
	let bos = -1 " Symbol for bottom of stack
	let node = {'symbol': bos, 'state': 0}
	let [t, col] = lex.advance()

	while v:true
		let s = node.state

		let action = actions[s][t - num_non_terminals]

		echomsg 'Doing action: ' . string(action)

		if type(action) == v:t_string && action == 'error'
			" Error
			echomsg 'Error: stack: ' . string(node)
			throw 'Bad input'
		elseif action.type == 'accept'
			" Finished successfully
			echomsg 'Success: stack: ' . string(node)
			break
		elseif action.type == 'shift'
			let node = {'symbol': t, 'state': action.next, 'predecessor': node, 'start': col}
			let [t, col] = lex.advance() " Scan the next input symbol into the lookahead buffer
			let node.end = col
		elseif action.type == 'reduce'
			let L = action.arity
			let new = {'symbol': action.lhs}
			let last_child = {}
			for i in range(L)
				let child = node
				let child.parent = new
				let new.first_child = child
				if last_child != {}
					let child.right_sibling = last_child
				endif
				let last_child = child

				let node = child.predecessor
			endfor
			let new.predecessor = node
			let new.state = goto[node.state][action.lhs]
			let node = new
		endif
	endwhile

	return

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
endfunction

call Parse()