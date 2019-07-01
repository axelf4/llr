" Incremental parser generator that compiles to VimL at runtime for
" indentation, syntax highlighting, etc.
"
" Then use `listener_add()`
"
" Have to have great error recovery...
"
" See:
" * https://pages.github-dev.cs.illinois.edu/cs421-haskell/web-su19/files/handouts/lr-parsing-tables.pdf
" * https://dl.acm.org.sci-hub.tw/citation.cfm?id=357066

" Action bit masks. super non optimal
" TODO add accept/done
let [shift, reduce, error] = [0x8000, 0x4000, 0x2000] | lockvar shift reduce error

function! Parse() abort
	" List of productions
	let grammar = [
				\ {'lhs': 'S', 'rhs': ['X']},
				\ {'lhs': 'X', 'rhs': ['(', 'X', ')']},
				\ {'lhs': 'X', 'rhs': ['(', ')']},
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
	let eof = next_id | let next_id += 1

	let [nonterminals, terminals] = [range(num_non_terminals), range(num_non_terminals, next_id - 1)]

	echom grammar
	echomsg 'Number of non-terminals: ' . num_non_terminals

	function! IsNonTerminal(symbol) abort closure
		call assert_true(type(a:symbol) == v:t_number
					\ && a:symbol >= 0 && a:symbol < next_id, 'Invalid symbol')
		return a:symbol < num_non_terminals " Non-terminal symbols are given the smaller id:s
	endfunction

	let item = {}
	function! item.new(production, cursor) dict
		let new = copy(self)
		let new.production = a:production
		let new.cursor = a:cursor
		return new
	endfunction

	" Returns the closure of the specified item set
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
				for N_production in filter(copy(grammar), {k, v -> v.lhs == N})
					let new_item = {'production': N_production, 'cursor': 0}
					" Only add if unique
					if index(a:item_set, new_item) == -1 | call add(a:item_set, new_item) | endif
				endfor
			endif
			let i += 1
		endwhile
		return a:item_set
	endfunction

	" FOLLOW sets are only defined for single nonterminals. The definition is
	" as follows: For a nonterminal A, FOLLOW(A) is the set of terminals that
	" can appear immediately to the right of A in some partial derivation;
	" i.e., terminal t is in FOLLOW(A) if:
	"     S → ... A t ..., where t is a terminal
	" Furthermore, if A can be the rightmost symbol in a derivation, then EOF
	" is in FOLLOW(A).
	function! FollowSet(A) abort closure
		call assert_true(IsNonTerminal(A))
		let result = []
		for production in grammar
			let start = 0
			while v:true
				let idx = index(production.rhs, a:A, start)
				if idx == -1 | break | endif
				let t = get(production.rhs, idx + 1, eof)
				if !IsNonTerminal(t) | call add(result, t) | endif
				let start = idx + 1
			endwhile
		endfor
		return result
	endfunction

	" Returns Kernel(IS, X) = {A -> aX•b | A -> a•Xb in IS}
	"
	" Modifies the specified list in-situ.
	let Kernel = {item_set, x -> map(filter(item_set, {k, v -> get(v.production.rhs, v.cursor, -1) == x}),
				\ {k, v -> extend(v, {'cursor': v.cursor + 1})})}

	" Create DFA

	" Augment grammar with a production S' -> S, where S is the start symbol
	" To generate the first item set, take the closure of the item S' -> *S
	let initial_item_set = filter(Closure([{'production': {'lhs': -1, 'rhs': [ToId('S')]}, 'cursor': 0}]),
				\ {k, v -> v.production.lhs != -1})
	" let initial_item_set = Closure([{'production': {'lhs': -1, 'rhs': [ToId('S')]}, 'cursor': 0}])
	echomsg 'Initial item set: ' . string(initial_item_set)
	let states = [initial_item_set] " Map from state index to associated closure
	let edges = []
	let n = 0
	while n < len(states)
		let state = states[n]
		call add(edges, [])
		for item in state
			let x = get(item.production.rhs, item.cursor, -1)
			if x != -1
				let goto = Closure(Kernel(deepcopy(state), x))
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
		call add(goto, map(range(next_id), 0))

		for edge in edges[i]
			echom edge
			if IsNonTerminal(edge.symbol)
				" Goto to that state
				let goto[i][edge.symbol] = edge.to
			else
				" Transition to another State using a Terminal Symbol is a shift to that State
				let actions[i][edge.symbol - num_non_terminals] = {'type': 'shift', 'next': edge.to}
			endif
		endfor

		" TODO Do reductions
		for item in state
			" For every final A-item for production P in this state
			if item.cursor != len(item.production.rhs) | continue | endif
			let A = item.production.lhs
			" echomsg 'Reduction item: ' . string(item) . ', i is ' . i . ' and A is ' . A . ' FollowSet: ' . string(FollowSet(A)) . ' eof: ' . eof
			for t in FollowSet(A)
				if actions[i][t - num_non_terminals] == 'shift' | throw 'Ambiguous grammar' | endif
				let actions[i][t - num_non_terminals] = {'type': 'reduce', 'lhs': A, 'arity': len(item.production.rhs)}
			endfor

			if A == 0
				let actions[i][eof - num_non_terminals] = {'type': 'done'}
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

	let input = map(str2list('((()))'), {k, v -> ToId(nr2char(v))}) " Input list of symbols
	let cur = 0

	let stack = []
	while v:true
		let s = get(stack, -1, 0)
		let t = get(input, cur, eof)

		call assert_false(IsNonTerminal(t))

		let action = actions[s][t - num_non_terminals]
		echomsg 'Doing action: ' . string(action)

		if type(action) == v:t_string && action == 'error'
			" Error
			echomsg 'Error: stack: ' . string(stack)
			throw 'Bad input'
		elseif action.type == 'done'
			if t == eof && len(stack) == 1
				" Finished successfully
				echomsg 'Success'
				break
			endif
		elseif action.type == 'shift'
			" call add(stack, t) " Shift the matched terminal t onto the parse stack
			let cur += 1 " Scan the next input symbol into the lookahead buffer
			call add(stack, action.next) " Push next state n onto the parse stack as the new current state
		elseif action.type == 'reduce'
			let L = action.arity
			call remove(stack, -L, -1) " Remove the matched topmost L symbols from the parse stack
			" let p = stack[-1]
			let p = get(stack, -1, 0)
			echomsg 'p is ' . p . ' and lhs is ' . action.lhs
			let n = goto[p][action.lhs]
			call add(stack, n)
		endif
	endwhile
endfunction

call Parse()
