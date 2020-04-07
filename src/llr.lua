local bit = require "bit"
local tablex = require "pl.tablex"
local fun = require "fun"
local iter = fun.iter

local Set = require "set"
local StringReLexer = require "lexer"

local unpack = rawget(table, "unpack") or unpack
local insert, remove = table.insert, table.remove

local function next_key(table, k)
	k = next(table, k)
	return k, k
end

-- Returns iterator over the keys of the table.
local function keys(table) return fun.wrap(next_key, table) end

local function flatten_gen(param, state)
	local gen_x, param_x = param[1], param[2]
	local i, state_x = state[1], state[2]

	while true do
		local new_state_x, gen_y, param_y, state_y = gen_x(param_x, state_x)
		if new_state_x == nil then return nil end
		local v
		i, v = gen_y(param_y, i or state_y)
		if i then return {i, state_x}, v end
		state_x = new_state_x
	end
end

local function flatten(gen, param, state)
	return fun.wrap(flatten_gen, {gen, param}, {nil, state})
end

-- Parse table constants.
--
-- Parse table representation: table[num_symbols * (state - 1) + symbol] =
--     |18 bits for production| |14 bits for goto state|
--     <-- higher bits                    lower bits -->
--
-- For reduce actions the production index is one-based, while zero for shift
-- actions. Since state zero is never the target of an edge, 0x0 indicates
-- error.
--
-- Accommodates approximately ten times more productions than states.
local error_action, accept_action, goto_mask, prod_mask, prod_shift = 0x0, 0x1, 0x3FFF, bit.bnot(0x3FFF), 14

local function build_table(productions, num_symbols, num_non_terminals, eof)
	local function is_non_terminal(symbol) return symbol <= num_non_terminals end

	-- Returns the closure of the specified item set.
	--
	-- Modifies the set in-situ.
	local function closure(item_set)
		local i = 1
		while i <= #item_set do
			local item = item_set[i]
			-- If item set contains item with cursor just to the left of some nonterminal N
			local N = item.production.rhs[item.cursor]
			if N and is_non_terminal(N) then
				-- Add all initial items for the N-productions of the grammer, recursively
				for _, production in iter(productions):filter(function(prod) return prod.lhs == N end) do
					local new_item = {production = production, cursor = 1}
					Set.insert(item_set, new_item)
				end
			end
			i = i + 1
		end
		return item_set
	end

	-- Returns Goto(I, X) = Closure({A → aX•b | A -> a•Xb in I}).
	local function gotocl(item_set, x)
		return closure(Set.new(iter(item_set):filter(function(i) return i.production.rhs[i.cursor] == x end)
			:map(function(i) return {production = i.production, cursor = i.cursor + 1} end)))
	end

	-- Create the DFA
	-- Augment grammar with a production S' -> S, where S is the start symbol
	-- To generate the first item set, take the closure of the item S' -> •S"
	local S = 1 -- Assume that the start symbol has id 1
	local initial_item_set = closure(Set.new{{production = {lhs = -1, rhs = {S, eof}}, cursor = 1}})
	local states = {{item_set = initial_item_set, edges = {}}}
	local n = 1
	while n <= #states do
		local state = states[n]

		for _, item in ipairs(state.item_set) do
			local x = item.production.rhs[item.cursor] -- Symbol to the right of dot
			if x then
				local goto_set = gotocl(state.item_set, x)
				-- Check if state already exists
				local n_prime
				for i, s in ipairs(states) do
					if tablex.deepcompare(s.item_set, goto_set) then
						n_prime = i
						break
					end
				end
				if not n_prime then
					-- Otherwise add new state
					states[#states + 1] = {item_set = goto_set, edges = {}}
					n_prime = #states
				end
				state.edges[x] = n_prime -- Add an edge X from state n to Goto(I, X) state
			end
		end
		n = n + 1
	end

	-- Compute which nonterminals are nullable (simple O(n^2) algo)
	local nullable = {} -- Dictionary of nonterminals that may produce epsilon
	repeat
		local finished = true
		for _, production in ipairs(productions) do
			if not nullable[production.lhs] then
				local is_nullable = iter(production.rhs):all(function(X) return nullable[X] end)
				if is_nullable then
					nullable[production.lhs] = true
					finished = false
				end
			end
		end
	until finished

	-- Build the LALR(1) lookahead sets from the LR(0) automata, based on:
	-- DeRemer, F. L., and T. J. Pennelo: "Efficient Computation of LALR(1)
	-- Lookahead Sets", ACM Transactions on Programming Languages and Systems,
	-- Vol. 4, No. 4, Oct. 1982, pp. 615-649"

	-- The set of nonterminal transitions of the LR(0) parser
	local X = flatten(iter(states):enumerate():map(function(i, state)
		return keys(state.edges):filter(is_non_terminal):map(function(transition_symbol)
			return {state = i, symbol = transition_symbol}
		end)
	end)):totable()

	-- Returns direct read symbols as keys of table.
	local function DR(p, A) return states[states[p].edges[A]].edges end

	-- (p, A) READS (r, C) iff p --A-> r --C-> and C =>* eps
	local reads = iter(X):map(function(trans)
		local r = states[trans.state].edges[trans.symbol]
		return keys(states[r].edges):filter(function(C) return nullable[C] end)
			:map(function(C) return {state = r, symbol = C} end):totable()
	end):totable()

	-- (p, A) INCLUDES (p', B) iff B -> L A T,  T =>* eps, and p' --L-> p
	local includes = iter(X):map(function() return {} end):totable()
	-- (q, A -> w) LOOKBACK (p, A) iff p --w-> q
	local lookback = {}
	for i, transition in ipairs(X) do
		local state, B = states[transition.state], transition.symbol

		for _, item in iter(state.item_set):filter(function(item)
			-- Consider only start B-items
			return item.production.lhs == B and item.cursor == 1
		end) do
			-- Run the state machine forward
			local j = transition.state
			for cursor = item.cursor, #item.production.rhs do
				local t = item.production.rhs[cursor]
				if cursor > 1 then
					-- If this (symbol, state) is a nonterminal transition
					local trans = Set.find(X, {state = j, symbol = t})
					if trans then
						local remaining_nullable = iter(item.production.rhs):drop_n(cursor)
							:all(function(v) return nullable[v] end)
						if remaining_nullable then
							table.insert(includes[trans], i)
						end
					end
				end
				j = states[j].edges[t]
			end
			-- At this point j is the final state
			lookback[#lookback + 1] = {q = j, production = item.production, transition = i}
		end
	end

	local function digraph(R, FP)
		local stack = {}
		-- Function from X to initially empty sets
		local F = iter(X):map(function() return {} end):totable()
		local N = tablex.new(#X, 0)

		local function traverse(i, x)
			table.insert(stack, i)
			local d = #stack
			N[i] = d
			F[i] = FP(x.state, x.symbol)

			for _, j in ipairs(R[i]) do
				if N[j] == 0 then traverse(j, X[j]) end
				if N[j] < N[i] then N[i] = N[j] end
				for _, f in ipairs(F[j]) do table.insert(F[i], f) end
			end

			if N[i] == d then
				repeat
					N[stack[#stack]] = math.huge
					F[stack[#stack]] = F[i]
				until table.remove(stack) == i
			end
		end

		for i, x in ipairs(X) do if N[i] == 0 then traverse(i, x) end end
		return F
	end

	local Read = digraph(reads, DR)
	local function ReadFunc(p, A) return Read[Set.find(X, {state = p, symbol = A})] end
	local Follow = digraph(includes, ReadFunc)

	-- LA(q, A -> w) = U{Follow(p, A) | (q, A -> w) lookback (p, A)}
	local function LA(q, production)
		return flatten(iter(lookback):filter(function(lb) return lb.q == q and lb.production == production end)
			:map(function(lb) return keys(Follow[lb.transition]) end))
	end

	-- Build parse table
	local table = {}
	for i = 1, #states * num_symbols do table[i] = error_action end -- Fill with error
	for i, state in ipairs(states) do
		for symbol, to in pairs(state.edges) do
			table[num_symbols * (i - 1) + symbol] = to -- Goto to that state
		end

		-- Given a final A-item for production P (A != S') fill corresponding
		-- row with reduce action for P
		for _, item in ipairs(state.item_set) do
			local A = item.production.lhs
			if item.cursor == #item.production.rhs + 1 and A ~= -1 then
				for _, s in LA(i, item.production) do
				-- for s in pairs(LA(i, item.production)) do
					local prev_action = table[num_symbols * (i - 1) + s]
					-- Check for ambiguous grammar
					if prev_action ~= nil and prev_action > 0 then error("Shift/reduce or reduce/reduce conflict") end
					table[num_symbols * (i - 1) + s] = bit.lshift(tablex.find(productions, item.production), prod_shift) -- TODO
				end
			end
		end

		-- For every item set containing S' → w•eof, set accept in eof column
		local has_accept = iter(state.item_set):any(function(item)
			return item.production.lhs == -1 and item.production.rhs[item.cursor] == eof
		end)
		if has_accept then table[num_symbols * (i - 1) + eof] = accept_action end
	end
	return table
end

-- Incrementally re-parses the current buffer given the previous tree.
--
-- Based on:
-- - Wagner, Tim A., and Susan L. Graham. "Efficient and Flexible Incremental
-- Parsing." ACM Transactions on Programming Languages and Systems 20.2 (1998).
local function parse(lang, root)
	local table, productions = lang.table, lang.productions
	local num_symbols, num_non_terminals = lang.num_symbols, lang.num_non_terminals
	local eof, error_sym, etoken = lang.eof, lang.error_sym, lang.etoken

	local function is_terminal(symbol) return symbol > num_non_terminals end

	local la, state = root, 1 -- Set lookahead to root of tree
	local eos = {symbol = lang.eof, length = 0}
	-- Initialize the parse stack to contain only bos
	local stack = setmetatable({}, {
		__index = {
			push = function(self, node) insert(self, {node, state}) end,
			pop = function(self)
				local node
				node, state = unpack(remove(self))
				return node, state
			end,
			top = function(self) return unpack(self[#self] or {eos, 1}) end,
		}
	})
	local verifying = 0

	local lex = lang.lexer
	local offset = 1 -- Byte offset of la

	-- Pop right stack by traversing previous tree structure.
	local function pop_lookahead(node)
		while not node.right_sibling do
			if not node.parent then return eos end
			node = node.parent
		end
		return node.right_sibling
	end
	-- Decompose a nonterminal lookahead.
	local function left_breakdown(node) return node.first_child or pop_lookahead(node) end

	-- Shift a node onto the parse stack and update the current parse state.
	local function shift(node)
		stack:push(node)
		state = bit.band(table[num_symbols * (state - 1) + node.symbol], goto_mask)
	end

	-- Remove any subtrees on top of parse stack with null yield, then break
	-- down right edge of topmost subtree.
	local function right_breakdown()
		local node
		repeat -- Replace top of stack with its children
			node = stack:pop()
			-- Does nothing when node is a terminal symbol
			local child = node.first_child
			while child do shift(child); child = child.right_sibling end
		until is_terminal(node.symbol)
		shift(node) -- Leave final terminal symbol on top of stack
	end

	local function is_transparent(symbol) return symbol == error_sym or symbol == etoken end

	local function reduce(production)
		local L = #production.rhs
		local parent = {symbol = production.lhs, length = 0} -- TODO Reuse parent
		local child, last_child
		while L > 0 or is_transparent(stack:top().symbol) do
			child = stack:pop()
			if not is_transparent(child.symbol) then L = L - 1 end
			child.parent = parent
			parent.length = parent.length + child.length
			if last_child then
				child.right_sibling = last_child
			else
				child.right_sibling = nil
				if child.parent.right_sibling then
					parent.parent = child.parent.right_sibling
				elseif child.parent then
					parent.parent = child.parent.parent
				end
			end
			last_child = child
		end
		parent.first_child = child
		parent.modified = false

		stack:push(parent)
		state = bit.band(table[num_symbols * (state - 1) + production.lhs], goto_mask)
	end

	-- Relex a continuous region of modified nodes.
	local function relex()
		lex:set_offset(offset)
		local node = la
		local diff = 0 -- Cursor offset to start of the current lookahead
		local need_new_node = false
		local prev

		repeat
			local symbol, length = lex:advance()
			diff = diff + length

			while true do
				if not need_new_node then
					if symbol == node.symbol or diff < node.length or node.symbol == eof then
						break
					end
					diff = diff - node.length
				end

				-- Drop overrun node by moving to the next terminal
				node = pop_lookahead(node)
				while not is_terminal(node.symbol) do node = left_breakdown(node) end
				need_new_node = false
			end

			local new_node
			if symbol == eof then
				new_node = eos
			elseif symbol == node.symbol then -- If node reuse is possible
				diff = diff - node.length
				node.length = length
				node.modifed = false
				need_new_node = true
				new_node = node
			else
				new_node = {symbol = symbol, length = length, right_sibling = node, parent = node.parent}
			end
			if prev then prev.right_sibling = new_node else la = new_node end

			prev = new_node
		until diff == 0 -- If synced up, break
	end

	-- Simple panic mode error recovery.
	--
	-- Returns a truthy value if should accept.
	local function recover()
		for i = #stack, 1, -1 do
			local stack_state, stack_node = unpack(stack[i])
			if not is_transparent(stack_node.symbol) then
				local action = table[num_symbols * (stack_state - 1) + la.symbol]
				if action then
					-- Pop stack nodes until can continue and wrap them in an error node
					local error_node = {symbol = error_sym, length = 0}
					local last_child
					for _ = i, #stack do
						local node = stack:pop()
						error_node.length = error_node.length + node.length
						error_node.first_child = node
						node.right_sibling = last_child
						last_child = node
					end
					stack:push(error_node)
					return
				end
			end
		end

		if la.symbol == eof then -- Wrap everything in an error node
			local error_node = {symbol = error_sym, length = 0}
			local last_child, child
			while #stack > 0 do
				child = stack:pop()
				child.parent = error_node
				error_node.length = error_node.length + child.length
				child.right_sibling = last_child
				last_child = child
			end
			if child then error_node.first_child = child end
			stack:push(error_node)
			return true
		end

		-- Wrap lookahead in error node
		local error_node = {symbol = error_sym, length = la.length, first_child = la}
		la = pop_lookahead(la)
		error_node.first_child.parent = error_node
		error_node.first_child.right_sibling = nil
		stack:push(error_node)
	end

	while true do
		if la.modified then
			if is_terminal(la.symbol) then relex()
			else la = left_breakdown(la) end -- Split at changed point
		else
			local action = table[num_symbols * (state - 1) + la.symbol]
			if action == error_action then -- Error action
				if is_terminal(la.symbol) then
					if verifying then
						right_breakdown() -- Delayed breakdown
						verifying = false
					else recover() end -- Actual parse error
				else la = left_breakdown(la) end
			elseif action == accept_action then -- Accept action
				if #stack == 1 or recover() then break end
			elseif bit.band(action, prod_mask) == 0 then -- Shift action
				verifying = not is_terminal(la.symbol)
				shift(la)
				offset = offset + la.length
				la = pop_lookahead(la)
			else -- Reduce action
				reduce(productions[bit.rshift(action, prod_shift)])
			end
		end
	end

	return (stack:pop())
end

--- Adjust the byte lengths of the specified node given an edit.
-- Should be done before re-parsing. The edit must be entirely contained inside
-- node. edit may be modified in-place.
local function adjust_len(node, edit)
	node.modified = true
	-- Enlarge according to edit length difference
	node.length = node.length + edit.new_end - edit.old_end

	-- Edit child ranges
	local child = node.first_child
	while child do
		if edit.start <= node.length then
			adjust_len(child, {
				start = edit.start,
				old_end = math.max(edit.old_end, child.length),
				new_end = edit.new_end, -- TODO
			})
			edit.new_end = 0 -- Distribute all new len to first child
		else
			edit.new_end = edit.new_end - child.length
		end
		edit.old_end = edit.old_end - child.length
		if edit.old_end <= 0 then break end
		edit.start = edit.start - child.length
		child = child.right_sibling
	end
end

local function extract_symbols(grammar)
	local extracted_symbols = {}
	local next_id = 1
	local function to_id(x)
		local id = extracted_symbols[x]
		if not id then
			id = next_id
			extracted_symbols[x] = id
			next_id = next_id + 1
		end
		return id
	end
	for _, production in pairs(grammar) do
		production.lhs = to_id(production.lhs)
	end
	local error_sym = next_id; next_id = next_id + 1
	local num_non_terminals = next_id - 1
	for _, production in pairs(grammar) do
		production.rhs = iter(production.rhs):map(to_id):totable()
	end
	local etoken, eof, num_symbols = next_id, next_id + 1, next_id + 1
	extracted_symbols["␄"] = eof
	return grammar, extracted_symbols, num_non_terminals, num_symbols, eof, error_sym, etoken
end

local function reverse_table(table)
	local result = {}
	for k, v in pairs(table) do result[v] = k end
	return result
end

local function init_lang(grammar, regexes)
	local productions, symbol_map, num_non_terminals, num_symbols, eof, error_sym, etoken = extract_symbols(grammar)

	local symbol_names = reverse_table(symbol_map)

	local table = build_table(productions, num_symbols, num_non_terminals, eof)

	local patterns = {}
	for symbol, pattern in pairs(regexes) do
		patterns[symbol_map[symbol] - num_non_terminals] = pattern
	end
	local lexer = StringReLexer.new(patterns, num_non_terminals, eof, etoken)

	return {
		table = table, productions = productions,
		num_symbols = num_symbols, num_non_terminals = num_non_terminals,
		eof = eof, error_sym = error_sym, etoken = etoken,
		lexer = lexer,
		symbol_names = symbol_names,
	}
end

return {
	build_table = build_table,
	parse = parse,
	init_lang = init_lang,
}
