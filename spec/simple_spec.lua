local llr = require "llr"
local StringReLexer = require "lexer"
local dump = require "pl.pretty".dump

local function tree_tostring(lang, node)
	return lang.symbol_names[node.symbol]
	.. (node.first_child and "(" .. tree_tostring(lang, node.first_child) .. ")" or "")
	.. (node.right_sibling and "," .. tree_tostring(lang, node.right_sibling) or "")
end

describe("Parser", function()
	it("should work", function()
		local grammar = {
			{lhs = "E", rhs = {"E", "+", "i"}},
			{lhs = "E", rhs = {"i"}},
		}
		local lang = llr.init_lang(grammar)
		assert.are.same({
			2, 0, 0, 3, 0, 0, 0, 0, 5, 0, 0, 1, 0, 0, 32768, 0,
			0, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0,
			16384, 0, 0, 16384,
		}, lang.table)

		local lexer = StringReLexer.new(lang, {["i"] = "%d+", ["+"] = "+"}, "1+2")
		local root = llr.parse(lang, {symbol = lang.etoken, length = 3, modified = true}, lexer)
		assert.are.equal("E(E(i),+,i)", tree_tostring(lang, root))
	end)
end)
