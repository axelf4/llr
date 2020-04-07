local llr = require "llr"
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
		local lang = llr.init_lang(grammar, {["i"] = "%d+", ["+"] = "+"})
		assert.are.same({
			2, 0, 0, 3, 0, 0, 0, 0, 5, 0, 0, 1, 0, 0, 32768, 0,
			0, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0,
			16384, 0, 0, 16384,
		}, lang.table)

		local root = llr.parse(lang, {symbol = lang.etoken, length = 3, modified = true})
		assert.are.equal("E(E(i),+,i)", tree_tostring(lang, root))
	end)
end)
