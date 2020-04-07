local tablex = require "pl.tablex"
local iter = require "fun".iter

local Set = {}

function Set.new(init)
	local set = setmetatable({}, {
		__index = function(table, value)
			for _, v in ipairs(table) do
				if tablex.deepcompare(v, value) then return true end
			end
			return false
		end,
	})
	if init then
		for _, v in iter(init) do Set.insert(set, v) end
	end
	return set
end

function Set.insert(set, value)
	if set[value] then return end -- Uses metamethod __index
	table.insert(set, value)
end

function Set.find(set, value)
	for i, v in ipairs(set) do
		if tablex.deepcompare(v, value) then return i end
	end
	return nil
end

return Set
