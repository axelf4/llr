local StringReLexer = {}

local prototype = {
	set_offset = function(self, offset)
		self.offset = offset
	end,
	advance = function(self)
		if self.offset > self.text:len() then return self.eof, 0 end
		for i, regex in ipairs(self.regexes) do
			local s, e = self.text:find("^" .. regex, self.offset)
			if s then
				local symbol = i + self.num_non_terminals
				local len = e - s + 1
				self.offset = self.offset + len
				return symbol, len
			end
		end
		local len = self.text:len() - self.offset + 1
		self.offset = self.text:len() + 1
		return self.etoken, len
	end,
}

function StringReLexer.new(regexes, num_non_terminals, eof, etoken)
	return setmetatable({
		regexes = regexes, num_non_terminals = num_non_terminals,
		eof = eof, etoken = etoken,
		offset = 1,
		text = "1+2",
	}, {
		__index = prototype,
	})
end

return StringReLexer
