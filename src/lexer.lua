local StringReLexer = {}

local prototype = {
	set_offset = function(self, offset)
		self.offset = offset
	end,
	advance = function(self)
		if self.offset > self.text:len() then return self.lang.eof, 0 end
		for symbol, pattern in pairs(self.patterns) do
			local s, e = self.text:find("^" .. pattern, self.offset)
			if s then
				local len = e - s + 1
				self.offset = self.offset + len
				return symbol, len
			end
		end
		local len = self.text:len() - self.offset + 1
		self.offset = self.text:len() + 1
		return self.lang.etoken, len
	end,
}

function StringReLexer.new(lang, regexes, text)
	local patterns = {}
	for symbol, pattern in pairs(regexes) do
		patterns[lang.symbol_map[symbol]] = pattern
	end

	return setmetatable({
		lang = lang, patterns = patterns, text = text, offset = 1,
	}, {
		__index = prototype,
	})
end

return StringReLexer
