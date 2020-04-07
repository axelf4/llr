rockspec_format = "3.0"
package = "llr"
version = "dev-1"
source = {
	url = "git@github.com:axelf4/llr.git"
}
description = {
	summary = "LR parser",
	detailed = [[LR parser]],
	homepage = "https://github.com/axelf4/llr",
	maintainer = "Axel Forsman",
	license = "MIT"
}
dependencies = {
	"luabitop ~= 1",
	"fun ~= 1",
	"penlight ~= 1",
}
test_dependencies = { "luacov", "luacheck" }