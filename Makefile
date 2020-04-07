all: check lint

check: ; luarocks test

lint: ; luacheck llr-dev-1.rockspec

.PHONY: all check
