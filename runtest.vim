let s:test_file = expand('%')
source %
bwipeout!

" Query list of functions matching ^Test_
let s:tests = execute('function /^Test_')->split("\n")->map('matchstr(v:val, ''function \zs\k\+\ze()'')')

for s:test_function in s:tests
	echo 'Test' s:test_function
	try
		execute 'call' s:test_function '()'
	catch
		eval v:errors->add("Uncaught exception: " .. v:exception .. " at " .. v:throwpoint)
	endtry

	if !empty(v:errors)
		echo s:test_file .. ':1:Error'
		for s:error in v:errors
			echo s:error
		endfor
		cquit!
	endif
endfor

quit!
