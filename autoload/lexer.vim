let s:bre_lexer = #{offset: 0, has_eof: 0}
let lexer#buffer_regex_lexer = s:bre_lexer

function s:bre_lexer.new(pattern, num_non_terminals, eof, etoken)
	let new = copy(self)
	let new.pattern = a:pattern
	let new.num_non_terminals = a:num_non_terminals
	let new.eof = a:eof
	let new.etoken = a:etoken
	return new
endfunction

" Positions the cursor for lexing the node at the specified offset.
function s:bre_lexer.set_offset(offset)
	let self.offset = a:offset
	let lnum = byte2line(a:offset + 1)
	let col = a:offset + 2 - line2byte(lnum)
	call cursor(lnum, col)
	return [lnum, col]
endfunction

function s:bre_lexer.reset()
	call self.set_offset(0)
	let self.has_eof = 0
endfunction

function s:bre_lexer.advance()
	if self.has_eof | return [self.eof, 0] | endif

	" TODO Position cursor on char before and don't accept match at cursor
	" pos instead
	let [lnum, col, submatch] = searchpos(self.pattern, 'cepWz')
	let byte = line2byte(lnum) - 1 + col
	let prev_lnum = line('.')
	silent execute "normal! 1\<Space>"
	if submatch <= 1 " No match
		if prev_lnum == line('$') | let self.has_eof = 1 | endif
		return [self.etoken, 1]
	endif
	let [bufnum, nlnum, ncol; rest] = getcurpos()
	" If cursor stayed in place it has reached EOF
	if nlnum == lnum && ncol == col | let self.has_eof = 1 | endif
	" If token at end of line: include EOL char
	if nlnum > lnum || ncol == col | let byte += 1 | endif

	let symbol = submatch - 2 + self.num_non_terminals
	let length = byte - self.offset
	let self.offset = byte
	return [symbol, length]
endfunction
