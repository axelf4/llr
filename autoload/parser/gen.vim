" Converts string names for symbols in the grammar to numerical ids.
"
" Modifies the arguments in place.
function s:ExtractSymbols(grammar) abort
	let extracted_symbols = {}
	let next_id = 0
	function ToId(x) abort closure
		let id = extracted_symbols->get(a:x, -1)
		if id == -1
			let id = next_id
			let extracted_symbols[a:x] = id
			let next_id += 1
		endif
		return id
	endfunction
	for production in a:grammar
		let production.lhs = ToId(production.lhs)
	endfor
	let error_sym = next_id | let next_id += 1
	let num_non_terminals = next_id
	for production in a:grammar
		call map(production.rhs, {_, v -> ToId(v)})
	endfor

	let etoken = next_id | let eof = next_id + 1 | let num_symbols = next_id + 2
	return [a:grammar, extracted_symbols, num_non_terminals, num_symbols, eof, error_sym, etoken]
endfunction

function s:ReverseDict(dict) abort
	let result = {}
	for [k, v] in items(a:dict)
		let result[v] = k
	endfor
	return result
endfunction

" Constructs a language object from the specified grammar/regexes.
"
" The returned values `error_sym` and `etoken` are the nonterminal and
" terminal error symbols, respectively.
function parser#gen#InitLanguage(grammar, regexes) abort
	let [productions, symbol_map, num_non_terminals, num_symbols, eof, error_sym, etoken] = s:ExtractSymbols(a:grammar)
	let num_terminals = num_symbols - num_non_terminals
	let symbol_to_name = s:ReverseDict(symbol_map)
	let symbol_to_name[eof] = '$'
	let symbol_to_name[etoken] = "LEXERR"
	let symbol_to_name[error_sym] = 'ERR'

	let table = parser#BuildTable(productions, num_non_terminals, num_symbols, eof)

	" Build lexer regex pattern
	if len(a:regexes) isnot num_terminals - 2 | throw 'Bad number of terminal regexes' | endif
	let pattern = '\%#\(' .. a:regexes->items()->sort({a, b -> symbol_map[a[0]] - symbol_map[b[0]]})
				\ ->map({_, v -> v[1]})->join('\)\|\(') .. '\)\|\(.\+\)'
	let lexer = g:lexer#buffer_regex_lexer.new(pattern, num_non_terminals, eof, etoken)

	return #{
				\ table: table, productions: productions, lexer: lexer,
				\ num_symbols: num_symbols, num_non_terminals: num_non_terminals,
				\ eof: eof, error_sym: error_sym, etoken: etoken,
				\ symbol_to_name: symbol_to_name,
				\ }
endfunction
