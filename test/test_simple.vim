let s:TreeString = {node, lang -> lang.symbol_to_name[node.symbol]
				\ .. (node->has_key('first_child') ? '(' .. s:TreeString(node.first_child, lang) .. ')' : '')
				\ .. (node->has_key('right_sibling') ? ',' .. s:TreeString(node.right_sibling, lang) : '')}

function Test_Simple() abort
	" List of productions
	let s:grammar = [{'lhs': 'E', 'rhs': ['E', '+', 'i']},
				\ {'lhs': 'E', 'rhs': ['i']}]
	let s:regexes = {'+': '+', 'i': '\d\+'}
	let lang = parser#gen#InitLanguage(s:grammar, s:regexes)

	call setline(1, ['1+2'])
	let node = parser#Parse(lang, g:InitialNode(lang))
	call assert_equal('E(E(i),+,i)', node->s:TreeString(lang))
endfunction
