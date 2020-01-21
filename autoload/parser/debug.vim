function parser#debug#PrintTree(node, depth) abort
	echom repeat(' ', 4 * a:depth) .. g:lang.symbol_to_name[a:node.symbol] .. a:node.length
	if a:node->has_key('first_child')
		call PrintTree(a:node.first_child, a:depth + 1)
	endif
	if a:node->has_key('right_sibling')
		call PrintTree(a:node.right_sibling, a:depth)
	endif
endfunction

function parser#debug#GetSyntaxNode(lnum, col) abort
	let byte = line2byte(a:lnum) - 1 + a:col
	let node = b:node
	let stack = [node]
	let offset = 0

	while node->has_key('first_child')
		" Output debug information
		echomsg 'Top level: -------'
		let child = node
		while 1
			echomsg 'Child: ' .. g:lang.symbol_to_name[child.symbol] .. ' len: ' .. child.length
			if !has_key(child, 'right_sibling') | break | endif
			let child = child.right_sibling
		endwhile

		let node = node.first_child
		while offset + node.length < byte
			let offset += node.length
			let node = node.right_sibling
		endwhile
		call add(stack, node)
	endwhile

	" return stack
	return string(map(stack, {_, v -> g:lang.symbol_to_name[v.symbol]})) .. ', modified: ' .. node->get('modified', 0) .. ', length: ' .. node.length
endfunction

function parser#debug#GetSyntaxNodeUnderCursor() abort
	return parser#debug#GetSyntaxNode(line('.'), col('.'))
endfunction
