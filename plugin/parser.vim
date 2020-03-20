" Only load the plugin once
if exists('g:loaded_parser') | finish | endif
let g:loaded_parser = 1

" Adjust the byte lengths of the specified node given an edit.
"
" Should be done before re-parsing. The edit must be entirely contained inside
" node. {edit} may be modified in-place.
function s:EditRanges(node, edit) abort
	let stack = [a:node, a:edit]

	while !empty(stack)
		let [node, edit] = stack->remove(-2, -1)
		let node.modified = 1
		" Enlarge according to edit length difference
		let node.length += edit.new_end - edit.old_end

		" Edit child ranges
		if node->has_key('first_child')
			let child = node.first_child
			while 1
				if edit.start <= child.length
					let child_edit = copy(edit)
					if child_edit.old_end > child.length | let child_edit.old_end = child.length | endif
					call add(stack, child) | call add(stack, child_edit)

					let edit.new_end = 0 " Distribute all new len to first child
				else
					let edit.new_end -= child.length
				endif

				let edit.old_end -= child.length
				if edit.old_end <= 0 | break | endif
				let edit.start -= child.length
				if edit.start < 0 | let edit.start = 0 | endif

				if !has_key(child, 'right_sibling') | break | endif
				let child = child.right_sibling
			endwhile
		endif
	endwhile
endfunction

function s:Listener(bufnr, start, end, added, changes) abort
	if !exists('b:node') | return | endif

	for change in a:changes
		" Inclusive start, exclusive end, all byte counts
		let old_len = b:node.length
		let new_len = line2byte(line('$') + 1) - 1
		let new_end = line2byte(change.end + change.added) - 1
		let edit = #{
					\ start: line2byte(change.lnum) - 1,
					\ new_end: new_end,
					\ old_end: new_end + (old_len - new_len),
					\ }
		call s:EditRanges(b:node, edit) " Adjust node ranges
	endfor

	let b:node = parser#Parse(b:lang, b:node) " Re-parse buffer
endfunction

let g:InitialNode = {lang -> #{symbol: lang.etoken, length: line2byte(line('$') + 1) - 1, modified: 1}}
