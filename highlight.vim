syn keyword NoteTodo NOTE TODO
syn keyword KeywordUse use

syn keyword KeywordDef mod data def and
syn keyword KeywordLet put let
syn keyword KeywordAccess pub

syn region HCommentLine start="#" end="$" contains=NoteTodo

hi def link NoteTodo Todo
hi def link KeywordUse Keyword
hi def link KeywordDef Define
hi def link KeywordLet Statement
hi def link KeywordAccess Keyword
" pub mi piacerebbe blu
" in A.B.c A e B devono essere blu (Include)
" highlight per |, ->, \, {, }, .

hi def link HCommentLine Comment
