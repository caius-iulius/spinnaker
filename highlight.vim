"TODO: Questo va eliminato, serve solo fino a quando non c'è un ftdetect
set filetype=

if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword mylangTopDef mod data def and rel inst
syn keyword mylangTopKeyword use
syn keyword mylangTopAccess pub
syn keyword mylangKeyword let put forall
syn keyword mylangConditional if then else
syn match mylangOperator "\v[:!$%&\*\+/\-<=>\?@\\^|~.]+"
" syn match haskellChar "\<'[^'\\]'\|'\\.'\|'\\u[0-9a-fA-F]\{4}'\>"
"FIXME: cosa significano esattamente \< e \> ? li posso usare in very magic mode?
syn match mylangType "\<[A-Z][a-zA-Z0-9_']*\>"
syn match mylangIdentifier "\<[_a-z][a-zA-Z0-9_']*\>"
syn match mylangNumber "\v[0-9][0-9_]*"
syn match mylangFloat "\v[0-9][0-9_]*\.[0-9_]+"
syn keyword mylangTodo TODO FIXME NOTE contained
syn match mylangLineComment "#.*$" contains=mylangTodo
syn region mylangChar start=+'+ skip=+\\\\\|\\'+ end=+'+
  \ contains=@Spell
syn region mylangString start=+"+ skip=+\\\\\|\\"+ end=+"+
  \ contains=@Spell
syn region mylangParens matchgroup=mylangDelimiter start="(" end=")" contains=TOP,@Spell
syn region mylangBrackets matchgroup=mylangDelimiter start="\[" end="]" contains=TOP,@Spell
syn region mylangBlock matchgroup=mylangDelimiter start="{" end="}" contains=TOP,@Spell
syn match mylangSeparator  "[,;]"

highlight def link mylangIdentifier Normal
highlight def link mylangType Type
highlight def link mylangTopDef Define
highlight def link mylangTopKeyword Keyword
highlight def link mylangTopAccess Keyword
highlight def link mylangKeyword Keyword
highlight def link mylangConditional Conditional
highlight def link mylangNumber Number
highlight def link mylangFloat Float
highlight def link mylangOperator Operator
highlight def link mylangTodo Todo
highlight def link mylangLineComment Comment
highlight def link mylangChar Character
highlight def link mylangString String
highlight def link mylangDelimiter Delimiter
highlight def link mylangSeparator Delimiter

" syn keyword mylangForall forall
" in A.B.c A e B devono essere blu (Include)
" highlight per |, ->, \
