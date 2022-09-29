" Syntax highlighting di base per spinnaker (file .spk)

if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword spinnakerTopDef mod data def and ext rel inst
syn keyword spinnakerModKeyword use pub
syn keyword spinnakerKeyword let put forall
syn keyword spinnakerConditional if then else
syn match spinnakerOperator "\v[:!$%&\*\+/\-<=>\?@\\^|~.]+"
syn match spinnakerNumber "\v[0-9][0-9_]*"
syn match spinnakerFloat "\v[0-9][0-9_]*\.[0-9_]+"
syn keyword spinnakerTodo TODO FIXME NOTE contained
syn match spinnakerLineComment "#.*$" contains=mylangTodo
syn match spinnakerIdentifier "[_a-z][a-zA-Z0-9_']*"
syn match spinnakerChar "'[^'\\]'\|'\\.'\|'\\u[0-9a-fA-F]\{4}'"
syn region spinnakerString start=+"+ skip=+\\\\\|\\"+ end=+"+
  \ contains=@Spell
syn match spinnakerType "[A-Z][a-zA-Z0-9_']*"
syn region spinnakerParens matchgroup=mylangDelimiter start="(" end=")" contains=TOP,@Spell
syn region spinnakerBrackets matchgroup=mylangDelimiter start="\[" end="]" contains=TOP,@Spell
syn region spinnakerBlock matchgroup=mylangDelimiter start="{" end="}" contains=TOP,@Spell
syn match spinnakerSeparator  "[,;]"

highlight def link spinnakerIdentifier Normal
highlight def link spinnakerType Type
highlight def link spinnakerTopDef Define
highlight def link spinnakerModKeyword Include
highlight def link spinnakerKeyword Keyword
highlight def link spinnakerConditional Conditional
highlight def link spinnakerNumber Number
highlight def link spinnakerFloat Float
highlight def link spinnakerOperator Operator
highlight def link spinnakerTodo Todo
highlight def link spinnakerLineComment Comment
highlight def link spinnakerChar String
highlight def link spinnakerString String
highlight def link spinnakerDelimiter Delimiter
highlight def link spinnakerSeparator Delimiter

let b:current_syntax = "spinnaker"
" in A.B.c A e B devono essere blu (Include)
" highlight per |, ->, \
