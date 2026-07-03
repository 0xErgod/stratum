; Syntax highlighting for the ρ-calculus surface syntax.

; The null process `0` / `nil`.
(nil) @constant.builtin

; Declaration keywords.
[
  "def"
  "new"
] @keyword

; Definition and macro names.
(def name: (identifier) @function)
(call macro: (identifier) @function.call)

; Names.
(identifier) @variable
(input bind: (identifier) @variable.parameter)
(parameters param: (identifier) @variable.parameter)
(new name: (identifier) @variable.parameter)
(named_argument param: (identifier) @variable.parameter)

; Operators.
"@" @operator
"*" @operator
"!" @operator
"|" @operator
"<-" @operator
"." @punctuation.delimiter

; Brackets.
[
  "("
  ")"
  "{"
  "}"
] @punctuation.bracket

; Separators.
"," @punctuation.delimiter

; Comments.
(comment) @comment
