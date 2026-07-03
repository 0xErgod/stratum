; Local-variable scoping for bound names.
;
; Each input `x(y).P` opens a scope; its binder `y` is a definition, and every
; bare identifier is a reference resolved against the innermost enclosing
; definition of the same text (inner binders shadow outer ones).
;
; This is an editor-only *approximation* of the runtime parser's scoping: the
; whole `input` node is the scope, so the binder is treated as visible over the
; channel position too, whereas the runtime resolves an input's channel in the
; enclosing scope (before pushing the binder). The authoritative scoping is the
; recursive-descent parser; these queries exist for highlighting only.

(input) @local.scope

(input bind: (identifier) @local.definition)

; A `def` body is a scope; its parameters and local `new` names are definitions.
(def_body) @local.scope

(parameters param: (identifier) @local.definition)

(new name: (identifier) @local.definition)

(identifier) @local.reference
