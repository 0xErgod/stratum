/**
 * @file Surface syntax for the reflective higher-order (ρ) calculus.
 * @author Stratum
 * @license MIT OR Apache-2.0
 *
 * This grammar is the *tooling* spec for the surface syntax also accepted by the
 * hand-written recursive-descent parser in `src/`. As a context-free CST grammar
 * it is a deliberate *superset* of the runtime language: it accepts an empty file
 * and open terms (free identifiers), leaving the non-empty-program requirement
 * and the closed-term rule to the runtime parser. It is deliberately CST-shaped
 * (named nodes for every construct, fields for the interesting children) rather
 * than producing the core AST directly.
 *
 * Grammar (ASCII transliteration of Meredith's notation):
 *
 *   file ::= declaration* process?
 *   declaration ::= 'def' NAME ('(' params ')')? '{' block '}'
 *                 | 'new' NAME (',' NAME)*
 *   P, Q ::= 0 | nil | x(y).P | x!(P) | *x | P | Q | ( P ) | NAME '(' args ')'
 *   x, y  ::= @P | <identifier>
 *
 * `def`/`new`/macros are *pure surface sugar* the runtime parser desugars away;
 * this CST grammar merely exposes them for tooling. Precedence: `|` (parallel)
 * is lowest; the input prefix `x(y).` and lift `x!(…)` bind tighter than `|`;
 * `*` binds to a name; `@` binds to a *primary* process (so `@0!(0)` is
 * `(@0)!(0)`).
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: 'stratum',

  word: $ => $.identifier,

  extras: $ => [/\s/, $.comment],

  // An input `x(y).P` and a macro application `f(args)` both begin
  // `identifier '('`; the CST grammar keeps both and lets the GLR parser pick by
  // lookahead (the trailing `.` marks an input). The authoritative disambiguation
  // is the recursive-descent runtime (a `def`-declared name is a macro).
  conflicts: $ => [
    [$._name, $.call],
  ],

  rules: {
    // A file is a preamble of declarations followed by an optional process. The
    // runtime additionally requires exactly one (non-empty) program process.
    source_file: $ => seq(
      repeat($._declaration),
      optional($._process),
    ),

    // --- declarations ---------------------------------------------------

    _declaration: $ => choice(
      $.def,
      $.new,
    ),

    // `def NAME { BODY }` (alias) or `def NAME(p1, …) { BODY }` (macro).
    def: $ => seq(
      'def',
      field('name', $.identifier),
      optional(field('params', $.parameters)),
      field('body', $.def_body),
    ),

    // `(p1, …, pn)` — a macro's formal parameters.
    parameters: $ => seq(
      '(',
      field('param', $.identifier),
      repeat(seq(',', field('param', $.identifier))),
      ')',
    ),

    // `{ new* (process | name) }` — a definition body. A body may be a bare name
    // (`@0`), making the definition a name-alias.
    def_body: $ => seq(
      '{',
      repeat($.new),
      optional(choice($._process, $.quote)),
      '}',
    ),

    // `new n1, …, nk` — mint k distinct fresh ground names.
    new: $ => seq(
      'new',
      field('name', $.identifier),
      repeat(seq(',', field('name', $.identifier))),
    ),

    // --- processes ------------------------------------------------------

    // A process is a parallel composition or a single term.
    _process: $ => choice(
      $.parallel,
      $._term,
    ),

    // `P | Q` — parallel, lowest precedence, left-associative.
    parallel: $ => prec.left(1, seq(
      field('left', $._process),
      '|',
      field('right', $._process),
    )),

    // The prefix-level terms: everything that binds tighter than `|`.
    _term: $ => choice(
      $.nil,
      $.drop,
      $.lift,
      $.input,
      $.call,
      $.use,
      $.parens,
    ),

    // `0` or `nil` — the null process.
    nil: _ => choice('0', 'nil'),

    // `*x` — drop / dereference of a name.
    drop: $ => seq('*', field('name', $._name)),

    // `x!(P)` — lift of a process on a channel.
    lift: $ => seq(
      field('channel', $._name),
      '!',
      '(',
      field('arg', $._process),
      ')',
    ),

    // `x(y).P` — input; binds `y` in the continuation. Right-associative so a
    // chain `x(y).a(z).P` nests to the right.
    input: $ => prec.right(2, seq(
      field('channel', $._name),
      '(',
      field('bind', $.identifier),
      ')',
      '.',
      field('body', $._term),
    )),

    // `NAME(arg1, …, argn)` — a macro application. Each argument is positional
    // (a process or bare name `@0`) or named (`param <- value`, order-independent).
    // Which sort each argument must have is fixed by the parameter's usage, and
    // checked by the runtime. As a permissive CST superset this rule accepts a
    // *mix* of positional and named arguments, and named arguments whose `param`
    // is not a real parameter of the macro; the recursive-descent runtime is
    // authoritative and rejects mixed calls and unknown/duplicate/missing names.
    call: $ => seq(
      field('macro', $.identifier),
      '(',
      optional(seq(
        field('arg', $._call_argument),
        repeat(seq(',', field('arg', $._call_argument))),
      )),
      ')',
    ),

    // A macro-call argument: positional or named.
    _call_argument: $ => choice($._argument, $.named_argument),

    // `param <- value` — a named argument binding one parameter by name.
    named_argument: $ => seq(
      field('param', $.identifier),
      '<-',
      field('value', $._argument),
    ),

    // A macro argument value: a process or a bare quote name.
    _argument: $ => choice($._process, $.quote),

    // A bare identifier used as a process: a `def` alias or a macro parameter.
    use: $ => prec(-1, $.identifier),

    // `( P )` — grouping.
    parens: $ => seq('(', $._process, ')'),

    // A name is a quote or a bound identifier.
    _name: $ => choice(
      $.quote,
      $.identifier,
    ),

    // `@P` — the quote of a *primary* (tightly-bound) process.
    quote: $ => seq('@', field('body', $._primary)),

    // The tight process that may follow `@` without grouping.
    _primary: $ => choice(
      $.nil,
      $.drop,
      $.parens,
    ),

    // Identifiers; `nil` is reserved (handled by `word`).
    identifier: _ => /[A-Za-z_][A-Za-z0-9_]*/,

    // Line comment.
    comment: _ => token(seq('//', /[^\n]*/)),
  },
});
