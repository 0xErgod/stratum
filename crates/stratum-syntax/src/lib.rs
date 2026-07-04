//! # stratum-syntax
//!
//! A concrete **surface syntax** (a small DSL) for writing terms of the
//! reflective higher-order (ρ) calculus of Meredith & Radestock, *A Reflective
//! Higher-order Calculus* (ENTCS 141(5), 2005), together with a hand-written
//! recursive-descent [`parse`]r that produces a [`stratum_core::Proc`].
//!
//! ## The syntax
//!
//! An ASCII transliteration of Meredith's notation:
//!
//! ```text
//! P, Q ::= 0 | nil        the null process
//!        | x(y) . P        input on channel x, binding the name y in P
//!        | x!(P)           lift: asynchronous output of the process P on x
//!        | *x              drop / dereference of a name
//!        | P | Q           parallel composition
//!        | ( P )           grouping
//! x, y  ::= @P             the quote of a process (the only name former)
//!        | <identifier>    a name bound by an enclosing input
//! ```
//!
//! * `|` is parallel (lowest precedence, left-associative / flat).
//! * The input prefix `x(y).` and the lift `x!(…)` bind tighter than `|`, so the
//!   continuation of an input runs only up to the next `|`: `x(y).*y | Q` is
//!   `(x(y).*y) | Q`.
//! * `*` binds tightly to a following name; `@` binds tightly to a following
//!   *primary* process (`0`, `*x`, or a parenthesized group), so `@0!(0)` is
//!   `(@0)!(0)` — the quote is of `0`, not of `0!(0)`.
//! * Line comments `// …` run to end of line; whitespace is insignificant.
//!
//! ## Closed terms and the input-bound-identifier rule
//!
//! Terms of the pure calculus are *closed*: the only free names are quotes
//! `@P`. Accordingly, a bare identifier is legal only when some enclosing input
//! binds it; a free (unbound) identifier is a [`ParseError`]. Each binder is
//! resolved to a fresh [`stratum_core::fresh_sym`] symbol at its `x(y).…`, and
//! every occurrence of `y` in the continuation resolves to that same
//! [`Name::Var`]. Scoping is lexical and inner binders shadow outer ones of the
//! same name.
//!
//! ## Declarations: `def`, `new`, and macros (pure surface sugar)
//!
//! A file may open with a preamble of declarations, then exactly one program
//! process:
//!
//! ```text
//! def NAME { BODY }              // alias for a name or a process
//! def NAME(p1, …, pn) { BODY }   // parameterized macro (an "encoding")
//! new n1, …, nk                  // mint k distinct fresh ground names
//! ```
//!
//! All of this is **pure surface sugar**: it is expanded at parse time, so
//! [`parse`] still returns an ordinary closed [`Proc`] with no trace of the
//! declarations. `new` is *name generation*, not the ν/restriction of the
//! π-calculus: `new n1, …` mints canonical distinct ground names `@0`,
//! `@(@0!(0))`, … (nested lifts over `0`, quoted), assigned by a global counter
//! in declaration order. A macro's local `new` is minted afresh on every
//! expansion, so repeated expansions get distinct channels (hygiene). Macro
//! arguments are substituted capture-avoidingly, cyclic definitions are
//! rejected, and everything is transparent: [`expand`] shows the fully
//! desugared raw term.
//!
//! ```
//! use stratum_syntax::{expand, parse};
//! use stratum_core::structurally_congruent;
//!
//! // `new` mints ground names; the program desugars to a pure term.
//! let sugared = "new req, ack\nreq!(0) | req(x).ack!(0)";
//! let raw = "@0!(0) | @0(x).@(@0!(0))!(0)";
//! assert!(structurally_congruent(
//!     &parse(sugared).unwrap(),
//!     &parse(raw).unwrap(),
//! ));
//! // `expand` reveals the desugaring.
//! assert_eq!(expand(sugared).unwrap(), "@0!(0) | @0(v0).@(@0!(0))!(0)");
//! ```
//!
//! ## Two parsers
//!
//! This crate ships the syntax twice:
//!
//! * The **recursive-descent parser** here is the *runtime*: pure Rust, no C
//!   toolchain, the default build. Use [`parse`] / [`parse_name`].
//! * A **tree-sitter grammar** (under `tree-sitter/`) is the *tooling spec*:
//!   editor highlighting, incremental parsing, and an inspectable CST. Its Rust
//!   binding lives behind the off-by-default `tree-sitter` feature
//!   ([`tree_sitter_language`]).
//!
//! They share one surface grammar, but the tree-sitter grammar is a permissive
//! *superset*: as a CST grammar it accepts an empty file and open terms, whereas
//! the runtime [`parse`] additionally requires a non-empty process and enforces
//! the closed-term rule above.
//!
//! ## Examples
//!
//! ```
//! use stratum_syntax::parse;
//! use stratum_core::term::{drop_, input, lift, quote, zero};
//! use stratum_core::structurally_congruent;
//!
//! assert!(structurally_congruent(&parse("0").unwrap(), &zero()));
//! assert!(structurally_congruent(
//!     &parse("@0!(0)").unwrap(),
//!     &lift(quote(zero()), zero()),
//! ));
//! assert!(structurally_congruent(
//!     &parse("@0(y).*y").unwrap(),
//!     &input(quote(zero()), |y| drop_(y)),
//! ));
//!
//! // A free identifier is rejected.
//! assert!(parse("*y").is_err());
//! ```

#![deny(unsafe_code)]

mod ast;
mod lexer;
mod parser;
mod render;
mod resolve;

pub use render::{
    latex_ident, name_to_latex, to_latex, to_latex_folded, to_source, to_source_folded,
};
pub use stratum_core::{Name, Proc};

use std::collections::HashMap;
use std::fmt;

/// An error produced while lexing or parsing surface syntax.
///
/// Positions are 1-based. The [`fmt::Display`] impl renders a single-line
/// diagnostic of the form `parse error at line L, column C: message`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// 1-based line of the offending token/character.
    pub line: usize,
    /// 1-based column of the offending token/character.
    pub column: usize,
    /// A human-readable description of what went wrong.
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parse error at line {}, column {}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

/// Parse a surface-syntax process into a [`Proc`].
///
/// Returns [`ParseError`] on a lexical error, a syntax error, or a free
/// (unbound) identifier. See the [crate docs](crate) for the grammar.
///
/// ```
/// use stratum_syntax::parse;
/// let p = parse("@0!(0) | @0(y).(*y | @0!(0))").unwrap();
/// assert!(p.is_closed());
/// ```
pub fn parse(src: &str) -> Result<Proc, ParseError> {
    let toks = lexer::lex(src)?;
    let program = parser::Parser::new(toks).parse_file()?;
    resolve::check_acyclic(&program.defs, &program.decl_pos)?;
    resolve::Resolver::new(&program.defs).resolve_program(&program.program)
}

/// A readable-name dictionary: the *canonical* form of a name mapped back to the
/// source identifier it was introduced under.
///
/// Produced by [`parse_with_aliases`] and consumed by [`to_source_folded`], this
/// captures the `def`/`new` names of the parsed source so the term can be
/// printed the way it was written. Keys are canonicalized with
/// [`stratum_core::canonicalize_name`], so a lookup succeeds up to structural
/// congruence regardless of how a matching name is spelled; use [`Aliases::get`]
/// (which canonicalizes the query for you) rather than reaching for a raw key.
#[derive(Clone, Debug, Default)]
pub struct Aliases {
    map: HashMap<Name, String>,
}

impl Aliases {
    /// Wrap a map whose keys are already [`stratum_core::canonicalize_name`]d.
    pub(crate) fn from_canonical_map(map: HashMap<Name, String>) -> Self {
        Aliases { map }
    }

    /// The source identifier `name` folds to, if any.
    ///
    /// `name` is canonicalized before the lookup, so it need not be in canonical
    /// form. Returns `None` when the name has no alias (e.g. a raw `@0` with no
    /// `def`/`new` behind it, or an input-bound variable).
    ///
    /// ```
    /// use stratum_syntax::parse_with_aliases;
    /// use stratum_core::term::{quote, zero};
    ///
    /// let (_p, aliases) = parse_with_aliases("new req\nreq!(0)").unwrap();
    /// assert_eq!(aliases.get(&quote(zero())), Some("req")); // @0 folds to `req`
    /// ```
    pub fn get(&self, name: &Name) -> Option<&str> {
        self.map
            .get(&stratum_core::canonicalize_name(name))
            .map(String::as_str)
    }

    /// The number of distinct canonical names that fold to an identifier.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether no name folds to an alias (the source had no `def`/`new` names).
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// Parse a surface-syntax process, also returning its readable-name [`Aliases`].
///
/// Identical to [`parse`] for the returned [`Proc`] — the same closed term, with
/// all sugar expanded — but additionally hands back the dictionary mapping each
/// top-level `new` name and name-shaped `def` alias (canonically) to the source
/// identifier it was written as. Pair it with [`to_source_folded`] to render the
/// term the way it was written.
///
/// ```
/// use stratum_syntax::{parse, parse_with_aliases, to_source_folded};
/// use stratum_core::structurally_congruent;
///
/// let src = "new req, ack\nreq!(0) | req(x).ack!(0)";
/// let (p, aliases) = parse_with_aliases(src).unwrap();
/// // The process is exactly what `parse` yields.
/// assert!(structurally_congruent(&p, &parse(src).unwrap()));
/// // And it can be printed back with its source names.
/// assert_eq!(to_source_folded(&p, &aliases), "req!(0) | req(v0).ack!(0)");
/// ```
pub fn parse_with_aliases(src: &str) -> Result<(Proc, Aliases), ParseError> {
    let toks = lexer::lex(src)?;
    let program = parser::Parser::new(toks).parse_file()?;
    resolve::check_acyclic(&program.defs, &program.decl_pos)?;
    let mut resolver = resolve::Resolver::new(&program.defs);
    let proc = resolver.resolve_program(&program.program)?;
    let aliases = Aliases::from_canonical_map(resolver.collect_aliases());
    Ok((proc, aliases))
}

/// Parse a surface-syntax name into a [`Name`].
///
/// Because names are parsed with an empty scope, only quote forms `@P` succeed
/// at the top level; a bare identifier would be unbound and is rejected.
///
/// ```
/// use stratum_syntax::parse_name;
/// use stratum_core::term::{quote, zero};
/// use stratum_core::name_equiv;
/// assert!(name_equiv(&parse_name("@0").unwrap(), &quote(zero())));
/// ```
pub fn parse_name(src: &str) -> Result<Name, ParseError> {
    let toks = lexer::lex(src)?;
    let s = parser::Parser::new(toks).parse_name_program()?;
    let defs = std::collections::HashMap::new();
    resolve::Resolver::new(&defs).resolve_name_top(&s)
}

/// Desugar sugared surface source to fully-explicit raw surface syntax.
///
/// [`parse`]s `src` (expanding `def`/`new`/macros) and renders the resulting
/// core [`Proc`] back with [`to_source`]. The output is transparent — it
/// contains no `def`/`new`/macro sugar, every quote `@…` is explicit — and
/// re-parses to a term structurally congruent to `parse(src)`.
///
/// ```
/// use stratum_syntax::{expand, parse};
/// use stratum_core::structurally_congruent;
///
/// let src = "new req, ack\nreq!(0) | req(x).ack!(0)";
/// let raw = expand(src).unwrap();
/// assert!(!raw.contains("new") && !raw.contains("def"));
/// assert!(structurally_congruent(
///     &parse(&raw).unwrap(),
///     &parse(src).unwrap(),
/// ));
/// ```
pub fn expand(src: &str) -> Result<String, ParseError> {
    let p = parse(src)?;
    Ok(to_source(&p))
}

/// The compiled tree-sitter grammar for the surface syntax.
///
/// Only available with the off-by-default `tree-sitter` feature, which compiles
/// the generated `tree-sitter/src/parser.c`. This exposes the same surface
/// grammar as [`parse`] (a permissive superset; see the crate docs), for
/// editor tooling and incremental
/// parsing.
#[cfg(feature = "tree-sitter")]
#[allow(unsafe_code)]
pub fn tree_sitter_language() -> tree_sitter::Language {
    extern "C" {
        fn tree_sitter_stratum() -> tree_sitter::Language;
    }
    // SAFETY: `tree_sitter_stratum` is the generated entry point compiled from
    // `tree-sitter/src/parser.c`; it returns a valid, statically-allocated
    // language table.
    unsafe { tree_sitter_stratum() }
}
