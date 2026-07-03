//! The intermediate **surface AST** produced by the parser before desugaring.
//!
//! The recursive-descent parser in [`crate::parser`] builds this tree without
//! resolving identifiers; the [`crate::resolve`] pass then turns it into a pure
//! [`stratum_core::Proc`], expanding `def`/`new`/macros. Keeping an explicit
//! intermediate layer is what lets a single identifier be interpreted as a name
//! or a process depending on the position it lands in after macro substitution.
//!
//! Every node that can be the anchor of a resolution error carries a source
//! [`Pos`] so diagnostics keep the 1-based line/column of the original token.

/// A 1-based source position: `(line, column)`.
pub(crate) type Pos = (usize, usize);

/// A surface expression: a process- or name-shaped fragment with identifiers
/// left unresolved.
///
/// The same node type covers both processes and names because a macro argument
/// is a syntactic hole that may be dropped into either position; which sort is
/// required is only known once substitution places the fragment, and is checked
/// by [`crate::resolve`].
#[derive(Clone, Debug)]
pub(crate) enum S {
    /// `0` / `nil` — the null process.
    Zero,
    /// `*x` — drop of a name-expression.
    Drop(Box<S>),
    /// `x!(P)` — lift of a process on a channel name.
    Lift {
        /// The channel name-expression.
        chan: Box<S>,
        /// The lifted process-expression.
        arg: Box<S>,
    },
    /// `x(y).P` — input; binds the identifier `bound` in `body`.
    Input {
        /// The channel name-expression (resolved in the enclosing scope).
        chan: Box<S>,
        /// The binder identifier text.
        bound: String,
        /// The continuation process-expression.
        body: Box<S>,
    },
    /// `P | Q | …` — parallel composition.
    Par(Vec<S>),
    /// `@P` — the quote of a *primary* process-expression (a name former).
    Quote(Box<S>, Pos),
    /// A bare identifier: an input binder, a `new`-name, a `def` alias, or a
    /// macro parameter, resolved by position.
    Ident(String, Pos),
    /// `NAME(arg1, …, argn)` — a macro application.
    Call {
        /// The macro name.
        name: String,
        /// The argument fragments, resolved at the call site — either all
        /// positional or all named (see [`Args`]).
        args: Args,
        /// Position of the macro name, for diagnostics.
        pos: Pos,
    },
}

/// The arguments of a macro call: **all** positional or **all** named.
///
/// A call is `f(A, B, …)` (positional, argument `i` binds parameter `i`) or
/// `f(p1 <- A, p2 <- B, …)` (named, order-independent, each `p <- A` binds the
/// parameter named `p`). Mixing the two forms in one call is a [`ParseError`].
/// Both forms are pure call-site sugar: routing only decides which argument
/// fragment lands in which parameter hole — expansion, hygiene, and the
/// per-argument sort check are identical afterwards.
///
/// [`ParseError`]: crate::ParseError
#[derive(Clone, Debug)]
pub(crate) enum Args {
    /// `f(A, B, …)` — positional: argument `i` binds parameter `i`.
    Positional(Vec<S>),
    /// `f(p1 <- A, p2 <- B, …)` — named: each argument binds its parameter by
    /// name, order-independent.
    Named(Vec<NamedArg>),
}

impl Args {
    /// The argument value fragments, in source order, regardless of form.
    ///
    /// Used by the free-reference walk (cycle detection); the parameter names of
    /// named arguments are call-site labels, not references, so only the values
    /// are yielded.
    pub(crate) fn values(&self) -> Vec<&S> {
        match self {
            Args::Positional(v) => v.iter().collect(),
            Args::Named(n) => n.iter().map(|a| &a.value).collect(),
        }
    }
}

/// One `param <- value` argument in a named macro call.
#[derive(Clone, Debug)]
pub(crate) struct NamedArg {
    /// The target parameter name.
    pub(crate) param: String,
    /// Position of the parameter name, for diagnostics (unknown/duplicate).
    pub(crate) pos: Pos,
    /// The argument fragment, resolved at the call site.
    pub(crate) value: S,
}

impl S {
    /// Whether this fragment is *name-shaped* — a quote `@P` or a bare
    /// identifier — as opposed to a manifestly process-shaped form.
    ///
    /// Used to give the "definition used in the wrong position" diagnostics a
    /// precise anchor before recursing into a definition body.
    pub(crate) fn is_name_shaped(&self) -> bool {
        matches!(self, S::Quote(..) | S::Ident(..))
    }
}

/// A braced body or the top-level program: a run of local `new` declarations
/// followed by a single term.
#[derive(Clone, Debug)]
pub(crate) struct Block {
    /// Local `new`-declared names, in declaration order, with their positions.
    pub(crate) news: Vec<(String, Pos)>,
    /// The body term.
    pub(crate) term: S,
}

/// A collected declaration: a nullary alias or a parameterized macro.
#[derive(Clone, Debug)]
pub(crate) enum Def {
    /// `def NAME { BODY }` — an alias for a name or a process.
    Alias(Block),
    /// `def NAME(p1, …, pn) { BODY }` — a parameterized macro (an encoding).
    Macro {
        /// The formal parameter names, in order.
        params: Vec<String>,
        /// The macro body.
        body: Block,
    },
}
