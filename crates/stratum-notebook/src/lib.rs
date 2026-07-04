//! # stratum-notebook
//!
//! The reusable, substrate-agnostic notebook core for Stratum. It owns the
//! *interactive* state and presentation logic that any front-end — the Jupyter
//! kernel (`stratum-kernel`), a future web REPL, an LSP server — layers on top
//! of the [`stratum`] toolkit. Keeping this crate free of any transport (no
//! ZeroMQ, no HTTP) is what lets the same evaluation/rendering semantics back
//! every front-end.
//!
//! ## Phase 1 (DSL-first research front)
//!
//! A notebook session is a persistent [`Namespace`] of named objects ([`Obj`]).
//! [`evaluate`] runs one cell against it:
//!
//! * A plain **DSL cell** parses a process (with an optional leading `name =`
//!   binding), binds it into the namespace, and renders the transparency pair.
//! * A line beginning with `%` is a **directive** — a thin wrapper over the
//!   toolkit (`%explore`, `%check`, `%bisim`, `%typecheck`, …) that renders its
//!   result and optionally binds it with `-> name`.
//! * A line beginning with `%%` is a **cell magic** (`%%rune` is reserved for a
//!   later phase).
//!
//! Results come back as [`MimeBundle`]s (`text/plain` + optional `text/html` /
//! `image/svg+xml`); the front-end maps those onto its own display messages.

#![forbid(unsafe_code)]

mod eval;
mod formula;
mod render;

use std::collections::HashMap;

use stratum::core::{canonicalize_name, Name, Proc};
use stratum::equiv::Verdict;
use stratum::logic::Checked;
use stratum::lts::Lts;
use stratum::syntax::Aliases;

pub use eval::evaluate;
pub use formula::{parse_formula, CompiledFormula, FormulaError};
pub use render::{
    dot_to_svg, escape_html, render_checked, render_lts, render_proc, render_run, render_typecheck,
    render_verdict, MimeBundle,
};

/// A value bound in a notebook [`Namespace`].
///
/// The variants grow as directives learn to produce new kinds of result; each
/// carries a first-class toolkit value so a later cell can name it.
#[derive(Debug, Clone)]
pub enum Obj {
    /// A process defined by a DSL cell or an `%expand` / inline directive.
    Proc(Proc),
    /// A trace LTS produced by `%explore`.
    Lts(Lts),
    /// An equivalence verdict produced by `%bisim`.
    Verdict(Verdict),
    /// A model-checking result produced by `%check`.
    Checked(Checked),
    /// A boolean result.
    Bool(bool),
    /// Free-form text.
    Text(String),
}

impl Obj {
    /// A short human-readable kind name, for error messages and `%help`.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Obj::Proc(_) => "proc",
            Obj::Lts(_) => "lts",
            Obj::Verdict(_) => "verdict",
            Obj::Checked(_) => "checked",
            Obj::Bool(_) => "bool",
            Obj::Text(_) => "text",
        }
    }
}

/// The per-session interactive environment: the bindings accumulated by earlier
/// cells, plus the name/alias tables the evaluator needs to resolve DSL
/// identifiers across cells.
#[derive(Debug, Default, Clone)]
pub struct Namespace {
    /// Named objects, insertion order not tracked (keyed by name).
    objs: HashMap<String, Obj>,
    /// Surface identifier → canonical channel [`Name`], accumulated from every
    /// DSL parse so `emits(<name>)` and `%typecheck` can resolve a name minted
    /// in an earlier cell.
    names: HashMap<String, Name>,
    /// The alias table from the most recent DSL parse, used for folded
    /// rendering (`to_source_folded`).
    aliases: Aliases,
    /// Counter for auto-generated binding names (`_1`, `_2`, …).
    auto_counter: usize,
}

impl Namespace {
    /// Create a fresh, empty namespace for a new notebook session.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind (or rebind) `name` to `obj`.
    pub fn insert(&mut self, name: impl Into<String>, obj: Obj) {
        self.objs.insert(name.into(), obj);
    }

    /// Look up a bound object by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Obj> {
        self.objs.get(name)
    }

    /// Look up a bound [`Proc`] by name.
    #[must_use]
    pub fn get_proc(&self, name: &str) -> Option<&Proc> {
        match self.objs.get(name) {
            Some(Obj::Proc(p)) => Some(p),
            _ => None,
        }
    }

    /// Look up a bound [`Lts`] by name.
    #[must_use]
    pub fn get_lts(&self, name: &str) -> Option<&Lts> {
        match self.objs.get(name) {
            Some(Obj::Lts(l)) => Some(l),
            _ => None,
        }
    }

    /// Resolve a surface identifier to its canonical channel [`Name`], if a DSL
    /// cell has minted it.
    #[must_use]
    pub fn resolve_name(&self, ident: &str) -> Option<Name> {
        self.names.get(ident).cloned()
    }

    /// The alias table from the most recent DSL parse.
    #[must_use]
    pub fn aliases(&self) -> &Aliases {
        &self.aliases
    }

    /// Record the alias table of a fresh parse and harvest its surface→canonical
    /// name bindings so later cells can resolve those identifiers.
    pub(crate) fn absorb_aliases(&mut self, proc: &Proc, aliases: Aliases) {
        let mut names = Vec::new();
        collect_names(proc, &mut names);
        for n in names {
            if let Some(surface) = aliases.get(&n) {
                self.names
                    .insert(surface.to_string(), canonicalize_name(&n));
            }
        }
        self.aliases = aliases;
    }

    /// Allocate the next auto-generated binding name (`_1`, `_2`, …).
    pub(crate) fn next_auto_name(&mut self) -> String {
        self.auto_counter += 1;
        format!("_{}", self.auto_counter)
    }
}

/// Collect every channel [`Name`] occurring in a process (recursing through
/// quoted sub-processes), so their aliases can be harvested.
pub(crate) fn collect_names(p: &Proc, out: &mut Vec<Name>) {
    match p {
        Proc::Zero => {}
        Proc::Input { chan, body, .. } => {
            out.push(chan.clone());
            collect_names_in_name(chan, out);
            collect_names(body, out);
        }
        Proc::Lift { chan, arg, .. } => {
            out.push(chan.clone());
            collect_names_in_name(chan, out);
            collect_names(arg, out);
        }
        Proc::Drop(n) => {
            out.push(n.clone());
            collect_names_in_name(n, out);
        }
        Proc::Par(ps) => {
            for q in ps {
                collect_names(q, out);
            }
        }
    }
}

fn collect_names_in_name(n: &Name, out: &mut Vec<Name>) {
    if let Name::Quote(p) = n {
        collect_names(p, out);
    }
}

/// A structured cell error, mapped by a front-end onto its error display (for
/// Jupyter: `ename` / `evalue` / `traceback`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellError {
    /// Error class name (e.g. `ParseError`, `DirectiveError`).
    pub ename: String,
    /// Human-readable message.
    pub evalue: String,
    /// Multi-line detail (e.g. a source line with a caret).
    pub traceback: Vec<String>,
}

impl CellError {
    /// A cell error whose traceback is just the message.
    #[must_use]
    pub fn new(ename: impl Into<String>, evalue: impl Into<String>) -> Self {
        let evalue = evalue.into();
        Self {
            ename: ename.into(),
            traceback: vec![evalue.clone()],
            evalue,
        }
    }

    /// A cell error with an explicit multi-line traceback.
    #[must_use]
    pub fn with_traceback(
        ename: impl Into<String>,
        evalue: impl Into<String>,
        traceback: Vec<String>,
    ) -> Self {
        Self {
            ename: ename.into(),
            evalue: evalue.into(),
            traceback,
        }
    }
}

/// The full result of evaluating one cell: zero or more displays, any streamed
/// stdout, and an optional error.
#[derive(Debug, Clone, Default)]
pub struct CellOutcome {
    /// Rich displays, in order. A front-end emits one `display_data` each.
    pub displays: Vec<MimeBundle>,
    /// Text streamed to stdout during evaluation.
    pub stream_stdout: String,
    /// The error, if the cell failed.
    pub error: Option<CellError>,
}

impl CellOutcome {
    /// An outcome carrying a single display.
    #[must_use]
    pub fn display(bundle: MimeBundle) -> Self {
        Self {
            displays: vec![bundle],
            stream_stdout: String::new(),
            error: None,
        }
    }

    /// An outcome carrying just an error.
    #[must_use]
    pub fn err(error: CellError) -> Self {
        Self {
            displays: Vec::new(),
            stream_stdout: String::new(),
            error: Some(error),
        }
    }
}
