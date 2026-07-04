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
//! * A line beginning with `%%` is a **cell magic**. `%%rune` runs the rest of
//!   the cell as an embedded [Rune](https://rune-rs.github.io/) script with a
//!   curated `stratum` module and the session namespace shared in (see
//!   [`script`]); its `println!` output and final value flow back as the cell's
//!   stdout and display.
//!
//! Results come back as [`MimeBundle`]s (`text/plain` + optional `text/html` /
//! `image/svg+xml`); the front-end maps those onto its own display messages.

#![forbid(unsafe_code)]

mod eval;
mod formula;
mod render;
mod script;
mod service;

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
pub use service::{complete, inspect, is_complete, Completions, Inspection, IsComplete};

/// How an [`Lts`] binding was reduced during exploration — which determines the
/// class of temporal properties whose verdicts are trustworthy against it.
///
/// Partial-order and symmetry reduction both drop the raw next-time (`EX`)
/// branching structure, so a reduced LTS must not be `%check`ed with `EX`, and
/// other verdicts carry a caveat about the preserved fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Reduction {
    /// Full exploration (`%explore`): every property is preserved.
    #[default]
    None,
    /// Partial-order reduction (`%explore ... por`): preserves reachability /
    /// safety of barbs, not full branching structure.
    Por,
    /// Symmetry reduction (`%explore ... sym=...`): preserves
    /// symmetry-invariant properties.
    Symmetry,
}

impl Reduction {
    /// A short human-readable name.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Reduction::None => "full",
            Reduction::Por => "partial-order reduced",
            Reduction::Symmetry => "symmetry reduced",
        }
    }

    /// The caveat describing the fragment whose verdicts remain valid, or `None`
    /// for an unreduced LTS.
    #[must_use]
    pub fn caveat(self) -> Option<&'static str> {
        match self {
            Reduction::None => None,
            Reduction::Por => Some(
                "partial-order reduced LTS: the verdict is only sound for \
                 reachability / safety of barbs, not full branching (no EX).",
            ),
            Reduction::Symmetry => Some(
                "symmetry reduced LTS: the verdict is only sound for \
                 symmetry-invariant properties (no EX).",
            ),
        }
    }
}

/// A value bound in a notebook [`Namespace`].
///
/// The variants grow as directives learn to produce new kinds of result; each
/// carries a first-class toolkit value so a later cell can name it.
#[derive(Debug, Clone)]
pub enum Obj {
    /// A process defined by a DSL cell or an `%expand` / inline directive.
    Proc(Proc),
    /// A trace LTS produced by `%explore`, tagged with how it was reduced.
    Lts {
        /// The explored transition system.
        lts: Lts,
        /// The reduction applied during exploration.
        reduction: Reduction,
    },
    /// An equivalence verdict produced by `%bisim`.
    Verdict(Verdict),
    /// A model-checking result produced by `%check`.
    Checked(Checked),
    /// A boolean result.
    Bool(bool),
    /// An integer result (e.g. a metric computed by a `%%rune` script).
    Int(i64),
    /// Free-form text.
    Text(String),
}

impl Obj {
    /// A short human-readable kind name, for error messages and `%help`.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Obj::Proc(_) => "proc",
            Obj::Lts { .. } => "lts",
            Obj::Verdict(_) => "verdict",
            Obj::Checked(_) => "checked",
            Obj::Bool(_) => "bool",
            Obj::Int(_) => "int",
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
            Some(Obj::Lts { lts, .. }) => Some(lts),
            _ => None,
        }
    }

    /// Look up a bound LTS together with the [`Reduction`] it was explored under.
    #[must_use]
    pub fn get_lts_binding(&self, name: &str) -> Option<(&Lts, Reduction)> {
        match self.objs.get(name) {
            Some(Obj::Lts { lts, reduction }) => Some((lts, *reduction)),
            _ => None,
        }
    }

    /// Resolve a surface identifier to its canonical channel [`Name`], if a DSL
    /// cell has minted it.
    #[must_use]
    pub fn resolve_name(&self, ident: &str) -> Option<Name> {
        self.names.get(ident).cloned()
    }

    /// The names of every object bound in this session, in stable sorted order.
    ///
    /// Used by the interactive [`crate::complete`] / [`crate::inspect`] services
    /// to offer bound namespace names as completion candidates.
    #[must_use]
    pub fn binding_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.objs.keys().cloned().collect();
        names.sort();
        names
    }

    /// The surface identifiers that resolve to a channel [`Name`] in this
    /// session (harvested from every DSL parse), in stable sorted order. These
    /// are the names usable inside `emits(...)` and directive channel lists.
    #[must_use]
    pub fn channel_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.names.keys().cloned().collect();
        names.sort();
        names
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

    /// Allocate the next auto-generated binding name (`_1`, `_2`, …), skipping
    /// any name the user has already bound explicitly so an auto name never
    /// clobbers a `_N =` binding.
    pub(crate) fn next_auto_name(&mut self) -> String {
        loop {
            self.auto_counter += 1;
            let candidate = format!("_{}", self.auto_counter);
            if !self.objs.contains_key(&candidate) {
                return candidate;
            }
        }
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

/// The default observation set shared by the `%bisim` directive and the `bisim`
/// binding in a `%%rune` script: every channel occurring in either process,
/// deduplicated up to structural congruence. Keeping this in one place stops the
/// directive and the scripted binding from silently drifting out of faithfulness.
pub(crate) fn default_observations(p: &Proc, q: &Proc) -> Vec<Name> {
    let mut raw = Vec::new();
    collect_names(p, &mut raw);
    collect_names(q, &mut raw);
    let mut out: Vec<Name> = Vec::new();
    for n in raw {
        let c = canonicalize_name(&n);
        if !out.contains(&c) {
            out.push(c);
        }
    }
    out
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
