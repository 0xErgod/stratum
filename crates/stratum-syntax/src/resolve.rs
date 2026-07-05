//! Desugaring: the surface AST ([`crate::ast`]) → a pure [`stratum_core::Proc`].
//!
//! This is where `def`/`new`/macros vanish. All of it is *surface sugar*: the
//! result is an ordinary closed term of the ρ-calculus, with every quote made
//! explicit and no trace of the declarations left in the AST.
//!
//! ## `new` — ground-name generation
//!
//! A "fresh name from nil" is a canonical distinct quote built from `0`:
//!
//! ```text
//! rep(0)   = 0
//! rep(k+1) = @0!(rep(k))          -- 0, @0!(0), @0!(@0!(0)), …
//! ground(k) = @(rep(k))           -- @0, @(@0!(0)), @(@0!(@0!(0))), …
//! ```
//!
//! These are pairwise `≢N` and never quote/drop-reducible (they contain no
//! drops). `ground(0) = @0 = ⌜0⌝` is **reserved**: the reification of the null
//! process is a special name and is never handed out (giving it out would make a
//! fresh channel `a` satisfy `a = ⌜0⌝`, so `a!(0)` would send `a`'s own name and
//! `*a = 0` — a degenerate self-reference). Minting therefore starts at
//! `ground(1)`. A single global counter, advanced in declaration order across
//! every `new` — top-level and macro-local — assigns each minted name its
//! `ground(k)` (`k ≥ 1`). Because a macro's local `new` is resolved afresh on
//! *every* expansion, two expansions of the same macro get distinct channels
//! (hygiene).
//!
//! ## Identifier resolution
//!
//! Lexical, innermost wins: an input binder, then a macro parameter (bound to
//! the call-site argument fragment together with its call-site environment, so
//! substitution is capture-avoiding), then a `new` name, then a `def`. A `def`
//! alias/macro body is resolved under the *global* environment (top-level `new`
//! names + parameters + its own local `new`s) — never the caller's lexical
//! scope — which is what keeps expansion hygienic.

use std::collections::HashMap;
use std::rc::Rc;

use stratum_core::canonicalize_name;
use stratum_core::term::{drop_, fresh_sym, lift, quote, zero, Name, Proc};

use crate::ast::{Args, Block, Def, Pos, S};
use crate::ParseError;

/// `rep(k)` — the `k`-fold nested lift over `0`.
fn rep(k: u64) -> Proc {
    if k == 0 {
        zero()
    } else {
        lift(quote(zero()), rep(k - 1))
    }
}

/// `ground(k) = @(rep(k))` — the `k`-th canonical fresh ground name.
fn ground(k: u64) -> Name {
    quote(rep(k))
}

/// What a bound identifier denotes in the environment.
#[derive(Clone)]
enum Binding {
    /// An input binder resolved to its fresh symbol.
    Var(u64),
    /// A `new`-minted ground name.
    NewName(Name),
    /// A macro parameter: the argument fragment and the environment of the call
    /// site where it was supplied (so it resolves capture-avoidingly).
    Param(Rc<S>, Env),
}

/// A persistent (structurally shared) lexical environment.
///
/// Cloning is cheap — it bumps a reference count — so environments can be
/// captured in parameter bindings and extended freely.
#[derive(Clone, Default)]
struct Env(Option<Rc<Frame>>);

/// One binding frame in the environment chain.
struct Frame {
    name: String,
    binding: Binding,
    parent: Env,
}

impl Env {
    /// Extend with a new innermost binding.
    fn extend(&self, name: String, binding: Binding) -> Env {
        Env(Some(Rc::new(Frame {
            name,
            binding,
            parent: self.clone(),
        })))
    }

    /// Look up `name`, innermost binder first.
    fn lookup(&self, name: &str) -> Option<Binding> {
        let mut cur = &self.0;
        while let Some(frame) = cur {
            if frame.name == name {
                return Some(frame.binding.clone());
            }
            cur = &frame.parent.0;
        }
        None
    }
}

/// Which sort a fragment is being resolved to.
#[derive(Clone, Copy)]
enum Sort {
    /// Process position.
    Proc,
    /// Name position.
    Name,
}

/// The desugaring engine: definition table + the global `new` counter.
pub(crate) struct Resolver<'a> {
    defs: &'a HashMap<String, Def>,
    /// Monotonic counter assigning `ground(k)` to each minted name.
    counter: u64,
    /// The global base environment: top-level `new` names (set once).
    global: Env,
    /// Readable-name dictionary: the canonical form of each top-level `new`
    /// name (and each name-shaped `def` alias) mapped back to its source
    /// identifier. Populated during [`Resolver::resolve_program`] and
    /// [`Resolver::collect_aliases`]; consumed by the alias-folding printer.
    aliases: HashMap<Name, String>,
}

/// Build a resolution error at a position.
fn err(pos: Pos, message: impl Into<String>) -> ParseError {
    ParseError {
        line: pos.0,
        column: pos.1,
        message: message.into(),
    }
}

impl<'a> Resolver<'a> {
    /// Create a resolver over a collected definition table.
    pub(crate) fn new(defs: &'a HashMap<String, Def>) -> Self {
        Resolver {
            defs,
            // `ground(0) = @0 = ⌜0⌝` is reserved; mint fresh names from `ground(1)`.
            counter: 1,
            global: Env::default(),
            aliases: HashMap::new(),
        }
    }

    /// Resolve a whole program to a closed [`Proc`].
    ///
    /// Top-level `new` names are minted first (so they get the lowest `ground`
    /// indices, in declaration order), fixing the global environment, and then
    /// the program term is resolved.
    pub(crate) fn resolve_program(&mut self, program: &Block) -> Result<Proc, ParseError> {
        let mut env = Env::default();
        for (name, _) in &program.news {
            let g = self.mint();
            // Record the readable alias: the canonical ground name folds back
            // to this source identifier. First declaration wins on collision.
            self.aliases
                .entry(canonicalize_name(&g))
                .or_insert_with(|| name.clone());
            env = env.extend(name.clone(), Binding::NewName(g));
        }
        self.global = env.clone();
        self.resolve_proc(&program.term, &env)
    }

    /// Extract the readable-name dictionary gathered during resolution.
    ///
    /// Beyond the top-level `new` names (recorded while resolving the program),
    /// this eagerly resolves every name-shaped `def` alias — one whose body is a
    /// bare name `@P` (possibly via other aliases) and takes no arguments — so a
    /// channel that spells out to such an alias can fold back to its identifier.
    /// Process-shaped aliases and macros have no single canonical name and are
    /// skipped; a name-shaped alias that fails to resolve is silently ignored,
    /// since alias collection must never turn a successful parse into an error.
    /// Call after [`Resolver::resolve_program`], when `global` is fixed.
    pub(crate) fn collect_aliases(&mut self) -> HashMap<Name, String> {
        // Collect candidate alias names first to avoid borrowing `self.defs`
        // across the resolving calls that borrow `self` mutably.
        let candidates: Vec<String> = self
            .defs
            .iter()
            .filter_map(|(name, def)| match def {
                Def::Alias(block) if block.term.is_name_shaped() => Some(name.clone()),
                _ => None,
            })
            .collect();
        for name in candidates {
            // Clone the body out of `self.defs` so the resolve call may borrow
            // `self` mutably (it advances the mint counter for any local `new`).
            if let Some(Def::Alias(block)) = self.defs.get(&name).cloned() {
                let base = self.global.clone();
                if let Ok(Slot::Name(n)) = self.resolve_block(&block, &base, Sort::Name) {
                    self.aliases
                        .entry(canonicalize_name(&n))
                        .or_insert_with(|| name.clone());
                }
            }
        }
        std::mem::take(&mut self.aliases)
    }

    /// Resolve a single name (used by [`crate::parse_name`]).
    pub(crate) fn resolve_name_top(&mut self, s: &S) -> Result<Name, ParseError> {
        let env = Env::default();
        self.resolve_name(s, &env)
    }

    /// Allocate the next ground name and advance the counter.
    fn mint(&mut self) -> Name {
        let g = ground(self.counter);
        self.counter += 1;
        g
    }

    /// Resolve a block (`new`s then a term) in the given sort under `base`.
    fn resolve_block(&mut self, block: &Block, base: &Env, sort: Sort) -> Result<Slot, ParseError> {
        let mut env = base.clone();
        for (name, _) in &block.news {
            let g = self.mint();
            env = env.extend(name.clone(), Binding::NewName(g));
        }
        match sort {
            Sort::Proc => self.resolve_proc(&block.term, &env).map(Slot::Proc),
            Sort::Name => self.resolve_name(&block.term, &env).map(Slot::Name),
        }
    }

    /// Resolve a fragment as a process.
    fn resolve_proc(&mut self, s: &S, env: &Env) -> Result<Proc, ParseError> {
        match s {
            S::Zero => Ok(Proc::Zero),
            S::Drop(name) => Ok(drop_(self.resolve_name(name, env)?)),
            S::Lift { chan, arg } => {
                let chan = self.resolve_name(chan, env)?;
                let arg = self.resolve_proc(arg, env)?;
                Ok(lift(chan, arg))
            }
            S::Input { chan, bound, body } => {
                // The channel is resolved in the enclosing scope, before the binder.
                let chan = self.resolve_name(chan, env)?;
                let sym = fresh_sym();
                let inner = env.extend(bound.clone(), Binding::Var(sym));
                let body = self.resolve_proc(body, &inner)?;
                Ok(Proc::Input {
                    chan,
                    bound: sym,
                    body: Box::new(body),
                })
            }
            S::Par(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(self.resolve_proc(item, env)?);
                }
                Ok(Proc::Par(out))
            }
            S::Quote(_, pos) => Err(err(
                *pos,
                "expected `!` (lift) or `(` (input) after a channel name; \
                 a name (`@…`) is not a process on its own",
            )),
            S::Ident(x, pos) => self.resolve_ident_proc(x, *pos, env),
            S::Call { name, args, pos } => match self.expand(name, args, *pos, env, Sort::Proc)? {
                Slot::Proc(p) => Ok(p),
                Slot::Name(_) => unreachable!("expand honours the requested sort"),
            },
        }
    }

    /// Resolve a fragment as a name.
    fn resolve_name(&mut self, s: &S, env: &Env) -> Result<Name, ParseError> {
        match s {
            S::Quote(body, _) => Ok(Name::Quote(Box::new(self.resolve_proc(body, env)?))),
            S::Ident(x, pos) => self.resolve_ident_name(x, *pos, env),
            S::Call { name, args, pos } => match self.expand(name, args, *pos, env, Sort::Name)? {
                Slot::Name(n) => Ok(n),
                Slot::Proc(_) => unreachable!("expand honours the requested sort"),
            },
            S::Drop(_) | S::Lift { .. } | S::Input { .. } | S::Par(_) | S::Zero => Err(err(
                self.first_pos(s),
                "expected a name (`@…` or a bound identifier), found a process",
            )),
        }
    }

    /// Resolve a bare identifier in process position.
    fn resolve_ident_proc(&mut self, x: &str, pos: Pos, env: &Env) -> Result<Proc, ParseError> {
        if let Some(binding) = env.lookup(x) {
            return match binding {
                Binding::Var(_) => Err(err(
                    pos,
                    format!(
                        "`{x}` is bound as a name here; write `*{x}` to drop it into a process"
                    ),
                )),
                Binding::NewName(_) => Err(err(
                    pos,
                    format!("`{x}` is a name; write `*{x}` to use it as a process"),
                )),
                Binding::Param(arg, cenv) => self.resolve_proc(&arg, &cenv),
            };
        }
        match self.defs.get(x) {
            Some(Def::Alias(block)) => {
                if matches!(block.term, S::Quote(..)) {
                    return Err(err(
                        pos,
                        format!(
                            "`{x}` is defined as a name but is used here where a process is required"
                        ),
                    ));
                }
                let base = self.global.clone();
                match self.resolve_block(block, &base, Sort::Proc)? {
                    Slot::Proc(p) => Ok(p),
                    Slot::Name(_) => unreachable!(),
                }
            }
            Some(Def::Macro { params, .. }) => Err(err(
                pos,
                format!(
                    "macro `{x}` used without arguments; expected {} argument(s), write `{x}(…)`",
                    params.len()
                ),
            )),
            None => Err(err(
                pos,
                format!(
                    "unbound identifier `{x}`; identifiers must be an enclosing input binder, \
                     a `new` name, or a `def` (only quotes `@P` may be free)"
                ),
            )),
        }
    }

    /// Resolve a bare identifier in name position.
    fn resolve_ident_name(&mut self, x: &str, pos: Pos, env: &Env) -> Result<Name, ParseError> {
        if let Some(binding) = env.lookup(x) {
            return match binding {
                Binding::Var(sym) => Ok(Name::Var(sym)),
                Binding::NewName(n) => Ok(n),
                Binding::Param(arg, cenv) => self.resolve_name(&arg, &cenv),
            };
        }
        match self.defs.get(x) {
            Some(Def::Alias(block)) => {
                if !block.term.is_name_shaped() {
                    return Err(err(
                        pos,
                        format!(
                            "`{x}` is defined as a process but is used here where a name is required"
                        ),
                    ));
                }
                let base = self.global.clone();
                match self.resolve_block(block, &base, Sort::Name)? {
                    Slot::Name(n) => Ok(n),
                    Slot::Proc(_) => unreachable!(),
                }
            }
            Some(Def::Macro { .. }) => Err(err(
                pos,
                format!("macro `{x}` must be applied to arguments; write `{x}(…)`"),
            )),
            None => Err(err(
                pos,
                format!(
                    "unbound identifier `{x}`; identifiers must be an enclosing input binder, \
                     a `new` name, or a `def` (only quotes `@P` may be free)"
                ),
            )),
        }
    }

    /// Expand a macro application `name(args)` in the requested sort.
    ///
    /// Positional and named calls differ only in *routing*: [`route_args`] turns
    /// either form into the argument fragments in declared-parameter order (and
    /// reports arity / unknown / duplicate / missing errors). From there on the
    /// two forms are identical — each parameter binds to its fragment together
    /// with the call-site environment (capture-avoiding), and the body is
    /// expanded with the same two-sort checking and hygiene.
    fn expand(
        &mut self,
        name: &str,
        args: &Args,
        pos: Pos,
        call_env: &Env,
        sort: Sort,
    ) -> Result<Slot, ParseError> {
        match self.defs.get(name) {
            Some(Def::Macro { params, body }) => {
                let ordered = route_args(name, params, args, pos)?;
                // Parameters bind to the call-site argument fragments together
                // with the call-site environment (capture-avoiding).
                let mut env = self.global.clone();
                for (param, arg) in params.iter().zip(ordered) {
                    env = env.extend(
                        param.clone(),
                        Binding::Param(Rc::new(arg.clone()), call_env.clone()),
                    );
                }
                // Clone `body` out of `self.defs` to satisfy the borrow checker.
                let body = body.clone();
                self.resolve_block(&body, &env, sort)
            }
            Some(Def::Alias(_)) => Err(err(
                pos,
                format!("`{name}` is an alias, not a macro; it cannot be applied to arguments"),
            )),
            None => Err(err(pos, format!("unbound macro `{name}`"))),
        }
    }

    /// Best-effort position for a fragment, for "process where a name was
    /// expected" diagnostics.
    fn first_pos(&self, s: &S) -> Pos {
        match s {
            S::Quote(_, pos) | S::Ident(_, pos) | S::Call { pos, .. } => *pos,
            S::Drop(n) => self.first_pos(n),
            S::Lift { chan, .. } | S::Input { chan, .. } => self.first_pos(chan),
            S::Par(items) => items.first().map(|s| self.first_pos(s)).unwrap_or((1, 1)),
            S::Zero => (1, 1),
        }
    }
}

/// Route a call's arguments into declared-parameter order.
///
/// This is the *only* place positional and named calls differ. A positional
/// call `f(A, B)` maps argument `i` to parameter `i` (with the existing arity
/// check). A named call `f(p <- A, q <- B)` places each `p <- A` at the position
/// of the parameter named `p`, order-independently, reporting:
///
/// * an **unknown** parameter name (no such parameter in `f`),
/// * a **duplicate** argument for the same parameter, and
/// * a **missing** argument for a declared parameter.
///
/// The returned fragments (borrowed from `args`) are in parameter order, so the
/// caller binds and sort-checks them exactly as for a positional call.
fn route_args<'s>(
    name: &str,
    params: &[String],
    args: &'s Args,
    pos: Pos,
) -> Result<Vec<&'s S>, ParseError> {
    match args {
        Args::Positional(list) => {
            if list.len() != params.len() {
                return Err(err(
                    pos,
                    format!(
                        "macro `{name}` expects {} argument(s), but got {}",
                        params.len(),
                        list.len()
                    ),
                ));
            }
            Ok(list.iter().collect())
        }
        Args::Named(named) => {
            let mut slots: Vec<Option<&S>> = vec![None; params.len()];
            for na in named {
                match params.iter().position(|p| p == &na.param) {
                    None => {
                        return Err(err(
                            na.pos,
                            format!("no parameter named `{}` in macro `{name}`", na.param),
                        ))
                    }
                    Some(i) => {
                        if slots[i].is_some() {
                            return Err(err(
                                na.pos,
                                format!("duplicate argument for parameter `{}`", na.param),
                            ));
                        }
                        slots[i] = Some(&na.value);
                    }
                }
            }
            let mut out = Vec::with_capacity(params.len());
            for (i, slot) in slots.into_iter().enumerate() {
                match slot {
                    Some(s) => out.push(s),
                    None => {
                        return Err(err(
                            pos,
                            format!("missing argument for parameter `{}`", params[i]),
                        ))
                    }
                }
            }
            Ok(out)
        }
    }
}

/// A resolved fragment in whichever sort was requested.
enum Slot {
    /// A process.
    Proc(Proc),
    /// A name.
    Name(Name),
}

// --- static cycle detection -------------------------------------------------

/// Reject cyclic `def` references so that expansion terminates.
///
/// Builds the reference graph — a `def` `A` has an edge to `def` `B` when `B`
/// appears free (not shadowed by a parameter, local `new`, or input binder) in
/// `A`'s body — and reports any cycle. Because the macro language has no
/// conditionals, any cycle in this graph is genuine non-termination.
pub(crate) fn check_acyclic(
    defs: &HashMap<String, Def>,
    decl_pos: &HashMap<String, Pos>,
) -> Result<(), ParseError> {
    // Reference edges per definition.
    let mut edges: HashMap<&str, Vec<String>> = HashMap::new();
    for (name, def) in defs {
        let (params, block): (&[String], &Block) = match def {
            Def::Alias(block) => (&[], block),
            Def::Macro { params, body } => (params, body),
        };
        let mut locals: Vec<String> = params.to_vec();
        locals.extend(block.news.iter().map(|(n, _)| n.clone()));
        let mut refs = Vec::new();
        collect_refs(&block.term, defs, &mut locals, &mut refs);
        edges.insert(name.as_str(), refs);
    }

    // DFS three-colouring to find a back edge.
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let mut colour: HashMap<&str, Colour> =
        defs.keys().map(|k| (k.as_str(), Colour::White)).collect();
    // Iterative DFS with an explicit stack to avoid deep recursion.
    for start in defs.keys() {
        if colour[start.as_str()] != Colour::White {
            continue;
        }
        let mut stack: Vec<(&str, usize)> = vec![(start.as_str(), 0)];
        colour.insert(start.as_str(), Colour::Grey);
        while let Some((node, idx)) = stack.last().copied() {
            let node_edges = edges.get(node).map(|v| v.as_slice()).unwrap_or(&[]);
            if idx < node_edges.len() {
                stack.last_mut().unwrap().1 += 1;
                let next = node_edges[idx].as_str();
                match colour.get(next).copied() {
                    Some(Colour::Grey) => {
                        let pos = decl_pos.get(next).copied().unwrap_or((1, 1));
                        return Err(err(
                            pos,
                            format!(
                                "cyclic definition: `{next}` is (transitively) defined in terms \
                                 of itself; expansion would not terminate"
                            ),
                        ));
                    }
                    Some(Colour::White) => {
                        colour.insert(next, Colour::Grey);
                        stack.push((next, 0));
                    }
                    _ => {}
                }
            } else {
                colour.insert(node, Colour::Black);
                stack.pop();
            }
        }
    }
    Ok(())
}

/// Collect the free references to *definition* names within a fragment.
fn collect_refs(
    s: &S,
    defs: &HashMap<String, Def>,
    locals: &mut Vec<String>,
    out: &mut Vec<String>,
) {
    match s {
        S::Zero => {}
        S::Drop(n) => collect_refs(n, defs, locals, out),
        S::Quote(p, _) => collect_refs(p, defs, locals, out),
        S::Lift { chan, arg } => {
            collect_refs(chan, defs, locals, out);
            collect_refs(arg, defs, locals, out);
        }
        S::Input { chan, bound, body } => {
            collect_refs(chan, defs, locals, out);
            locals.push(bound.clone());
            collect_refs(body, defs, locals, out);
            locals.pop();
        }
        S::Par(items) => {
            for item in items {
                collect_refs(item, defs, locals, out);
            }
        }
        S::Ident(x, _) => {
            if !locals.contains(x) && defs.contains_key(x) {
                out.push(x.clone());
            }
        }
        S::Call { name, args, .. } => {
            if !locals.contains(name) && defs.contains_key(name) {
                out.push(name.clone());
            }
            for arg in args.values() {
                collect_refs(arg, defs, locals, out);
            }
        }
    }
}
