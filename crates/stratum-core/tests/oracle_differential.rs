//! Differential test against the **machine-checked Coq oracle** (issue #16,
//! Tier-3).
//!
//! The trust chain closed here:
//!
//! ```text
//!   Rust engine  ⇐ this test ⇒  corpus  ⇐ vm_compute ⇐  Coq-proven canon/step
//!                                                        (Print Assumptions:
//!                                                         Closed — ZERO axioms)
//! ```
//!
//! `proofs/Rho.v` proves `canon` a sound+complete decision procedure for `≡`
//! (`canon_decides`) and `step` sound+complete for one-step Comm reduction
//! (`step_sound`/`step_complete`), all `Qed` with **no** remaining axioms (the
//! `pleb` order laws are now *proved* of a concrete comparator). `proofs/Extract.v`
//! (a) *extracts* those verified functions to OCaml (`proofs/oracle.ml`) and
//! (b) has the Coq **kernel** `vm_compute` them on a fixed list of closed,
//! de-Bruijn-explicit ρ-terms, serializing the results to `oracle_corpus.txt`.
//! Kernel evaluation of a `Qed`-verified function is the proven oracle just as the
//! extracted OCaml would be — the OCaml toolchain was unavailable on the build
//! host, so the kernel is the evaluator (documented in `Extract.v`).
//!
//! This test parses that corpus and asserts, for every vector, that the Rust
//! `canonicalize` / `step` **agree** with the proven oracle.
//!
//! ## The α / de-Bruijn boundary (precise scope of the comparison)
//!
//! The Coq model treats `var n` as an *opaque* de-Bruijn atom and does **not**
//! model the Rust engine's nominal→de-Bruijn conversion (the `env` push/pop in
//! `congruence.rs`). To keep the differential comparing the *engine* (`canon` /
//! `step`) and not that unmodelled conversion, every corpus term is **closed** and
//! **de-Bruijn-explicit**, and both sides use the same index convention (index `0`
//! = innermost binder). The Rust side reconstructs a nominal term (allocating a
//! fresh binder symbol per `Input`, resolving `(V k)` to the k-th enclosing
//! binder) and then runs `canonicalize`, which recomputes exactly those indices —
//! so this test additionally exercises, and pins, the conversion *for these closed
//! terms*.
//!
//! Canonical forms are compared **modulo the order of parallel components**: the
//! canonical representative's component order is a documented design freedom (the
//! `pleb` order in Coq vs the derived `Ord` in Rust); `canon p = canon q` means the
//! component multisets are permutations (`sort_par_perm`). [`normalize`] re-sorts
//! `Par` components by Rust's `Ord` on both sides, so the assertion tests that the
//! two engines produce the *same canonical term up to that freedom* — a genuine
//! cross-engine check (a real disagreement in flattening, de-Bruijn indexing, or
//! quote-drop would survive re-sorting), not a tautology.

use stratum_core::congruence::canonicalize;
use stratum_core::reduce::step;
use stratum_core::term::{fresh_sym, Name, Proc};

/// The committed corpus: `term | canon term | step-set` per line, S-expressions
/// (`Z`, `(I n p)`, `(L n p)`, `(D n)`, `(P p p)`; names `(V k)`, `(Q p)`; the
/// step-set is `;;`-separated, possibly empty), produced by `proofs/Extract.v`.
const CORPUS: &str = include_str!("oracle_corpus.txt");

// ---------------------------------------------------------------------------
// S-expression tokenizer + recursive-descent parser.
// ---------------------------------------------------------------------------

fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

struct Parser<'a> {
    toks: &'a [String],
    pos: usize,
    /// Stack of enclosing binder symbols (innermost last); `None` ⇒ *literal*
    /// mode, in which `(V k)` becomes `Name::Var(k)` verbatim (for parsing the
    /// oracle's already-de-Bruijn canonical outputs).
    env: Option<Vec<u64>>,
}

impl<'a> Parser<'a> {
    fn new(toks: &'a [String], nominal: bool) -> Self {
        Parser {
            toks,
            pos: 0,
            env: if nominal { Some(Vec::new()) } else { None },
        }
    }

    fn peek(&self) -> &str {
        &self.toks[self.pos]
    }

    fn eat(&mut self) -> String {
        let t = self.toks[self.pos].clone();
        self.pos += 1;
        t
    }

    fn expect(&mut self, t: &str) {
        let got = self.eat();
        assert_eq!(got, t, "expected `{t}`");
    }

    fn proc(&mut self) -> Proc {
        if self.peek() == "Z" {
            self.eat();
            return Proc::Zero;
        }
        self.expect("(");
        let head = self.eat();
        let p = match head.as_str() {
            "I" => {
                let chan = self.name();
                // The channel is resolved *before* this input binds its name.
                let bound = match &mut self.env {
                    Some(env) => {
                        let s = fresh_sym();
                        env.push(s);
                        s
                    }
                    None => 0,
                };
                let body = self.proc();
                if let Some(env) = &mut self.env {
                    env.pop();
                }
                Proc::Input {
                    chan,
                    bound,
                    body: Box::new(body),
                }
            }
            "L" => {
                let chan = self.name();
                let arg = self.proc();
                Proc::Lift {
                    chan,
                    arg: Box::new(arg),
                }
            }
            "D" => Proc::Drop(self.name()),
            "P" => {
                let a = self.proc();
                let b = self.proc();
                Proc::Par(vec![a, b])
            }
            other => panic!("bad proc head `{other}`"),
        };
        self.expect(")");
        p
    }

    fn name(&mut self) -> Name {
        self.expect("(");
        let head = self.eat();
        let n = match head.as_str() {
            "V" => {
                let k: u64 = self.eat().parse().expect("V index");
                match &self.env {
                    // Nominal mode: resolve the de-Bruijn index to the k-th
                    // enclosing binder symbol (index 0 = innermost).
                    Some(env) => {
                        let depth = env.len();
                        let idx = depth
                            .checked_sub(1 + k as usize)
                            .expect("free var in supposedly-closed corpus term");
                        Name::Var(env[idx])
                    }
                    // Literal mode: keep the de-Bruijn index as-is.
                    None => Name::Var(k),
                }
            }
            "Q" => Name::Quote(Box::new(self.proc())),
            other => panic!("bad name head `{other}`"),
        };
        self.expect(")");
        n
    }
}

/// Parse one S-expression as a **nominal** term (fresh binder symbols; de-Bruijn
/// occurrences resolved to enclosing binders) — the shape `canonicalize` expects.
fn parse_nominal(s: &str) -> Proc {
    let toks = tokenize(s);
    let mut p = Parser::new(&toks, true);
    let out = p.proc();
    assert_eq!(p.pos, toks.len(), "trailing tokens in `{s}`");
    out
}

/// Parse one S-expression **literally** — `(V k)` ⇒ `Var(k)`, `Input.bound = 0` —
/// i.e. exactly the oracle's already-canonical de-Bruijn output.
fn parse_literal(s: &str) -> Proc {
    let toks = tokenize(s);
    let mut p = Parser::new(&toks, false);
    let out = p.proc();
    assert_eq!(p.pos, toks.len(), "trailing tokens in `{s}`");
    out
}

// ---------------------------------------------------------------------------
// Order-of-parallel-components–insensitive normalization (see module doc).
// ---------------------------------------------------------------------------

fn flatten(p: &Proc, out: &mut Vec<Proc>) {
    match p {
        Proc::Zero => {}
        Proc::Par(ps) => ps.iter().for_each(|q| flatten(q, out)),
        other => out.push(other.clone()),
    }
}

/// Canonicalize the `Par` *shape* (flatten units/nesting, sort components by
/// Rust `Ord`) recursively, and force `Input.bound = 0`, so two canonical forms
/// that differ only by the choice of order representative compare equal.
fn normalize(p: &Proc) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => Proc::Drop(normalize_name(n)),
        Proc::Lift { chan, arg } => Proc::Lift {
            chan: normalize_name(chan),
            arg: Box::new(normalize(arg)),
        },
        Proc::Input { chan, body, .. } => Proc::Input {
            chan: normalize_name(chan),
            bound: 0,
            body: Box::new(normalize(body)),
        },
        Proc::Par(_) => {
            let mut comps = Vec::new();
            flatten(p, &mut comps);
            let mut comps: Vec<Proc> = comps.iter().map(normalize).collect();
            comps.sort();
            match comps.len() {
                0 => Proc::Zero,
                1 => comps.pop().unwrap(),
                _ => Proc::Par(comps),
            }
        }
    }
}

fn normalize_name(n: &Name) -> Name {
    match n {
        Name::Var(k) => Name::Var(*k),
        Name::Quote(p) => Name::Quote(Box::new(normalize(p))),
    }
}

/// A canonical, order-insensitive key for a *set* of processes.
fn norm_set(mut ps: Vec<Proc>) -> Vec<Proc> {
    ps = ps.iter().map(normalize).collect();
    ps.sort();
    ps.dedup();
    ps
}

// ---------------------------------------------------------------------------
// The differential.
// ---------------------------------------------------------------------------

#[test]
fn rust_engine_agrees_with_coq_proven_oracle() {
    let mut checked = 0usize;
    let mut redex_vectors = 0usize;

    for (lineno, raw) in CORPUS.lines().enumerate() {
        // Strip only a trailing CR (never trailing spaces: an empty step-set
        // record legitimately ends with the separator `" | "`).
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        if line.trim().is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.split(" | ").collect();
        assert_eq!(
            fields.len(),
            3,
            "corpus line {} malformed: `{line}`",
            lineno + 1
        );
        let term = parse_nominal(fields[0]);
        let oracle_canon = parse_literal(fields[1]);
        let oracle_steps: Vec<Proc> = fields[2]
            .split(";;")
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .map(parse_literal)
            .collect();

        // --- canon: Rust canonicalize vs proven `canon`. ---
        let rust_canon = canonicalize(&term);
        assert_eq!(
            normalize(&rust_canon),
            normalize(&oracle_canon),
            "canon mismatch on corpus line {} (`{}`)\n rust   = {:?}\n oracle = {:?}",
            lineno + 1,
            fields[0],
            rust_canon,
            oracle_canon,
        );

        // --- step: Rust step-set vs proven `step` set (both up to ≡). ---
        let rust_step_set = norm_set(step(&term).iter().map(canonicalize).collect());
        let oracle_step_set = norm_set(oracle_steps);
        assert_eq!(
            rust_step_set,
            oracle_step_set,
            "step-set mismatch on corpus line {} (`{}`)",
            lineno + 1,
            fields[0],
        );

        if !oracle_step_set.is_empty() {
            redex_vectors += 1;
        }
        checked += 1;
    }

    // Guard against an empty/short corpus silently passing.
    assert!(
        checked >= 30,
        "expected a substantial corpus, only checked {checked}"
    );
    assert!(
        redex_vectors >= 5,
        "expected several reducible vectors, only {redex_vectors}"
    );
    eprintln!(
        "oracle differential: {checked} vectors agree ({redex_vectors} with non-empty step-set)"
    );
}
