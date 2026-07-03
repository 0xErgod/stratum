//! End-to-end demo: write a protocol in the Stratum surface syntax, parse it,
//! build its trace LTS, and check temporal properties — the whole pipeline from
//! a `.strat` source file.
//!
//! Run with: `cargo run -p stratum --example handshake`

use stratum::core::{lift, quote, zero, Name, Proc};
use stratum::logic::examples::emits;
use stratum::logic::{af, ag, counterexample, ef, holds, neg, prop, witness};
use stratum::lts::{format_proc, Lts};
use stratum::syntax::{expand, parse};

/// The protocol, written in the `.strat` surface syntax (see `handshake.strat`).
const SOURCE: &str = include_str!("handshake.strat");

/// The acknowledge channel `ack = @(@0!(0))`, referenced by the property below.
fn ack() -> Name {
    quote(lift(quote(zero()), zero()))
}

fn main() {
    // 1. Parse the surface syntax into a core process.
    let protocol: Proc = parse(SOURCE).expect("handshake.strat should parse");
    println!("== protocol ==\n{}\n", format_proc(&protocol));

    // 1a. `expand` — the transparency view: the named channels desugared to the
    // raw quoted-process names the calculus actually works with.
    println!(
        "== expanded (raw core) ==\n{}\n",
        expand(SOURCE).expect("expand")
    );

    // 2. Build the trace LTS (bounded exploration of all runs).
    let lts = Lts::explore(&protocol, 1000);
    println!(
        "== trace LTS ==\n{} states, {} transitions (truncated: {})\n",
        lts.num_states(),
        lts.num_transitions(),
        lts.is_truncated(),
    );
    for i in 0..lts.num_states() {
        let mark = if lts.is_terminal(i) { " [terminal]" } else { "" };
        println!("  s{i}: {}{mark}", format_proc(lts.state(i)));
    }
    println!();

    // 3. Define the atomic proposition "acked": a pending output on `ack`.
    let ack_chan = ack();
    let label = move |p: &str, s: &Proc| match p {
        "acked" => emits(s, &ack_chan),
        _ => false,
    };

    // 4. Check temporal properties of the protocol.
    println!("== properties ==");
    println!(
        "  EF acked   (the request can be acknowledged)      : {}",
        holds(&lts, &ef(prop("acked")), &label)
    );
    println!(
        "  AF acked   (every run eventually acknowledges)    : {}",
        holds(&lts, &af(prop("acked")), &label)
    );
    println!(
        "  AG ~acked  (it is never acknowledged) [expect: false] : {}",
        holds(&lts, &ag(neg(prop("acked"))), &label)
    );

    // 5. Extract a witness run reaching the acknowledgement.
    if let Some(run) = witness(&lts, &prop("acked"), &label) {
        let path: Vec<usize> = run.iter().map(|(_, s)| *s).collect();
        println!(
            "\n  witness to `acked`: {} step(s), s0 -> {:?}",
            run.len(),
            path
        );
    }

    // 6. And a counterexample to the (false) safety invariant "never acked".
    if let Some(cex) = counterexample(&lts, &neg(prop("acked")), &label) {
        let (_, bad) = cex.last().unwrap();
        println!(
            "  counterexample to `AG ~acked`: reaches s{bad} in {} step(s)",
            cex.len()
        );
    }
}
