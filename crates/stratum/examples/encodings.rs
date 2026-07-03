//! The encodings standard library, demonstrated end to end: expand the §3
//! replication macro to its raw machinery, watch it accumulate copies, and
//! confirm it is invisible off its internal channel.
//!
//! Run with: `cargo run -p stratum --example encodings`

use stratum::core::{name_equiv, quote, zero, Name, Proc};
use stratum::encodings::{with_stdlib, BANG, CONTRACT};
use stratum::equiv::weak_barbed_bisimilar;
use stratum::lts::{format_name, format_proc, Lts};
use stratum::syntax::{expand, parse};

fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Par(ps) => ps.iter().collect(),
        Proc::Zero => Vec::new(),
        other => vec![other],
    }
}

fn count_lifts_on(p: &Proc, chan: &Name) -> usize {
    components(p)
        .iter()
        .filter(|c| matches!(c, Proc::Lift { chan: ch, .. } if name_equiv(ch, chan)))
        .count()
}

fn internal_channel(p: &Proc) -> Name {
    for c in components(p) {
        if let Proc::Lift { chan, .. } = c {
            return chan.clone();
        }
    }
    unreachable!("bang(...) has a top-level lift");
}

fn main() {
    // 0. The shipped macros — inspectable source.
    println!("== the encodings ==");
    println!("  BANG     = {BANG}");
    println!("  CONTRACT = {CONTRACT}\n");

    // 1. Transparency: expand `bang(0)` to the raw §3 term.
    println!("== expand(bang(0)) — the raw §3 replication machinery ==");
    println!("{}\n", expand(&with_stdlib("bang(0)")).expect("expand"));

    // 2. Replication really replicates: `bang(s!(0))` accumulates copies of the
    //    inert output `s!(0)`, one per internal step. `s = @0` is observable.
    let bang_s = parse(&with_stdlib("new s\nbang( s!(0) )")).unwrap();
    let s = quote(zero());
    let lts = Lts::explore(&bang_s, 6);
    println!("== bang(s!(0)) accumulates copies (s = @0) ==");
    for i in 0..lts.num_states() {
        println!(
            "  s{i}: {} copies of s!(0)",
            count_lifts_on(lts.state(i), &s)
        );
    }
    println!(
        "  (truncated: {} — replication is unbounded)\n",
        lts.is_truncated()
    );

    // 3. Operational correspondence: `bang(0)` is `0` up to the internal channel.
    let b0 = parse(&with_stdlib("bang(0)")).unwrap();
    let nil = parse("0").unwrap();
    let x = internal_channel(&b0);
    println!("== bang(0) vs 0 — correspondence modulo the internal channel ==");
    println!("  bang(0) desugars to: {}", format_proc(&b0));
    println!("  internal channel x = {}", format_name(&x));
    println!(
        "  bang(0) ≈N 0  with N = {{}}          : {:?}",
        weak_barbed_bisimilar(&b0, &nil, &[], 50)
    );
    println!(
        "  bang(0) ≈N 0  with N = {{x}} [expect: distinguished] : {:?}",
        weak_barbed_bisimilar(&b0, &nil, std::slice::from_ref(&x), 50)
    );
}
