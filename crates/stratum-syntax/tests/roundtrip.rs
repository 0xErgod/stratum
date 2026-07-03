//! Property test: rendering a closed term to surface syntax with the public
//! [`stratum_syntax::to_source`] and parsing it back yields a structurally
//! congruent term.
//!
//! The renderer (formerly a test-only pretty-printer, now promoted into the
//! crate as [`stratum_syntax::to_source`]) assigns fresh identifiers `v0, v1, …`
//! to input binders and resolves bound-name occurrences against them. The
//! generator produces only *closed* terms — every [`stratum_core::Name::Var`]
//! refers to an enclosing input — which is the class the surface syntax can
//! express.

use proptest::prelude::*;
use stratum_core::fresh_sym;
use stratum_core::structurally_congruent;
use stratum_core::term::{Name, Proc};
use stratum_syntax::{parse, to_source};

// --- generator of closed terms --------------------------------------------

fn name_strat(depth: u32, scope: Vec<u64>) -> BoxedStrategy<Name> {
    let quote = proc_strat(depth, scope.clone()).prop_map(|p| Name::Quote(Box::new(p)));
    if scope.is_empty() {
        quote.boxed()
    } else {
        let vars = scope;
        prop_oneof![
            2 => quote,
            3 => (0..vars.len()).prop_map(move |i| Name::Var(vars[i])),
        ]
        .boxed()
    }
}

fn proc_strat(depth: u32, scope: Vec<u64>) -> BoxedStrategy<Proc> {
    if depth == 0 {
        if scope.is_empty() {
            return Just(Proc::Zero).boxed();
        }
        let vars = scope;
        return prop_oneof![
            Just(Proc::Zero),
            (0..vars.len()).prop_map(move |i| Proc::Drop(Name::Var(vars[i]))),
        ]
        .boxed();
    }
    let d = depth - 1;
    let zero = Just(Proc::Zero).boxed();
    let drop_p = name_strat(d, scope.clone()).prop_map(Proc::Drop).boxed();
    let lift = (name_strat(d, scope.clone()), proc_strat(d, scope.clone()))
        .prop_map(|(chan, arg)| Proc::Lift {
            chan,
            arg: Box::new(arg),
        })
        .boxed();
    // Allocate the binder symbol once for this strategy node.
    let sym = fresh_sym();
    let mut inner = scope.clone();
    inner.push(sym);
    let input = (name_strat(d, scope.clone()), proc_strat(d, inner))
        .prop_map(move |(chan, body)| Proc::Input {
            chan,
            bound: sym,
            body: Box::new(body),
        })
        .boxed();
    let par = proptest::collection::vec(proc_strat(d, scope), 2..=3)
        .prop_map(Proc::Par)
        .boxed();
    prop_oneof![zero, drop_p, lift, input, par].boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn print_then_parse_is_congruent(p in proc_strat(3, vec![])) {
        let src = to_source(&p);
        let reparsed = parse(&src)
            .unwrap_or_else(|e| panic!("printed `{src}` but re-parse failed: {e}"));
        prop_assert!(
            structurally_congruent(&reparsed, &p),
            "src=`{src}`\n  orig={p:?}\n  back={reparsed:?}",
        );
    }
}
