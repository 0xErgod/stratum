//! End-to-end demo of the `stratum-types` grain: give the handshake's channels a
//! sorting, type-check the protocol, and watch an ill-sorted variant get
//! rejected with a clear error.
//!
//! The discipline is *channel-sort / behavioral* typing: a channel's type says
//! what shape of message it carries, and — because names are quoted processes —
//! a payload `⌜Q⌝`'s type is the spatial type of the process `Q` it quotes.
//!
//! Run with: `cargo run -p stratum --example typed_handshake`

use stratum::core::term::{drop_, lift, quote, zero};
use stratum::core::{par, Name, Proc};
use stratum::syntax::parse;
use stratum::types::{check, Env, Ty};

/// The handshake, in the surface syntax: `new` mints req = @0, ack = @(@0!(0)).
const SOURCE: &str = "\
new req, ack

req!(0) | req(x).ack!(0)
";

/// req = ⌜0⌝ — the request channel minted first by `new`.
fn req() -> Name {
    quote(zero())
}

/// ack = ⌜ @0!(0) ⌝ — the acknowledge channel minted second by `new`.
fn ack() -> Name {
    quote(lift(quote(zero()), zero()))
}

/// The sorting: both channels carry the empty message `Nil`.
fn env() -> Env {
    Env::new().with(req(), Ty::Nil).with(ack(), Ty::Nil)
}

fn main() {
    // 1. Parse the surface syntax into a core process and type-check it.
    let protocol: Proc = parse(SOURCE).expect("handshake.strat should parse");
    println!("== protocol ==");
    println!("  {SOURCE}");
    println!("== sorting ==");
    println!("  req : channel carrying Nil");
    println!("  ack : channel carrying Nil\n");

    match check(&env(), &protocol) {
        Ok(()) => println!("well-typed: every send matches its channel's carried type\n"),
        Err(e) => println!("UNEXPECTED type error: {e}\n"),
    }

    // 2. An ill-typed variant: send a *channel-shaped* message on `req`, which
    //    only carries Nil. `req!( ack!(0) )` puts a `Chan(Nil)` on the wire.
    //    (`ack!(0)` desugars to a lift, whose spatial type is `Chan(Nil)`.)
    let ill = par([
        lift(req(), lift(ack(), zero())), // req!( ack!(0) )
        // req(x).0
        stratum::core::term::input(req(), |_x| zero()),
    ]);
    println!("== ill-typed variant: req!( ack!(0) ) | req(x).0 ==");
    match check(&env(), &ill) {
        Ok(()) => println!("  UNEXPECTED: accepted an ill-sorted protocol"),
        Err(e) => println!("  rejected, as intended: {e}"),
    }

    // 3. The reflective view: a name's type is the type of the process it quotes.
    println!("\n== reflective name typing (names are quoted processes) ==");
    let samples: [(&str, Name); 3] = [
        ("@0", quote(zero())),
        ("@(*@0)", quote(drop_(quote(zero())))),
        ("@(@0!(0))", ack()),
    ];
    for (shown, n) in samples {
        let t = stratum::types::msg_type(&env(), &n).expect("closed name");
        println!("  {shown:<10} : {t}");
    }
}
