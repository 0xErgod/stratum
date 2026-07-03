(** * Extract.v — the verified oracle: extraction + corpus generation

    This file closes the differential loop of issue #16.  It is a MANUAL artifact
    (NOT on the CI path — CI compiles only `Rho.v`); it [Require]s the proven
    development and does two things:

    1. [Extraction] of the machine-checked [canon] (structural-congruence
       decision, Tier-1) and [step] (one-step Comm reducer, Tier-2) — together
       with the [Proc]/[Name] term types and the [pleb] order — to OCaml
       (`oracle.ml`).  These functions are exactly the trustworthy engine: their
       correctness is [Qed] in `Rho.v` and rests on ZERO axioms (see
       `Print Assumptions canon_decides` / `step_sound`).  The extracted OCaml IS
       the "proven oracle".

    2. Since this machine's OCaml toolchain could not be run (the Rocq-platform
       `ocamlfind` points at a missing prefix; no `ocamlc`/`ocamlopt`), the
       differential CORPUS is produced instead by the Coq KERNEL itself:
       [vm_compute] of the very same verified [canon]/[step] on a fixed list of
       closed, de-Bruijn-explicit ρ-terms, serialized to a stable S-expression
       text format.  Kernel computation of a [Qed]-verified function is equally a
       "proven-oracle" output — the trust chain is identical, only the evaluator
       differs (Coq kernel vs extracted OCaml).

    Regenerate the corpus (from this directory, with the proofs compiled):

        rocq compile -Q . Stratum Rho.v
        rocq compile -Q . Stratum Extract.v      (* writes corpus_raw.out + oracle.ml *)

    then strip the Coq print wrapper into the committed corpus (see the
    Makefile-free one-liner in `README.md`). *)

From Stdlib Require Import String List Extraction.
From Stdlib Require Ascii.
From Stratum Require Import Rho.
Import ListNotations.
Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** OCaml extraction of the verified oracle                          *)
(* ------------------------------------------------------------------ *)

Extraction Language OCaml.
(** Extract [canon], [canon_name] (the ≡ / ≡N decision) and [step] (the Comm
    reducer), pulling in [Proc], [Name], [pleb] and all their proven support
    (norm_par/sort_par, subst_sem, redexes, ...) automatically. *)
Extraction "oracle.ml" canon canon_name step pleb.

(* ------------------------------------------------------------------ *)
(** ** A stable S-expression serializer (for the corpus)               *)
(* ------------------------------------------------------------------ *)

Definition nat_to_digit (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

Fixpoint nat_to_string (fuel n : nat) : string :=
  match fuel with
  | 0 => "0"
  | S f =>
      if Nat.ltb n 10 then nat_to_digit n
      else nat_to_string f (Nat.div n 10) ++ nat_to_digit (Nat.modulo n 10)
  end.

Definition nts (n : nat) : string := nat_to_string (S n) n.

(** Prefix S-expressions:
      Proc ::= Z | (I name proc) | (L name proc) | (D name) | (P proc proc)
      Name ::= (V nat) | (Q proc)                                            *)
Fixpoint ser_proc (p : Proc) : string :=
  match p with
  | zero     => "Z"
  | inp c b  => "(I " ++ ser_name c ++ " " ++ ser_proc b ++ ")"
  | lift c a => "(L " ++ ser_name c ++ " " ++ ser_proc a ++ ")"
  | drop x   => "(D " ++ ser_name x ++ ")"
  | par a b  => "(P " ++ ser_proc a ++ " " ++ ser_proc b ++ ")"
  end
with ser_name (x : Name) : string :=
  match x with
  | var n   => "(V " ++ nts n ++ ")"
  | quote p => "(Q " ++ ser_proc p ++ ")"
  end.

Fixpoint ser_list (l : list Proc) : string :=
  match l with
  | []      => ""
  | [x]     => ser_proc x
  | x :: xs => ser_proc x ++ " ;; " ++ ser_list xs
  end.

(* ------------------------------------------------------------------ *)
(** ** The verified-oracle outputs for a term                          *)
(* ------------------------------------------------------------------ *)

(** Deduplicate a list of (canonical) processes up to syntactic equality using
    the verified [proc_beq] (which reflects Leibniz equality, [beq_correct]). *)
Fixpoint dedup (l : list Proc) : list Proc :=
  match l with
  | []      => []
  | x :: xs => if existsb (proc_beq x) xs then dedup xs else x :: dedup xs
  end.

(** The Comm-reduct SET up to ≡: canonicalize every [step] reduct, dedup, and
    sort into a deterministic order (via the verified [sort_par]). *)
Definition step_canon_set (p : Proc) : list Proc :=
  sort_par (dedup (map canon (step p))).

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

(** One corpus record: [ term | canon term | step-set ], one per line. *)
Definition render (p : Proc) : string :=
  ser_proc p ++ " | " ++ ser_proc (canon p) ++ " | " ++ ser_list (step_canon_set p).

Fixpoint render_all (l : list Proc) : string :=
  match l with
  | []      => ""
  | [x]     => render x
  | x :: xs => render x ++ nl ++ render_all xs
  end.

(* ------------------------------------------------------------------ *)
(** ** The corpus: closed, de-Bruijn-explicit ρ-terms                  *)
(* ------------------------------------------------------------------ *)

(** Every term is CLOSED (each [var k] refers to an enclosing [inp]) and lives in
    the fragment the Coq model and the Rust engine share directly — so the
    differential compares the ENGINE (canon/step) and not the unmodelled
    nominal→de-Bruijn conversion (see the α/de-Bruijn caveat in `README.md`).
    Channels are quotes (closed); [var] appears only bound by an [inp]. *)
Definition q0 : Name := quote zero.
Definition qd0 : Name := quote (drop (quote zero)).   (* ⌜*⌜0⌝⌝ ≡N ⌜0⌝ *)

Definition corpus : list Proc :=
  [ (* --- structural congruence: monoid laws, flatten, sort --- *)
    zero
  ; drop q0
  ; lift q0 zero
  ; par zero zero
  ; par (drop q0) zero
  ; par zero (drop q0)
  ; par (drop q0) (drop q0)
  ; par (lift q0 zero) (drop q0)
  ; par (par (drop q0) zero) (lift q0 zero)
  ; par (par (lift q0 zero) (drop q0)) (par zero (drop q0))
  ; par (drop (quote (par zero zero))) zero
  ; lift q0 (par zero (par zero (drop q0)))
  ; par (drop q0) (par (lift q0 zero) (par zero (drop (quote (lift q0 zero)))))
    (* --- name equivalence ≡N: quote-drop and struct-equiv --- *)
  ; drop (quote (drop (quote zero)))            (* *⌜*⌜0⌝⌝  ≡  *⌜0⌝ *)
  ; drop qd0
  ; lift qd0 zero
  ; drop (quote (drop (quote (drop (quote zero)))))
  ; drop (quote (par (drop q0) zero))           (* quote of (drop q0 | 0), collapses via quote-drop *)
    (* --- binders and de-Bruijn indices (no redex) --- *)
  ; inp q0 (drop (var 0))
  ; inp q0 zero
  ; inp q0 (inp q0 (par (drop (var 0)) (drop (var 1))))
  ; inp q0 (inp (var 0) (drop (var 1)))         (* inner channel = outer binder *)
  ; inp q0 (par (drop (var 0)) (lift q0 zero))
    (* --- Comm redexes: step is non-empty --- *)
  ; par (lift q0 zero) (inp q0 (drop (var 0)))              (* -> 0 *)
  ; par (lift q0 zero) (inp q0 zero)                        (* -> 0 *)
  ; par (lift q0 (lift q0 zero)) (inp q0 (drop (var 0)))    (* -> ⌜0⌝!(0) *)
  ; par (lift qd0 zero) (inp q0 (drop (var 0)))             (* ≡N channel match -> 0 *)
  ; par (lift q0 (drop q0)) (inp q0 (drop (var 0)))         (* runs *⌜0⌝ -> 0 *)
  ; par (inp q0 (drop (var 0))) (lift q0 zero)              (* order swapped *)
    (* --- multiple / composite redexes --- *)
  ; par (par (lift q0 zero) (inp q0 zero)) (par (lift q0 zero) (inp q0 zero))
  ; par (lift q0 zero) (par (inp q0 (drop (var 0))) (inp q0 zero))
  ; par (par (lift q0 zero) (drop q0)) (inp q0 (drop (var 0)))
  ; par (lift q0 zero) (par (inp q0 (drop (var 0))) (lift q0 zero))
  ].

(* ------------------------------------------------------------------ *)
(** ** Emit the corpus (kernel-computed, verified oracle)              *)
(* ------------------------------------------------------------------ *)

Set Printing Width 100000000.
Redirect "corpus_raw" Compute (render_all corpus).
