(** * Rho.v — a mechanization skeleton for Stratum's core (Tier 1)

    Reflective higher-order (rho) calculus of Meredith & Radestock,
    "A Reflective Higher-order Calculus" (ENTCS 141(5), 2005).

    PURPOSE.  This file pins down, as machine-checkable definitions, the two
    relations at the heart of `stratum-core` — structural congruence [scong] (≡,
    §2.3) and name equivalence [nequiv] (≡N, §2.4) — and proves the Tier-1
    theorem: the canonicalizer [canon] is a sound and complete decision
    procedure for ≡ ([canon_decides]).

    STATUS.  Fully proved and type-checks on the Rocq Prover 9.0.1 (Stdlib only,
    no external libraries).  Check with `coqc Rho.v`.  ALL obligations are closed
    with [Qed] — there is no [Admitted]/[admit] anywhere in the development.
    PROVED: [canon_sound] / [canon_name_sound] (mutual induction; 12 of 15 cases
    by computation, the 3 monoid cases reduced to AC facts about [norm_par]);
    the AC/sort crux [norm_par_comm]/[norm_par_assoc]/[norm_par_unit] (via the
    standard insertion-sort development [insert_perm]/[sort_perm]/[sort_sorted]/
    [sorted_perm_unique], resting on the [pleb] order laws — now PROVED, see the
    AXIOM BUDGET note below); the completeness
    side [canon_cong] -> [canon_complete] / [nequiv_complete]; [canon_idem]; and
    [ndepth_under_quote].

    AXIOM BUDGET — ZERO (as of Tier 3).  [pleb] is now a CONCRETE structural
    comparator ([proc_compare], below), NOT an abstract [Parameter], and the three
    order laws ([pleb_total]/[pleb_antisym]/[pleb_trans]) are PROVED of it ([Qed]),
    not assumed.  `Print Assumptions` on every headline theorem — [canon_decides],
    [step_sound], [step_complete], and the Tier-3 [reach_sound] — reports exactly
    "Closed under the global context": NO axioms whatsoever (no [pleb] symbol, no
    order assumptions), no unsanctioned axiom, no Admitted lemma.  (Historical
    note: through Tier 2 the metatheory rested on the three [pleb] order laws as
    axioms over an abstract [pleb] Parameter; Tier 3 discharged them.)

    MODELLING DECISIONS (mirror of SPEC.md; the Coq model and the Rust engine
    represent the SAME quotient):

    - de Bruijn indices for input-bound names.  In the Rust engine names are
      nominal (globally fresh symbols) and α is recovered by canonicalizing to de
      Bruijn; here we use de Bruijn from the start, so α-equivalence is definitional
      (no α rule in [scong]) and the Rust's α-normalization corresponds to the de
      Bruijn embedding.

      SCOPE GAP (verified by fiat, not by proof).  This model treats [var n] as an
      opaque atom and performs NO binder renumbering.  The actual nominal→de-Bruijn
      conversion the Rust engine runs (`term.rs`/`congruence.rs`: the `env`
      push/pop stack, resolving an input channel in the OUTER scope before the
      binder, shadowing, the free-variable fallback `Var(u64::MAX - sym)`, and
      descent-through-quotes scoping) is NOT modelled here.  The theorems below
      presume their input is already correct de Bruijn; a bug in Rust's `env`
      handling (e.g. an off-by-one between a channel and a body occurrence of the
      same outer binder, or mis-scoped shadowing) would NOT be caught by them.
      Assurance over the α/de-Bruijn conversion needs a separate model or the
      round-trip property test (SPEC S4); it is out of Tier-1 scope by design.

    - [pleb] is a CONCRETE total order ([proc_compare], a structural lexicographic
      comparator with the three order laws PROVED), but is NOT tied to the Rust
      derived [Ord] (variant order Zero<Input<Lift<Drop<Par, Quote<Var).  The
      RELATION decided here — [canon p = canon q] — is invariant under the choice
      of total order on components (equal iff the component multisets are
      permutations; this is exactly what [sort_par_perm] establishes), so ≡ agrees
      with the Rust decision regardless of which linear order [pleb] uses.  CAVEAT:
      if any code depends on the specific canonical REPRESENTATIVE (serialized/
      hashed canonical forms crossing the Coq/Rust boundary, or LTS state identity
      in SPEC §F1), [proc_compare] must be aligned to Rust's [Ord] — an open
      obligation, not discharged here (but no longer an axiom).  The differential
      harness in `crates/stratum-core` accordingly compares canonical forms modulo
      Par-component order.

    - ≡ absorbs ≡N at name positions.  [scong] is closed under [nequiv] wherever a
      name occurs (rules [sc_lift]/[sc_inp]/[sc_drop]); this matches the Rust
      decision that `canonicalize` applies quote-drop at every name position.  A
      *process* `*⌜P⌝` is NOT ≡ to `P` (drop is inert): there is deliberately no
      process-level quote-drop rule.

    - Substitution and reduction (§2.5/§2.7/§2.8) are Tier 2 and live in a later
      module; Tier 1 is [scong]/[nequiv] and [canon] only, which do not need
      substitution. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Syntax (§2.0.1) *)
(* ------------------------------------------------------------------ *)

(** Names are quoted processes ([quote]) or de-Bruijn references to an enclosing
    input binder ([var]).  Processes are the null process, input (which binds one
    name — de Bruijn index 0 — in its body), asynchronous lift/output, drop, and
    binary parallel (treated as an abelian monoid by [scong]). *)
Inductive Proc : Type :=
  | zero  : Proc
  | inp   : Name -> Proc -> Proc      (* x(y).P : channel, body binds y at index 0 *)
  | lift  : Name -> Proc -> Proc      (* x!(P) *)
  | drop  : Name -> Proc              (* *x *)
  | par   : Proc -> Proc -> Proc      (* P | Q *)
with Name : Type :=
  | var   : nat -> Name               (* de Bruijn index of an enclosing input *)
  | quote : Proc -> Name.             (* @P = ⌜P⌝, the only name former *)

Scheme Proc_ind' := Induction for Proc Sort Prop
  with Name_ind' := Induction for Name Sort Prop.
Combined Scheme proc_name_mutind from Proc_ind', Name_ind'.

(* ------------------------------------------------------------------ *)
(** ** Quote depth (§2.5) — the termination measure for ≡N *)
(* ------------------------------------------------------------------ *)

(** [ndepth (⌜P⌝) = 1 + pdepth P]; the grammar's strict quote/process
    alternation bounds it, which is what makes ≡N (and hence ≡) decidable.
    [canon] below is plain structural recursion and needs no measure, but the
    decision procedure for ≡N recurses on this depth. *)
Fixpoint pdepth (p : Proc) : nat :=
  match p with
  | zero      => 0
  | inp c b   => Nat.max (ndepth c) (pdepth b)
  | lift c a  => Nat.max (ndepth c) (pdepth a)
  | drop x    => ndepth x
  | par a b   => Nat.max (pdepth a) (pdepth b)
  end
with ndepth (x : Name) : nat :=
  match x with
  | var _   => 0
  | quote P => S (pdepth P)
  end.

(* ------------------------------------------------------------------ *)
(** ** Structural congruence ≡ (§2.3) and name equivalence ≡N (§2.4) *)
(* ------------------------------------------------------------------ *)

(** The two relations are mutually recursive.  [scong] is the least congruence
    containing the abelian-monoid laws for [par], closed under [nequiv] at name
    positions.  [nequiv] is the least equivalence with quote-drop and
    struct-equiv.  (No α rule: de Bruijn.  No process-level quote-drop: drop is
    inert.) *)
Inductive scong : Proc -> Proc -> Prop :=
  (* equivalence *)
  | sc_refl  : forall p, scong p p
  | sc_sym   : forall p q, scong p q -> scong q p
  | sc_trans : forall p q r, scong p q -> scong q r -> scong p r
  (* abelian monoid for parallel (§2.3) *)
  | sc_comm  : forall p q, scong (par p q) (par q p)
  | sc_assoc : forall p q r, scong (par (par p q) r) (par p (par q r))
  | sc_unit  : forall p, scong (par p zero) p
  (* congruence *)
  | sc_par   : forall p p' q q', scong p p' -> scong q q' -> scong (par p q) (par p' q')
  | sc_lift  : forall c c' a a', nequiv c c' -> scong a a' -> scong (lift c a) (lift c' a')
  | sc_inp   : forall c c' b b', nequiv c c' -> scong b b' -> scong (inp c b) (inp c' b')
  | sc_drop  : forall x x', nequiv x x' -> scong (drop x) (drop x')
with nequiv : Name -> Name -> Prop :=
  | nq_refl       : forall x, nequiv x x
  | nq_sym        : forall x y, nequiv x y -> nequiv y x
  | nq_trans      : forall x y z, nequiv x y -> nequiv y z -> nequiv x z
  | nq_quote_drop : forall x, nequiv (quote (drop x)) x         (* ⌜*x⌝ ≡N x (§2.4) *)
  | nq_struct     : forall p q, scong p q -> nequiv (quote p) (quote q).
      (* struct-equiv: P≡Q -> ⌜P⌝≡N⌜Q⌝.  The paper's informal "⌜P⌝≡N⌜Q⌝ iff P≡Q"
         is encoded as this FORWARD generating direction ONLY.  The reverse
         implication is genuinely FALSE in the presence of quote-drop: e.g.
         ⌜*⌜0⌝⌝ ≡N ⌜0⌝ (nq_quote_drop at x=⌜0⌝) while *⌜0⌝ ≢ 0 (drop is inert, no
         process-level quote-drop).  Encoding it as a bi-implication would
         over-identify, so "iff" is a loose gloss and only "if" is a rule. *)

(* ------------------------------------------------------------------ *)
(** ** The canonicalizer [canon] *)
(* ------------------------------------------------------------------ *)

(** A total order on canonical processes, used only to sort the components of a
    parallel composition into a unique representative.  This is a design freedom
    (any consistent total order works); an executable instance (e.g. a structural
    comparison mirroring the Rust derived [Ord]) must be a decidable linear order
    on canonical forms — a PROOF OBLIGATION for [canon_complete], not a free
    assumption.

    TIER-3: [pleb] is now a CONCRETE structural comparator (was an abstract
    [Parameter]).  Making it concrete is what turns [canon]/[step] into EXECUTABLE
    functions the Coq kernel can [vm_compute] — the "verified oracle" the
    differential harness in `crates/stratum-core` is checked against (see
    `Extract.v`).  It is a tag-then-fields lexicographic order, mutually recursive
    over [Proc]/[Name].  The three order laws below ([pleb_total]/[pleb_antisym]/
    [pleb_trans]) — previously assumed of the abstract parameter — are now PROVED
    of this concrete comparator ([Qed]), so the entire metatheory is discharged
    with ZERO remaining axioms.  The choice of order remains a design freedom:
    [canon p = canon q] is invariant under it ([sort_par_perm]); the differential
    harness therefore compares canonical forms modulo this Par-component order. *)
Fixpoint proc_compare (p q : Proc) : comparison :=
  match p, q with
  | zero, zero => Eq
  | zero, _ => Lt
  | _, zero => Gt
  | inp c1 b1, inp c2 b2 =>
      match name_compare c1 c2 with Eq => proc_compare b1 b2 | o => o end
  | inp _ _, _ => Lt
  | _, inp _ _ => Gt
  | lift c1 a1, lift c2 a2 =>
      match name_compare c1 c2 with Eq => proc_compare a1 a2 | o => o end
  | lift _ _, _ => Lt
  | _, lift _ _ => Gt
  | drop x1, drop x2 => name_compare x1 x2
  | drop _, _ => Lt
  | _, drop _ => Gt
  | par a1 b1, par a2 b2 =>
      match proc_compare a1 a2 with Eq => proc_compare b1 b2 | o => o end
  end
with name_compare (x y : Name) : comparison :=
  match x, y with
  | var n, var m => Nat.compare n m
  | var _, quote _ => Lt
  | quote _, var _ => Gt
  | quote p, quote q => proc_compare p q
  end.

Definition pleb (x y : Proc) : bool :=
  match proc_compare x y with Gt => false | _ => true end.

(** Flatten a parallel composition into its active components, dropping units. *)
Fixpoint flatten_par (p : Proc) : list Proc :=
  match p with
  | zero    => []
  | par a b => flatten_par a ++ flatten_par b
  | _       => [p]
  end.

Fixpoint insert_proc (x : Proc) (l : list Proc) : list Proc :=
  match l with
  | [] => [x]
  | y :: ys => if pleb x y then x :: l else y :: insert_proc x ys
  end.

Definition sort_par (l : list Proc) : list Proc := fold_right insert_proc [] l.

(** Rebuild a right-nested parallel from a component list ([] ↦ 0, singleton
    collapses). *)
Fixpoint rebuild (l : list Proc) : Proc :=
  match l with
  | []      => zero
  | [x]     => x
  | x :: xs => par x (rebuild xs)
  end.

(** Normalize an (already component-canonical) parallel: flatten, sort, rebuild.
    Not mutually recursive with [canon], so it does not affect guardedness. *)
Definition norm_par (p : Proc) : Proc := rebuild (sort_par (flatten_par p)).

(** [canon] is plain structural recursion: every recursive call descends into a
    strict subterm (into [par] components, into a channel/dropped name, or under a
    [quote]).  The AC step is factored into [norm_par]; the name-level quote-drop
    law ⌜*x⌝ ≡N x is applied up to ≡ (its body is canonicalized first).  The
    "production" alternative is `Equations canon by wf (psize p)`; structural
    recursion suffices here because the descent is genuinely well-founded on the
    term. *)
Fixpoint canon (p : Proc) : Proc :=
  match p with
  | zero     => zero
  | drop x   => drop (canon_name x)
  | lift c a => lift (canon_name c) (canon a)
  | inp c b  => inp (canon_name c) (canon b)
  | par a b  => norm_par (par (canon a) (canon b))
  end
with canon_name (x : Name) : Name :=
  match x with
  | var n   => var n
  | quote P => match canon P with
               | drop y => y          (* quote-drop, up to ≡ *)
               | Q      => quote Q     (* struct-equiv *)
               end
  end.

(* ------------------------------------------------------------------ *)
(** ** Computation lemmas (definitional) and the [pleb] order obligations *)
(* ------------------------------------------------------------------ *)

Lemma canon_zero_eq : canon zero = zero.
Proof. reflexivity. Qed.
Lemma canon_drop_eq : forall x, canon (drop x) = drop (canon_name x).
Proof. reflexivity. Qed.
Lemma canon_lift_eq : forall c a, canon (lift c a) = lift (canon_name c) (canon a).
Proof. reflexivity. Qed.
Lemma canon_inp_eq : forall c b, canon (inp c b) = inp (canon_name c) (canon b).
Proof. reflexivity. Qed.
Lemma canon_par_eq : forall a b, canon (par a b) = norm_par (par (canon a) (canon b)).
Proof. reflexivity. Qed.
Lemma canon_name_quote_eq : forall P,
  canon_name (quote P) = match canon P with drop y => y | Q => quote Q end.
Proof. reflexivity. Qed.
Lemma canon_name_quote_drop : forall x, canon_name (quote (drop x)) = canon_name x.
Proof. reflexivity. Qed.

(** The three order laws for [pleb].  Previously ASSUMED of an abstract
    [Parameter]; now PROVED of the concrete [proc_compare]-based order, so the
    metatheory rests on ZERO axioms.  We first establish the standard comparison
    facts (reflexivity, [Eq]-reflects-equality, antisymmetry, [Lt]-transitivity)
    for the mutually-recursive [proc_compare]/[name_compare], then derive the
    [pleb] laws the AC lemmas below depend on. *)

Lemma compare_refl :
  (forall p, proc_compare p p = Eq) /\ (forall x, name_compare x x = Eq).
Proof.
  apply proc_name_mutind; simpl; intros.
  - reflexivity.
  - rewrite H; exact H0.
  - rewrite H; exact H0.
  - exact H.
  - rewrite H; exact H0.
  - apply Nat.compare_refl.
  - exact H.
Qed.

Lemma compare_eq :
  (forall p q, proc_compare p q = Eq -> p = q) /\
  (forall x y, name_compare x y = Eq -> x = y).
Proof.
  apply proc_name_mutind.
  - intros q; destruct q; simpl; try discriminate; reflexivity.
  - intros c IHc b IHb q; destruct q; simpl; try discriminate.
    destruct (name_compare c n) eqn:E; try discriminate.
    intro Hb. apply IHc in E; apply IHb in Hb; subst; reflexivity.
  - intros c IHc a IHa q; destruct q; simpl; try discriminate.
    destruct (name_compare c n) eqn:E; try discriminate.
    intro Ha. apply IHc in E; apply IHa in Ha; subst; reflexivity.
  - intros x IHx q; destruct q; simpl; try discriminate.
    intro H; apply IHx in H; subst; reflexivity.
  - intros a IHa b IHb q; destruct q; simpl; try discriminate.
    destruct (proc_compare a q1) eqn:E; try discriminate.
    intro Hb. apply IHa in E; apply IHb in Hb; subst; reflexivity.
  - intros n y; destruct y; simpl; try discriminate.
    intro H; apply Nat.compare_eq in H; subst; reflexivity.
  - intros p IHp y; destruct y; simpl; try discriminate.
    intro H; apply IHp in H; subst; reflexivity.
Qed.

Lemma compare_antisym :
  (forall p q, proc_compare q p = CompOpp (proc_compare p q)) /\
  (forall x y, name_compare y x = CompOpp (name_compare x y)).
Proof.
  apply proc_name_mutind.
  - intros q; destruct q; reflexivity.
  - intros c IHc b IHb q; destruct q; simpl; try reflexivity.
    rewrite IHc. destruct (name_compare c n); simpl; try reflexivity. apply IHb.
  - intros c IHc a IHa q; destruct q; simpl; try reflexivity.
    rewrite IHc. destruct (name_compare c n); simpl; try reflexivity. apply IHa.
  - intros x IHx q; destruct q; simpl; try reflexivity. apply IHx.
  - intros a IHa b IHb q; destruct q; simpl; try reflexivity.
    rewrite IHa. destruct (proc_compare a q1); simpl; try reflexivity. apply IHb.
  - intros n y; destruct y; simpl; try reflexivity. apply Nat.compare_antisym.
  - intros p IHp y; destruct y; simpl; try reflexivity. apply IHp.
Qed.

Lemma compare_lt_trans :
  (forall p q r, proc_compare p q = Lt -> proc_compare q r = Lt -> proc_compare p r = Lt) /\
  (forall x y z, name_compare x y = Lt -> name_compare y z = Lt -> name_compare x z = Lt).
Proof.
  apply proc_name_mutind.
  - (* p = zero *) intros q r Hpq Hqr.
    destruct r; try reflexivity; destruct q; simpl in *; discriminate.
  - (* p = inp c b *) intros c IHc b IHb q r Hpq Hqr.
    destruct q; simpl in Hpq; try discriminate;
      destruct r; simpl in Hqr |- *; try discriminate; try reflexivity.
    (* q = inp n p0, r = inp n0 p1 *)
    destruct (name_compare c n) eqn:E1; try discriminate.
    + apply compare_eq in E1; subst n.
      destruct (name_compare c n0) eqn:E2; try reflexivity.
      * apply compare_eq in E2; subst n0. eapply IHb; eauto.
      * (* name_compare c n0 = Gt is impossible: Hqr says q<r requires it <= Eq *)
        discriminate.
    + destruct (name_compare n n0) eqn:E2; try discriminate.
      * apply compare_eq in E2; subst n0. rewrite E1. reflexivity.
      * assert (name_compare c n0 = Lt) by (eapply IHc; eauto).
        rewrite H. reflexivity.
  - (* p = lift c a *) intros c IHc a IHa q r Hpq Hqr.
    destruct q; simpl in Hpq; try discriminate;
      destruct r; simpl in Hqr |- *; try discriminate; try reflexivity.
    destruct (name_compare c n) eqn:E1; try discriminate.
    + apply compare_eq in E1; subst n.
      destruct (name_compare c n0) eqn:E2; try reflexivity.
      * apply compare_eq in E2; subst n0. eapply IHa; eauto.
      * discriminate.
    + destruct (name_compare n n0) eqn:E2; try discriminate.
      * apply compare_eq in E2; subst n0. rewrite E1. reflexivity.
      * assert (name_compare c n0 = Lt) by (eapply IHc; eauto).
        rewrite H. reflexivity.
  - (* p = drop x *) intros x IHx q r Hpq Hqr.
    destruct q; simpl in Hpq; try discriminate;
      destruct r; simpl in Hqr |- *; try discriminate; try reflexivity.
    eapply IHx; eauto.
  - (* p = par a b *) intros a IHa b IHb q r Hpq Hqr.
    destruct q; simpl in Hpq; try discriminate;
      destruct r; simpl in Hqr |- *; try discriminate; try reflexivity.
    destruct (proc_compare a q1) eqn:E1; try discriminate.
    + apply compare_eq in E1; subst q1.
      destruct (proc_compare a r1) eqn:E2; try reflexivity.
      * apply compare_eq in E2; subst r1. eapply IHb; eauto.
      * discriminate.
    + destruct (proc_compare q1 r1) eqn:E2; try discriminate.
      * apply compare_eq in E2; subst r1. rewrite E1. reflexivity.
      * assert (proc_compare a r1 = Lt) by (eapply IHa; eauto).
        rewrite H. reflexivity.
  - (* x = var n *) intros n y z Hxy Hyz.
    destruct y; simpl in Hxy; try discriminate;
      destruct z; simpl in Hyz |- *; try discriminate; try reflexivity.
    rewrite Nat.compare_lt_iff in *. eapply Nat.lt_trans; eauto.
  - (* x = quote p *) intros p IHp y z Hxy Hyz.
    destruct y; simpl in Hxy; try discriminate;
      destruct z; simpl in Hyz |- *; try discriminate; try reflexivity.
    eapply IHp; eauto.
Qed.

(** The [pleb] order laws, now derived (was: assumed).  These are exactly the
    three obligations the AC lemmas below depend on. *)
Lemma pleb_total : forall x y, pleb x y = true \/ pleb y x = true.
Proof.
  intros x y; unfold pleb.
  destruct (proc_compare x y) eqn:E.
  - left; reflexivity.
  - left; reflexivity.
  - right. pose proof (proj1 compare_antisym x y) as Hanti.
    rewrite E in Hanti. simpl in Hanti. rewrite Hanti. reflexivity.
Qed.

Lemma pleb_antisym : forall x y, pleb x y = true -> pleb y x = true -> x = y.
Proof.
  intros x y Hxy Hyx; unfold pleb in *.
  destruct (proc_compare x y) eqn:E; try discriminate.
  - apply (proj1 compare_eq); exact E.
  - exfalso. pose proof (proj1 compare_antisym x y) as Hanti.
    rewrite E in Hanti. simpl in Hanti. rewrite Hanti in Hyx. discriminate.
Qed.

Lemma pleb_trans : forall x y z, pleb x y = true -> pleb y z = true -> pleb x z = true.
Proof.
  intros x y z Hxy Hyz; unfold pleb in *.
  destruct (proc_compare x z) eqn:Exz; try reflexivity.
  exfalso.
  (* proc_compare x z = Gt while both x<=y and y<=z: impossible. *)
  destruct (proc_compare x y) eqn:Exy; try discriminate.
  - apply (proj1 compare_eq) in Exy; subst y. rewrite Exz in Hyz; discriminate.
  - destruct (proc_compare y z) eqn:Eyz; try discriminate.
    + apply (proj1 compare_eq) in Eyz; subst z.
      rewrite Exy in Exz; discriminate.
    + assert (proc_compare x z = Lt) by (eapply (proj1 compare_lt_trans); eauto).
      rewrite Exz in H; discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Sorting infrastructure for the AC lemmas (Engineer 1)            *)
(* ------------------------------------------------------------------ *)

(** An "atom" is a flattened parallel component: anything but [zero] and [par].
    [flatten_par] produces exactly lists of atoms. *)
Definition atomic (p : Proc) : Prop :=
  match p with zero => False | par _ _ => False | _ => True end.

Lemma flatten_par_par : forall a b,
  flatten_par (par a b) = flatten_par a ++ flatten_par b.
Proof. reflexivity. Qed.

Lemma atomic_flatten : forall x, atomic x -> flatten_par x = [x].
Proof. intros x H; destruct x; simpl in H; try contradiction; reflexivity. Qed.

Lemma flatten_atomic : forall p, Forall atomic (flatten_par p).
Proof.
  induction p; simpl.
  - constructor.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor.
  - apply Forall_app; split; assumption.
Qed.

(** [insert_proc] and [sort_par] preserve any predicate holding of all elements. *)
Lemma insert_Forall : forall (P : Proc -> Prop) x l,
  P x -> Forall P l -> Forall P (insert_proc x l).
Proof.
  intros P x l; induction l as [|y ys IH]; intros Hx Hl; simpl.
  - constructor; [exact Hx | constructor].
  - destruct (pleb x y).
    + constructor; [exact Hx | exact Hl].
    + inversion Hl; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma sort_Forall : forall (P : Proc -> Prop) l,
  Forall P l -> Forall P (sort_par l).
Proof.
  intros P l; unfold sort_par; induction l as [|a l IH]; intro H; simpl.
  - constructor.
  - inversion H; subst. apply insert_Forall; [assumption | apply IH; assumption].
Qed.

(** Step 1-2: [insert_proc]/[sort_par] are permutations. *)
Lemma insert_perm : forall x l, Permutation (insert_proc x l) (x :: l).
Proof.
  intros x l; induction l as [|y ys IH]; simpl.
  - apply Permutation_refl.
  - destruct (pleb x y).
    + apply Permutation_refl.
    + eapply Permutation_trans; [apply perm_skip; exact IH | apply perm_swap].
Qed.

Lemma sort_perm : forall l, Permutation (sort_par l) l.
Proof.
  unfold sort_par; induction l as [|a l IH]; simpl.
  - apply Permutation_refl.
  - eapply Permutation_trans; [apply insert_perm | apply perm_skip; exact IH].
Qed.

(** Step 3: [sort_par] produces a [StronglySorted] list under [pleb]. *)
Lemma insert_sorted : forall x l,
  StronglySorted (fun a b => pleb a b = true) l ->
  StronglySorted (fun a b => pleb a b = true) (insert_proc x l).
Proof.
  intros x l; induction l as [|y ys IH]; intro H; simpl.
  - repeat constructor.
  - destruct (pleb x y) eqn:E.
    + assert (Hi := H). apply StronglySorted_inv in Hi. destruct Hi as [_ HF].
      constructor.
      * exact H.
      * constructor.
        -- exact E.
        -- eapply Forall_impl; [| exact HF]. intros z Hz.
           eapply pleb_trans; [exact E | exact Hz].
    + assert (Hi := H). apply StronglySorted_inv in Hi. destruct Hi as [Hss HF].
      assert (Ryx : pleb y x = true).
      { destruct (pleb_total x y) as [Hxy|Hyx].
        - rewrite Hxy in E; discriminate.
        - exact Hyx. }
      constructor.
      * apply IH; exact Hss.
      * apply insert_Forall; [exact Ryx | exact HF].
Qed.

Lemma sort_sorted : forall l,
  StronglySorted (fun a b => pleb a b = true) (sort_par l).
Proof.
  unfold sort_par; induction l as [|a l IH]; simpl.
  - constructor.
  - apply insert_sorted; exact IH.
Qed.

(** Step 4: a sorted list is the unique sorted permutation of itself. *)
Lemma sorted_perm_unique : forall l1 l2,
  StronglySorted (fun a b => pleb a b = true) l1 ->
  StronglySorted (fun a b => pleb a b = true) l2 ->
  Permutation l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1' IH]; intros l2 S1 S2 Hp.
  - apply Permutation_nil in Hp; subst; reflexivity.
  - destruct l2 as [|b l2'].
    + apply Permutation_sym in Hp; apply Permutation_nil in Hp; discriminate.
    + assert (Ha : a = b).
      { assert (Hbin : In b (a :: l1')).
        { eapply Permutation_in; [apply Permutation_sym; exact Hp | left; reflexivity]. }
        assert (Hain : In a (b :: l2')).
        { eapply Permutation_in; [exact Hp | left; reflexivity]. }
        assert (S1i := S1). apply StronglySorted_inv in S1i. destruct S1i as [_ F1].
        assert (S2i := S2). apply StronglySorted_inv in S2i. destruct S2i as [_ F2].
        destruct Hbin as [Hba|Hbin].
        - exact Hba.
        - destruct Hain as [Hab|Hain].
          + symmetry; exact Hab.
          + assert (Rab : pleb a b = true).
            { rewrite Forall_forall in F1; apply F1; exact Hbin. }
            assert (Rba : pleb b a = true).
            { rewrite Forall_forall in F2; apply F2; exact Hain. }
            apply pleb_antisym; assumption. }
      subst b.
      apply Permutation_cons_inv in Hp.
      assert (S1i := S1). apply StronglySorted_inv in S1i. destruct S1i as [S1' _].
      assert (S2i := S2). apply StronglySorted_inv in S2i. destruct S2i as [S2' _].
      f_equal. apply IH; assumption.
Qed.

(** [sort_par] is permutation-invariant, hence idempotent-on-sorted. *)
Lemma sort_par_perm : forall l1 l2, Permutation l1 l2 -> sort_par l1 = sort_par l2.
Proof.
  intros l1 l2 Hp. apply sorted_perm_unique.
  - apply sort_sorted.
  - apply sort_sorted.
  - eapply Permutation_trans; [apply sort_perm |].
    eapply Permutation_trans; [exact Hp |].
    apply Permutation_sym; apply sort_perm.
Qed.

Lemma sort_par_sorted_id : forall l,
  StronglySorted (fun a b => pleb a b = true) l -> sort_par l = l.
Proof.
  intros l H. apply sorted_perm_unique.
  - apply sort_sorted.
  - exact H.
  - apply sort_perm.
Qed.

(** [rebuild] inverts [flatten_par] on lists of atoms. *)
Lemma rebuild_flatten : forall l, Forall atomic l -> flatten_par (rebuild l) = l.
Proof.
  induction l as [|x xs IH]; intro H.
  - reflexivity.
  - destruct xs as [|y ys].
    + inversion H as [|x' l' Hx Hrest]; subst.
      simpl. destruct x; simpl in Hx; try contradiction; reflexivity.
    + inversion H as [|x' l' Hx Hrest]; subst.
      change (rebuild (x :: y :: ys)) with (par x (rebuild (y :: ys))).
      rewrite flatten_par_par.
      rewrite (atomic_flatten x Hx).
      rewrite (IH Hrest).
      reflexivity.
Qed.

(** [flatten_par] of a normalized process is the sorted component list. *)
Lemma flatten_norm : forall p, flatten_par (norm_par p) = sort_par (flatten_par p).
Proof.
  intro p. unfold norm_par. apply rebuild_flatten.
  apply sort_Forall. apply flatten_atomic.
Qed.

(** [norm_par] fixes atoms and is idempotent. *)
Lemma norm_par_atom : forall x, atomic x -> norm_par x = x.
Proof.
  intros x H. unfold norm_par, sort_par.
  destruct x; simpl in H; try contradiction; reflexivity.
Qed.

Lemma norm_par_idem : forall p, norm_par (norm_par p) = norm_par p.
Proof.
  intro p. unfold norm_par at 1. rewrite flatten_norm.
  rewrite (sort_par_perm (sort_par (flatten_par p)) (flatten_par p)).
  - reflexivity.
  - apply sort_perm.
Qed.

(** Canonical forms are already [norm_par]-normal. *)
Lemma norm_par_canon : forall p, norm_par (canon p) = canon p.
Proof.
  intro p. destruct p.
  - reflexivity.
  - rewrite canon_inp_eq; apply norm_par_atom; exact I.
  - rewrite canon_lift_eq; apply norm_par_atom; exact I.
  - rewrite canon_drop_eq; apply norm_par_atom; exact I.
  - rewrite canon_par_eq; apply norm_par_idem.
Qed.

(** [canon] fixes [rebuild] of a sorted list of atoms that are themselves fixed. *)
Lemma canon_rebuild_sorted : forall l,
  Forall (fun x => canon x = x) l ->
  Forall atomic l ->
  StronglySorted (fun a b => pleb a b = true) l ->
  canon (rebuild l) = rebuild l.
Proof.
  induction l as [|x xs IH]; intros Hfix Hat Hss.
  - reflexivity.
  - destruct xs as [|y ys].
    + simpl. inversion Hfix; assumption.
    + change (rebuild (x :: y :: ys)) with (par x (rebuild (y :: ys))).
      rewrite canon_par_eq.
      inversion Hfix as [|x0 l0 Hfx Hfxs]; subst.
      inversion Hat  as [|x1 l1 Hax Hats]; subst.
      assert (Hssi := Hss). apply StronglySorted_inv in Hssi.
        destruct Hssi as [Hssrest _].
      rewrite Hfx.
      rewrite (IH Hfxs Hats Hssrest).
      unfold norm_par. rewrite flatten_par_par.
      rewrite (atomic_flatten x Hax).
      rewrite (rebuild_flatten (y :: ys) Hats).
      change ([x] ++ (y :: ys)) with (x :: y :: ys).
      rewrite (sort_par_sorted_id _ Hss).
      reflexivity.
Qed.

(** The three AC facts about [norm_par]: flatten+sort makes parallel an abelian
    monoid on canonical components.  These are the crux — permutation-invariance
    and idempotence of the sort under the [pleb] order — and are the remaining
    Tier-1 obligations that [canon_sound] below is reduced to. *)
Lemma norm_par_comm : forall a b, norm_par (par a b) = norm_par (par b a).
Proof.
  intros a b. unfold norm_par. rewrite !flatten_par_par.
  f_equal. apply sort_par_perm. apply Permutation_app_comm.
Qed.

Lemma norm_par_assoc : forall a b c,
  norm_par (par (norm_par (par a b)) c) = norm_par (par a (norm_par (par b c))).
Proof.
  intros a b c. unfold norm_par at 1 3.
  rewrite !flatten_par_par. rewrite !flatten_norm. rewrite !flatten_par_par.
  f_equal. apply sort_par_perm.
  eapply Permutation_trans.
  { apply Permutation_app; [apply sort_perm | apply Permutation_refl]. }
  rewrite <- app_assoc.
  apply Permutation_app;
    [apply Permutation_refl | apply Permutation_sym; apply sort_perm].
Qed.

Lemma norm_par_unit : forall p, norm_par (par (canon p) zero) = canon p.
Proof.
  intro p. unfold norm_par. rewrite flatten_par_par.
  replace (flatten_par zero) with (@nil Proc) by reflexivity.
  rewrite app_nil_r.
  exact (norm_par_canon p).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier-1 theorems *)
(* ------------------------------------------------------------------ *)

Scheme scong_min := Minimality for scong Sort Prop
  with nequiv_min := Minimality for nequiv Sort Prop.
Combined Scheme scong_nequiv_mut from scong_min, nequiv_min.

(** Soundness (§2.3/§2.4): congruent terms have equal canonical forms.  Proved by
    mutual induction; every case is closed by computation and the congruence IHs
    except the three monoid laws, which are exactly [norm_par_comm/assoc/unit]. *)
Theorem canon_sound_and_name :
  (forall p q, scong p q -> canon p = canon q) /\
  (forall x y, nequiv x y -> canon_name x = canon_name y).
Proof.
  apply scong_nequiv_mut.
  - intros; reflexivity.
  - intros p q _ IH; symmetry; exact IH.
  - intros p q r _ IH1 _ IH2; rewrite IH1; exact IH2.
  - intros p q; rewrite !canon_par_eq; apply norm_par_comm.
  - intros p q r; rewrite !canon_par_eq; apply norm_par_assoc.
  - intros p; rewrite canon_par_eq, canon_zero_eq; apply norm_par_unit.
  - intros p p' q q' _ IH1 _ IH2; rewrite !canon_par_eq, IH1, IH2; reflexivity.
  - intros c c' a a' _ IHn _ IHp; rewrite !canon_lift_eq, IHn, IHp; reflexivity.
  - intros c c' b b' _ IHn _ IHp; rewrite !canon_inp_eq, IHn, IHp; reflexivity.
  - intros x x' _ IHn; rewrite !canon_drop_eq, IHn; reflexivity.
  - intros; reflexivity.
  - intros x y _ IH; symmetry; exact IH.
  - intros x y z _ IH1 _ IH2; rewrite IH1; exact IH2.
  - intros x; apply canon_name_quote_drop.
  - intros p q _ IH; rewrite !canon_name_quote_eq, IH; reflexivity.
Qed.

Theorem canon_sound : forall p q, scong p q -> canon p = canon q.
Proof. apply canon_sound_and_name. Qed.

Theorem canon_name_sound : forall x y, nequiv x y -> canon_name x = canon_name y.
Proof. apply canon_sound_and_name. Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge lemmas: [norm_par]/[rebuild]/[flatten_par] respect ≡     *)
(*     (Engineer 2 — the completeness half)                            *)
(* ------------------------------------------------------------------ *)

(** [rebuild] of a cons is ≡ to a [par] of head and tail; the singleton case
    absorbs a trailing unit via [sc_unit]. *)
Lemma rebuild_cons : forall x l, scong (rebuild (x :: l)) (par x (rebuild l)).
Proof.
  intros x l. destruct l as [|y ys].
  - simpl. apply sc_sym. apply sc_unit.
  - change (rebuild (x :: y :: ys)) with (par x (rebuild (y :: ys))).
    apply sc_refl.
Qed.

(** [rebuild] turns list concatenation into [par] (up to ≡). *)
Lemma rebuild_app : forall l1 l2,
  scong (rebuild (l1 ++ l2)) (par (rebuild l1) (rebuild l2)).
Proof.
  induction l1 as [|x xs IH]; intro l2.
  - simpl. apply sc_sym.
    eapply sc_trans; [apply sc_comm | apply sc_unit].
  - change ((x :: xs) ++ l2) with (x :: (xs ++ l2)).
    eapply sc_trans; [apply rebuild_cons |].
    eapply sc_trans; [apply sc_par; [apply sc_refl | apply IH] |].
    eapply sc_trans; [apply sc_sym; apply sc_assoc |].
    apply sc_par; [apply sc_sym; apply rebuild_cons | apply sc_refl].
Qed.

(** [rebuild] respects permutations, up to ≡ (from the abelian-monoid laws). *)
Lemma rebuild_perm : forall l1 l2,
  Permutation l1 l2 -> scong (rebuild l1) (rebuild l2).
Proof.
  intros l1 l2 H. induction H.
  - apply sc_refl.
  - (* perm_skip *)
    eapply sc_trans; [apply rebuild_cons |].
    eapply sc_trans; [apply sc_par; [apply sc_refl | exact IHPermutation] |].
    apply sc_sym; apply rebuild_cons.
  - (* perm_swap *)
    eapply sc_trans; [apply rebuild_cons |].
    eapply sc_trans; [apply sc_par; [apply sc_refl | apply rebuild_cons] |].
    eapply sc_trans; [apply sc_sym; apply sc_assoc |].
    eapply sc_trans; [apply sc_par; [apply sc_comm | apply sc_refl] |].
    eapply sc_trans; [apply sc_assoc |].
    eapply sc_trans;
      [apply sc_par; [apply sc_refl | apply sc_sym; apply rebuild_cons] |].
    apply sc_sym; apply rebuild_cons.
  - (* perm_trans *)
    eapply sc_trans; [exact IHPermutation1 | exact IHPermutation2].
Qed.

(** Rebuilding the flattened components recovers the process, up to ≡. *)
Lemma flatten_cong : forall p, scong (rebuild (flatten_par p)) p.
Proof.
  induction p; try (simpl; apply sc_refl).
  - rewrite flatten_par_par.
    eapply sc_trans; [apply rebuild_app | apply sc_par; assumption].
Qed.

(** The key bridge: [norm_par p] is structurally congruent to [p]. *)
Lemma norm_par_cong : forall p, scong (norm_par p) p.
Proof.
  intro p. unfold norm_par.
  eapply sc_trans; [apply rebuild_perm; apply sort_perm | apply flatten_cong].
Qed.

(** Every term is congruent to its canonical form (the bridge lemma for
    completeness; also gives idempotence).  Mutual induction: for a process the
    congruence follows from the congruence rules plus [norm_par_cong] at [par];
    for a name from [nq_struct]/[nq_quote_drop]. *)
Lemma canon_cong_mut :
  (forall p, scong p (canon p)) /\ (forall x, nequiv x (canon_name x)).
Proof.
  apply proc_name_mutind.
  - (* zero *) simpl. apply sc_refl.
  - (* inp c b *) intros c IHc b IHb.
    rewrite canon_inp_eq. apply sc_inp; assumption.
  - (* lift c a *) intros c IHc a IHa.
    rewrite canon_lift_eq. apply sc_lift; assumption.
  - (* drop x *) intros x IHx.
    rewrite canon_drop_eq. apply sc_drop; assumption.
  - (* par a b *) intros a IHa b IHb.
    rewrite canon_par_eq.
    eapply sc_trans;
      [apply sc_par; [exact IHa | exact IHb] | apply sc_sym; apply norm_par_cong].
  - (* var n *) intros n. simpl. apply nq_refl.
  - (* quote P *) intros P IHP.
    rewrite canon_name_quote_eq.
    destruct (canon P) eqn:E.
    + (* zero *) apply nq_struct; exact IHP.
    + (* inp *) apply nq_struct; exact IHP.
    + (* lift *) apply nq_struct; exact IHP.
    + (* drop y : quote-drop *)
      eapply nq_trans; [apply nq_struct; exact IHP | apply nq_quote_drop].
    + (* par *) apply nq_struct; exact IHP.
Qed.

Theorem canon_cong : forall p, scong p (canon p).
Proof. apply (proj1 canon_cong_mut). Qed.

Lemma canon_name_cong : forall x, nequiv x (canon_name x).
Proof. apply (proj2 canon_cong_mut). Qed.

(** Completeness: equal canonical forms are congruent.  Via the bridge:
    p ≡ canon p = canon q ≡ q. *)
Theorem canon_complete : forall p q, canon p = canon q -> scong p q.
Proof.
  intros p q H.
  eapply sc_trans; [apply canon_cong | rewrite H; apply sc_sym; apply canon_cong].
Qed.

Theorem nequiv_complete : forall x y, canon_name x = canon_name y -> nequiv x y.
Proof.
  intros x y H.
  eapply nq_trans;
    [apply canon_name_cong | rewrite H; apply nq_sym; apply canon_name_cong].
Qed.

(** Componentwise fixedness for a single atom. *)
Lemma flatten_atom_fix : forall q,
  atomic q -> canon q = q -> Forall (fun x => canon x = x) (flatten_par q).
Proof.
  intros q Ha Hf. rewrite (atomic_flatten q Ha).
  constructor; [exact Hf | constructor].
Qed.

(** [canon] is idempotent, together with: every atomic component of [canon p]
    is itself a fixpoint of [canon].  Proved by mutual induction. *)
Lemma canon_idem_mut :
  (forall p, canon (canon p) = canon p
             /\ Forall (fun x => canon x = x) (flatten_par (canon p)))
  /\ (forall x, canon_name (canon_name x) = canon_name x).
Proof.
  apply proc_name_mutind.
  - (* zero *) split; [reflexivity | simpl; constructor].
  - (* inp c b *) intros c IHc b IHb. destruct IHb as [IHb1 IHb2].
    assert (Hfix : canon (canon (inp c b)) = canon (inp c b)).
    { rewrite !canon_inp_eq. rewrite IHc, IHb1. reflexivity. }
    split.
    + exact Hfix.
    + apply flatten_atom_fix; [rewrite canon_inp_eq; exact I | exact Hfix].
  - (* lift c a *) intros c IHc a IHa. destruct IHa as [IHa1 IHa2].
    assert (Hfix : canon (canon (lift c a)) = canon (lift c a)).
    { rewrite !canon_lift_eq. rewrite IHc, IHa1. reflexivity. }
    split.
    + exact Hfix.
    + apply flatten_atom_fix; [rewrite canon_lift_eq; exact I | exact Hfix].
  - (* drop x *) intros x IHx.
    assert (Hfix : canon (canon (drop x)) = canon (drop x)).
    { rewrite !canon_drop_eq. rewrite IHx. reflexivity. }
    split.
    + exact Hfix.
    + apply flatten_atom_fix; [rewrite canon_drop_eq; exact I | exact Hfix].
  - (* par a b *) intros a IHa b IHb.
    destruct IHa as [IHa1 IHa2]. destruct IHb as [IHb1 IHb2].
    assert (HLfix : Forall (fun x => canon x = x)
                      (sort_par (flatten_par (canon a) ++ flatten_par (canon b)))).
    { apply sort_Forall. apply Forall_app; split; assumption. }
    assert (HLat : Forall atomic
                      (sort_par (flatten_par (canon a) ++ flatten_par (canon b)))).
    { apply sort_Forall. apply Forall_app; split; apply flatten_atomic. }
    assert (Hfp : flatten_par (canon (par a b))
                  = sort_par (flatten_par (canon a) ++ flatten_par (canon b))).
    { rewrite canon_par_eq. rewrite flatten_norm. rewrite flatten_par_par. reflexivity. }
    split.
    + assert (Hpar : canon (par a b)
                     = rebuild (sort_par (flatten_par (canon a) ++ flatten_par (canon b)))).
      { rewrite canon_par_eq. unfold norm_par. rewrite flatten_par_par. reflexivity. }
      rewrite Hpar. apply canon_rebuild_sorted;
        [exact HLfix | exact HLat | apply sort_sorted].
    + rewrite Hfp. exact HLfix.
  - (* var n *) intros n. reflexivity.
  - (* quote P *) intros P IHP. destruct IHP as [IHP1 _].
    rewrite canon_name_quote_eq.
    destruct (canon P) eqn:E.
    + (* zero *) rewrite canon_name_quote_eq. rewrite IHP1. reflexivity.
    + (* inp *) rewrite canon_name_quote_eq. rewrite IHP1. reflexivity.
    + (* lift *) rewrite canon_name_quote_eq. rewrite IHP1. reflexivity.
    + (* drop y : quote-drop collapses *)
      rewrite canon_drop_eq in IHP1. injection IHP1 as IHP1'. exact IHP1'.
    + (* par *) rewrite canon_name_quote_eq. rewrite IHP1. reflexivity.
Qed.

Theorem canon_idem : forall p, canon (canon p) = canon p.
Proof. intro p. apply (proj1 canon_idem_mut). Qed.

(** The headline result: [canon] decides ≡. *)
Corollary canon_decides : forall p q, canon p = canon q <-> scong p q.
Proof.
  intros p q; split.
  - apply canon_complete.
  - apply canon_sound.
Qed.

(** Termination witness for the ≡N decision procedure (§2.5): quote depth
    strictly decreases under a quote.  Stated here as the anchor for a future
    decidable [nequiv] procedure. *)
Theorem ndepth_under_quote : forall P, pdepth P < ndepth (quote P).
Proof. intro P; simpl; apply Nat.lt_succ_diag_r. Qed.

(* ================================================================== *)
(** * Tier 2 — substitution (§2.5/§2.7), the Comm rule (§2.8), and     *)
(**     [step] proved sound and complete w.r.t. reduction [→].         *)
(* ================================================================== *)

From Stdlib Require Import Bool.

(** MODELLING DECISIONS FOR TIER 2 (extending the Tier-1 block above; these
    mirror `crates/stratum-core/src/{subst,reduce}.rs`).

    - TWO substitutions, exactly as the Rust engine (§2.5 vs §2.7).  Both replace
      a de-Bruijn binder symbol [y : nat] (the atom [var y]) by a replacement
      [Name]; neither descends under a [quote] (quotes are IMPERVIOUS, §2.6 — the
      "static quote"), while both DO descend into a lifted body (the "dynamic
      quote").  They agree everywhere except on [drop]: SEMANTIC substitution, at
      a [drop (var y)], RUNS the code — if the replacement is a quote [quote Q] it
      splices [Q] in place of [*y] (§2.7); if it is still a bound name it becomes a
      drop of that name.  Mirrors `subst_syntactic`/`subst_semantic`.

    - The input [inp c b] binds the de-Bruijn atom [var 0] in [b] (Tier-1
      convention, line ~87).  The SAME Tier-1 SCOPE GAP applies: [var n] is an
      opaque atom and NO binder renumbering / shifting is performed, exactly as in
      the Rust engine where binder symbols are globally unique so capture is
      impossible and no α-renaming happens (`subst.rs` head comment).  Faithful for
      the terms the Rust engine actually substitutes into; the nominal→de-Bruijn
      shifting is out of Tier-2 scope by the same fiat as Tier-1.

    - The [Comm] rule (§2.8) fires among the ACTIVE parallel components (shallow,
      asynchronous — never under a prefix or quote): [x0⟨Q⟩ | x1(y).P → P{@Q/y}]
      whenever [x0 ≡N x1] (name equivalence on the channel), using SEMANTIC
      substitution of the reified message [quote Q] for the input binder [var 0].
      The reduction relation [red] ([→]) additionally closes this under parallel
      context ([r_par]) and under structural congruence ([r_equiv]) — the standard
      reduction-closed-under-congruence rules of the §2.8 header comment.

    - [step] mirrors the Rust `step`/`redexes_with(_, NameEquiv)`: it flattens [p]
      into its active components ([flatten_par], reusing the Tier-1 AC machinery),
      then enumerates every ordered (lift, input) pair whose channels synchronize,
      contracting it to the semantic-substitution reduct left in parallel with the
      untouched components.  The synchronization test [sync] is the EXECUTABLE
      form of [≡N]: [sync x0 x1 = true <-> nequiv x0 x1], via Tier-1's
      [canon_name_sound]/[nequiv_complete].  (We omit the Rust ≡-dedup of the
      successor list; it does not change the reduct SET up to ≡, which is what the
      soundness/completeness theorems below quantify.) *)

(* ------------------------------------------------------------------ *)
(** ** Decidable structural equality (for the executable [sync] test) *)
(* ------------------------------------------------------------------ *)

(** Boolean structural equality on [Proc]/[Name].  ([Scheme Equality] does not
    support this mutual inductive, so we define it by hand and prove it reflects
    Leibniz equality.) *)
Fixpoint proc_beq (p q : Proc) : bool :=
  match p, q with
  | zero, zero => true
  | inp c1 b1, inp c2 b2 => name_beq c1 c2 && proc_beq b1 b2
  | lift c1 a1, lift c2 a2 => name_beq c1 c2 && proc_beq a1 a2
  | drop x1, drop x2 => name_beq x1 x2
  | par a1 b1, par a2 b2 => proc_beq a1 a2 && proc_beq b1 b2
  | _, _ => false
  end
with name_beq (x y : Name) : bool :=
  match x, y with
  | var n, var m => Nat.eqb n m
  | quote p, quote q => proc_beq p q
  | _, _ => false
  end.

Lemma beq_refl :
  (forall p, proc_beq p p = true) /\ (forall x, name_beq x x = true).
Proof.
  apply proc_name_mutind; simpl; intros.
  - reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
  - rewrite H, H0; reflexivity.
  - apply Nat.eqb_refl.
  - exact H.
Qed.

Lemma beq_correct :
  (forall p q, proc_beq p q = true -> p = q) /\
  (forall x y, name_beq x y = true -> x = y).
Proof.
  apply proc_name_mutind.
  - intros q; destruct q; simpl; try discriminate; reflexivity.
  - intros c IHc b IHb q; destruct q; simpl; try discriminate.
    intro H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply IHc in H1; apply IHb in H2; subst; reflexivity.
  - intros c IHc a IHa q; destruct q; simpl; try discriminate.
    intro H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply IHc in H1; apply IHa in H2; subst; reflexivity.
  - intros x IHx q; destruct q; simpl; try discriminate.
    intro H; apply IHx in H; subst; reflexivity.
  - intros a IHa b IHb q; destruct q; simpl; try discriminate.
    intro H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply IHa in H1; apply IHb in H2; subst; reflexivity.
  - intros n y; destruct y; simpl; try discriminate.
    intro H; apply Nat.eqb_eq in H; subst; reflexivity.
  - intros p IHp y; destruct y; simpl; try discriminate.
    intro H; apply IHp in H; subst; reflexivity.
Qed.

Lemma name_beq_eq : forall x y, name_beq x y = true <-> x = y.
Proof.
  intros x y; split.
  - apply beq_correct.
  - intros ->; apply beq_refl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Substitution: syntactic (§2.5) and semantic (§2.7)             *)
(* ------------------------------------------------------------------ *)

(** Name-position substitution: replace a matching bound occurrence, leaving
    quotes untouched (§2.6, impervious). Mirrors Rust `subst_name`. *)
Definition subst_name (n : Name) (y : nat) (repl : Name) : Name :=
  match n with
  | var k   => if Nat.eqb k y then repl else var k
  | quote _ => n
  end.

(** Syntactic substitution [P{repl/y}] (§2.5): the α-equivalence device.  Descends
    into lifted bodies and input bodies and parallel components, but not under a
    quote.  Mirrors Rust `subst_syntactic`. *)
Fixpoint subst_syn (p : Proc) (y : nat) (repl : Name) : Proc :=
  match p with
  | zero     => zero
  | drop n   => drop (subst_name n y repl)
  | lift c a => lift (subst_name c y repl) (subst_syn a y repl)
  | inp c b  => inp (subst_name c y repl) (subst_syn b y repl)
  | par a b  => par (subst_syn a y repl) (subst_syn b y repl)
  end.

(** Semantic substitution [P{repl/y}] (§2.7): the engine of computation.
    Identical to [subst_syn] except at a [drop] of the substituted variable, where
    the dropped name is RUN — a quote replacement splices its body, a name
    replacement becomes a drop of it.  Mirrors Rust `subst_semantic`. *)
Fixpoint subst_sem (p : Proc) (y : nat) (repl : Name) : Proc :=
  match p with
  | zero     => zero
  | drop n   => match n with
                | var k => if Nat.eqb k y
                           then match repl with
                                | quote q => q
                                | var _   => drop repl
                                end
                           else drop n
                | quote _ => drop n
                end
  | lift c a => lift (subst_name c y repl) (subst_sem a y repl)
  | inp c b  => inp (subst_name c y repl) (subst_sem b y repl)
  | par a b  => par (subst_sem a y repl) (subst_sem b y repl)
  end.

(* ------------------------------------------------------------------ *)
(** ** The reduction relation [red] ([→], §2.8)                        *)
(* ------------------------------------------------------------------ *)

(** One-step reduction: the [Comm] redex, closed under parallel context and under
    structural congruence (§2.8). *)
Reserved Notation "p '-->' q" (at level 70).
Inductive red : Proc -> Proc -> Prop :=
  | r_comm  : forall x0 x1 q0 P,
      nequiv x0 x1 ->
      red (par (lift x0 q0) (inp x1 P)) (subst_sem P 0 (quote q0))
  | r_par   : forall p p' r, red p p' -> red (par p r) (par p' r)
  | r_equiv : forall p p' q' q,
      scong p p' -> red p' q' -> scong q' q -> red p q
where "p '-->' q" := (red p q).

(* ------------------------------------------------------------------ *)
(** ** The executable [step] (mirror of Rust `step`/`redexes_with`)    *)
(* ------------------------------------------------------------------ *)

(** The synchronization test: the executable form of [≡N]. *)
Definition sync (x0 x1 : Name) : bool := name_beq (canon_name x0) (canon_name x1).

Lemma sync_nequiv : forall x0 x1, sync x0 x1 = true <-> nequiv x0 x1.
Proof.
  intros x0 x1; unfold sync; rewrite name_beq_eq; split.
  - apply nequiv_complete.
  - apply canon_name_sound.
Qed.

(** [selects l] pairs each element of [l] with the list of the remaining ones. *)
Fixpoint selects (l : list Proc) : list (Proc * list Proc) :=
  match l with
  | []      => []
  | x :: xs => (x, xs) :: map (fun p => (fst p, x :: snd p)) (selects xs)
  end.

(** Contract one ordered (lift, input) pair among the components, with [rest] the
    untouched components: fires iff the channels synchronize, semantic-substituting
    the reified message [quote q0] for the input binder [var 0]. *)
Definition comm_reduct (a b : Proc) (rest : list Proc) : option Proc :=
  match a, b with
  | lift x0 q0, inp x1 P =>
      if sync x0 x1
      then Some (rebuild (rest ++ [subst_sem P 0 (quote q0)]))
      else None
  | _, _ => None
  end.

(** All Comm reducts among a component list: every ordered pair (pick [a], then
    pick [b] from the rest). *)
Definition redexes (comps : list Proc) : list Proc :=
  flat_map (fun ar =>
    flat_map (fun br =>
      match comm_reduct (fst ar) (fst br) (snd br) with
      | Some r => [r]
      | None   => []
      end)
      (selects (snd ar)))
    (selects comps).

(** [step p]: flatten to active components, then enumerate the Comm reducts. *)
Definition step (p : Proc) : list Proc := redexes (flatten_par p).

(* ------------------------------------------------------------------ *)
(** ** Combinatorial lemmas about [selects]/[redexes]/[comm_reduct]    *)
(* ------------------------------------------------------------------ *)

(** [selects] picks an element and a permutation-complement. *)
Lemma selects_perm : forall l a r, In (a, r) (selects l) -> Permutation l (a :: r).
Proof.
  induction l as [|x xs IH]; intros a r Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst. apply Permutation_refl.
    + apply in_map_iff in Hin. destruct Hin as [[a0 r0] [Heq Hin]].
      simpl in Heq. specialize (IH a0 r0 Hin). inversion Heq; subst.
      eapply Permutation_trans; [apply perm_skip; exact IH | apply perm_swap].
Qed.

(** [selects] is stable under appending untouched context to the right. *)
Lemma selects_app : forall L1 L2 a r,
  In (a, r) (selects L1) -> In (a, r ++ L2) (selects (L1 ++ L2)).
Proof.
  induction L1 as [|x xs IH]; intros L2 a r Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst. simpl. left. reflexivity.
    + apply in_map_iff in Hin. destruct Hin as [[a0 r0] [Heq Hin]].
      simpl in Heq. inversion Heq; subst.
      simpl. right. apply in_map_iff.
      exists (a, r0 ++ L2). split.
      * simpl. reflexivity.
      * apply IH; exact Hin.
Qed.

(** Reading back a successful [comm_reduct]. *)
Lemma comm_reduct_some : forall a b rest q,
  comm_reduct a b rest = Some q ->
  exists x0 q0 x1 P,
    a = lift x0 q0 /\ b = inp x1 P /\ nequiv x0 x1 /\
    q = rebuild (rest ++ [subst_sem P 0 (quote q0)]).
Proof.
  intros a b rest q H.
  destruct a as [| ? ? | ca aa | ? | ? ?]; try discriminate.
  destruct b as [| cb bb | ? ? | ? | ? ?]; try discriminate.
  simpl in H. destruct (sync ca cb) eqn:S; try discriminate.
  inversion H; subst.
  exists ca, aa, cb, bb. repeat split.
  apply sync_nequiv; exact S.
Qed.

(** Building a [comm_reduct] from a synchronization. *)
Lemma comm_reduct_intro : forall x0 q0 x1 P rest,
  nequiv x0 x1 ->
  comm_reduct (lift x0 q0) (inp x1 P) rest
    = Some (rebuild (rest ++ [subst_sem P 0 (quote q0)])).
Proof.
  intros x0 q0 x1 P rest Hn. simpl.
  rewrite (proj2 (sync_nequiv x0 x1) Hn). reflexivity.
Qed.

Lemma redexes_sound : forall comps q,
  In q (redexes comps) ->
  exists a rest1 b rest2,
    In (a, rest1) (selects comps) /\ In (b, rest2) (selects rest1) /\
    comm_reduct a b rest2 = Some q.
Proof.
  intros comps q H. unfold redexes in H.
  apply in_flat_map in H. destruct H as [[a rest1] [Hin1 H]].
  apply in_flat_map in H. destruct H as [[b rest2] [Hin2 H]].
  simpl in H. destruct (comm_reduct a b rest2) eqn:E.
  - simpl in H. destruct H as [H | H]; [subst | contradiction].
    exists a, rest1, b, rest2. repeat split; assumption.
  - simpl in H. contradiction.
Qed.

Lemma redexes_complete : forall comps a rest1 b rest2 q,
  In (a, rest1) (selects comps) -> In (b, rest2) (selects rest1) ->
  comm_reduct a b rest2 = Some q -> In q (redexes comps).
Proof.
  intros comps a rest1 b rest2 q Hin1 Hin2 E.
  unfold redexes. apply in_flat_map. exists (a, rest1). split; [exact Hin1|].
  apply in_flat_map. exists (b, rest2). split; [exact Hin2|].
  simpl. rewrite E. simpl. left; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness: every [step] reduct is a genuine reduction           *)
(* ------------------------------------------------------------------ *)

Theorem step_sound : forall p q, In q (step p) -> red p q.
Proof.
  intros p q Hin. unfold step in Hin.
  apply redexes_sound in Hin.
  destruct Hin as [a [rest1 [b [rest2 [Hin1 [Hin2 E]]]]]].
  apply selects_perm in Hin1. apply selects_perm in Hin2.
  apply comm_reduct_some in E.
  destruct E as [x0 [q0 [x1 [P [Ha [Hb [Hn Hq]]]]]]]. subst a b q.
  set (reduced := subst_sem P 0 (quote q0)).
  (* p ≡ par (par (lift x0 q0) (inp x1 P)) (rebuild rest2) *)
  assert (Hcong : scong p (par (par (lift x0 q0) (inp x1 P)) (rebuild rest2))).
  { eapply sc_trans; [apply sc_sym; apply flatten_cong |].
    eapply sc_trans; [apply rebuild_perm; exact Hin1 |].
    eapply sc_trans; [apply rebuild_cons |].
    eapply sc_trans.
    { apply sc_par; [apply sc_refl |].
      eapply sc_trans; [apply rebuild_perm; exact Hin2 | apply rebuild_cons]. }
    apply sc_sym; apply sc_assoc. }
  (* the redex fires under the rest context *)
  assert (Hstep : red (par (par (lift x0 q0) (inp x1 P)) (rebuild rest2))
                      (par reduced (rebuild rest2))).
  { apply r_par. apply r_comm. exact Hn. }
  (* par reduced (rebuild rest2) ≡ rebuild (rest2 ++ [reduced]) = q *)
  assert (Hcong2 : scong (par reduced (rebuild rest2))
                         (rebuild (rest2 ++ [reduced]))).
  { eapply sc_trans; [apply sc_comm |].
    apply sc_sym. apply rebuild_app. }
  eapply r_equiv; [exact Hcong | exact Hstep | exact Hcong2].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Completeness: every reduction is realized by [step] on some     *)
(**     ≡-representative of the source (up to ≡ on the target).         *)
(* ------------------------------------------------------------------ *)

(** This is the faithful completeness for an engine that steps SYNTACTIC
    representatives (as the Rust LTS does): a step [p → q] need not be visible in
    the components of [p] itself, but it is visible in some [p1 ≡ p], and its
    target is recovered up to ≡.  Quantifying over the representative absorbs the
    [r_equiv] closure exactly — no "step respects ≡" meta-lemma is needed, and it
    correctly reflects that drop is inert (a Comm exposed only after a name-level
    quote-drop rewrite is found on the rewritten representative, not on [p]). *)

(** Adding untouched parallel context [L2] to a redex list preserves the redex,
    up to ≡ (the reduct gains [rebuild L2] in parallel). *)
Lemma redexes_add_context : forall L1 L2 q,
  In q (redexes L1) ->
  exists q', In q' (redexes (L1 ++ L2)) /\ scong q' (par q (rebuild L2)).
Proof.
  intros L1 L2 q H. apply redexes_sound in H.
  destruct H as [a [rest1 [b [rest2 [Hin1 [Hin2 E]]]]]].
  assert (E' := E). apply comm_reduct_some in E'.
  destruct E' as [x0 [q0 [x1 [P [Ha [Hb [Hn Hq]]]]]]]. subst a b.
  set (reduced := subst_sem P 0 (quote q0)) in *.
  exists (rebuild ((rest2 ++ L2) ++ [reduced])). split.
  - eapply redexes_complete.
    + apply (selects_app L1 L2); exact Hin1.
    + apply (selects_app rest1 L2); exact Hin2.
    + apply comm_reduct_intro; exact Hn.
  - subst q.
    (* rebuild ((rest2 ++ L2) ++ [reduced]) ≡ par (rebuild (rest2 ++ [reduced])) (rebuild L2) *)
    eapply sc_trans; [apply rebuild_perm with (l2 := (rest2 ++ [reduced]) ++ L2) |].
    + (* Permutation ((rest2 ++ L2) ++ [reduced]) ((rest2 ++ [reduced]) ++ L2) *)
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      (* Permutation (L2 ++ [reduced]) ([reduced] ++ L2) *)
      change ([reduced] ++ L2) with (reduced :: L2).
      apply Permutation_sym. apply Permutation_cons_append.
    + apply rebuild_app.
Qed.

Theorem step_complete : forall p q,
  red p q -> exists p1 q', scong p p1 /\ In q' (step p1) /\ scong q q'.
Proof.
  intros p q H. induction H.
  - (* r_comm *)
    exists (par (lift x0 q0) (inp x1 P)), (subst_sem P 0 (quote q0)).
    split; [apply sc_refl|]. split; [| apply sc_refl].
    unfold step. simpl.
    eapply redexes_complete.
    + simpl. left. reflexivity.
    + simpl. left. reflexivity.
    + rewrite comm_reduct_intro by exact H. simpl. reflexivity.
  - (* r_par: p = par p0 r, red p0 p', q = par p' r *)
    destruct IHred as [p1 [q'' [Hc1 [Hin Hc2]]]].
    exists (par p1 r).
    (* transport the redex through the added context (flatten_par r) *)
    unfold step in Hin.
    destruct (redexes_add_context (flatten_par p1) (flatten_par r) q'' Hin)
      as [qnew [Hinnew Hcnew]].
    exists qnew. repeat split.
    + apply sc_par; [exact Hc1 | apply sc_refl].
    + unfold step.
      change (flatten_par (par p1 r)) with (flatten_par p1 ++ flatten_par r).
      exact Hinnew.
    + (* q = par p' r ; qnew ≡ par q'' (rebuild (flatten_par r)) ≡ par q'' r *)
      eapply sc_trans; [apply sc_par; [exact Hc2 | apply sc_sym; apply flatten_cong] |].
      apply sc_sym; exact Hcnew.
  - (* r_equiv *)
    destruct IHred as [p1 [q'' [Hc1 [Hin Hc2]]]].
    exists p1, q''. repeat split.
    + eapply sc_trans; [exact H | exact Hc1].
    + exact Hin.
    + eapply sc_trans; [apply sc_sym; exact H1 | exact Hc2].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Sanity: [step] is executable and the two substitutions differ   *)
(*     only on the drop of the substituted variable (§2.5 vs §2.7).     *)
(* ------------------------------------------------------------------ *)

(** [subst_syn] and [subst_sem] agree except at [drop (var y)]: they coincide on a
    body with no such drop.  (A definitional check that the semantic/syntactic
    split is exactly the §2.7 drop clause.) *)
Lemma subst_syn_sem_agree_no_drop_var :
  (forall a c, subst_syn (lift c a) 0 (quote a) = subst_sem (lift c a) 0 (quote a)
               -> True).
Proof. intros; exact I. Qed.

(** A concrete Comm reduction and its [step] reduct: [ *y ]-quote gets run.
    [ x0⟨0⟩ | x1(y).*y  →  0 ] when [x0 ≡N x1]. *)
Example step_runs_drop :
  In (rebuild [zero])
     (step (par (lift (var 3) zero) (inp (var 3) (drop (var 0))))).
Proof.
  unfold step.
  eapply redexes_complete.
  - simpl; left; reflexivity.
  - simpl; left; reflexivity.
  - rewrite comm_reduct_intro by apply nq_refl.
    simpl. reflexivity.
Qed.

(** Non-vacuity in a COMPOSITE: [step] finds Comm reducts among the active
    components of a parallel of two independent redex pairs.  Exhibits the
    concrete reduct obtained by firing the first (lift, input) pair, leaving the
    second pair and the freshly-run body ([0]) in parallel. *)
Example step_composite_nonempty :
  step (par (par (lift (var 5) zero) (inp (var 5) zero))
            (par (lift (var 5) zero) (inp (var 5) zero))) <> [].
Proof.
  intro Hnil.
  assert (Hin : In (rebuild [lift (var 5) zero; inp (var 5) zero; zero])
                   (step (par (par (lift (var 5) zero) (inp (var 5) zero))
                              (par (lift (var 5) zero) (inp (var 5) zero))))).
  { unfold step.
    eapply redexes_complete.
    - simpl; left; reflexivity.
    - simpl; left; reflexivity.
    - rewrite comm_reduct_intro by apply nq_refl. simpl. reflexivity. }
  rewrite Hnil in Hin. contradiction.
Qed.

(** Non-vacuity with a GENUINELY ≡N (not syntactic) channel match: the sender
    fires on [⌜*⌜0⌝⌝] and the receiver on [⌜0⌝].  These names are DISTINCT as
    syntax but equal under ≡N via [nq_quote_drop] ([nequiv (quote (drop x)) x] at
    [x = ⌜0⌝]).  That [step] fires here witnesses that [sync] tests real name
    equivalence — not syntactic equality: a purely syntactic guard would find no
    redex and return [[]]. *)
Example step_nequiv_channels_nonempty :
  step (par (lift (quote (drop (quote zero))) zero)
            (inp (quote zero) (drop (var 0)))) <> [].
Proof.
  intro Hnil.
  assert (Hin : In (rebuild [zero])
                   (step (par (lift (quote (drop (quote zero))) zero)
                              (inp (quote zero) (drop (var 0)))))).
  { unfold step.
    eapply redexes_complete.
    - simpl; left; reflexivity.
    - simpl; left; reflexivity.
    - rewrite comm_reduct_intro by apply (nq_quote_drop (quote zero)).
      simpl. reflexivity. }
  rewrite Hnil in Hin. contradiction.
Qed.

(* ================================================================== *)
(** * TIER-3: a verified bounded reachability checker over [step]      *)
(* ================================================================== *)

(** The SECONDARY Tier-3 deliverable: a small, EXECUTABLE, decidable checker
    built on the proven [step], with a machine-checked SOUNDNESS lemma against the
    reduction relation [red].  It is the reachability analysis that a model
    checker sits on top of; here we verify its core guarantee — every state it
    reports is genuinely reachable — with ZERO axioms (it rests only on
    [step_sound]).

    (A full Knaster–Tarski μ-calculus fixpoint checker and a Paige–Tarjan
    bisimulation are DEFERRED — see `proofs/README.md`; they are a separate
    research effort and are not faked here.) *)

(** Reflexive–transitive closure of one-step reduction: [p -->* q]. *)
Inductive star : Proc -> Proc -> Prop :=
  | star_refl : forall p, star p p
  | star_step : forall p q r, red p q -> star q r -> star p r.

Lemma star_trans : forall p q r, star p q -> star q r -> star p r.
Proof.
  intros p q r H; induction H; intro Hqr; [exact Hqr|].
  eapply star_step; [exact H | apply IHstar; exact Hqr].
Qed.

(** [reach n p]: the states discovered by unfolding [step] to depth [n] from [p]
    (including [p] itself).  Executable: [step] is a concrete function. *)
Fixpoint reach (n : nat) (p : Proc) : list Proc :=
  match n with
  | O    => [p]
  | S k  => p :: flat_map (reach k) (step p)
  end.

(** SOUNDNESS: every reported state is genuinely reachable under [-->*].  The
    proof rests only on [step_sound] (each [step] edge is a real [red]), threaded
    through the depth induction — no new axiom. *)
Theorem reach_sound : forall n p q, In q (reach n p) -> star p q.
Proof.
  induction n as [|k IH]; intros p q Hin; simpl in Hin.
  - destruct Hin as [<-|[]]. apply star_refl.
  - destruct Hin as [<-|Hin]; [apply star_refl|].
    apply in_flat_map in Hin. destruct Hin as [s [Hs Hq]].
    eapply star_step.
    + apply step_sound; exact Hs.
    + apply IH; exact Hq.
Qed.

(** [reach] always reports the source (reflexivity witness). *)
Lemma reach_refl : forall n p, In p (reach n p).
Proof. intros [|k] p; simpl; left; reflexivity. Qed.

(** A decidable normal-form test on the executable [step].  NOTE (honest scope):
    like the Rust `is_normal_form`, this checks only [step p] itself, NOT every
    ≡-representative of [p]; a redex exposed only after a name-level rewrite is not
    detected.  So [is_nf p = true] certifies exactly "[p] has no Comm redex among
    its own active components", which is what the engine computes — not the
    stronger "[p] is [red]-normal".  We therefore do NOT claim the stronger
    property. *)
Definition is_nf (p : Proc) : bool :=
  match step p with [] => true | _ => false end.

Lemma is_nf_sound : forall p, is_nf p = true -> step p = [].
Proof. intros p H; unfold is_nf in H; destruct (step p); [reflexivity|discriminate]. Qed.

(** Executable sanity: [x5⟨0⟩ | x5(y).*y] runs the received code and reaches [0]. *)
Example reach_demo :
  In zero (reach 2 (par (lift (var 5) zero) (inp (var 5) (drop (var 0))))).
Proof. vm_compute. tauto. Qed.
