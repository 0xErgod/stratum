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
    [sorted_perm_unique], resting on the [pleb] order axioms); the completeness
    side [canon_cong] -> [canon_complete] / [nequiv_complete]; [canon_idem]; and
    [ndepth_under_quote].

    AXIOM BUDGET.  The ONLY axioms are the three [pleb] order laws
    ([pleb_total]/[pleb_antisym]/[pleb_trans], below), which any concrete
    instantiation of the [pleb] comparison must discharge.  `Print Assumptions`
    on every theorem reports exactly these (plus the [pleb] Parameter itself) and
    nothing else — in particular no unsanctioned axiom and no Admitted lemma.

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

    - [pleb] is an ABSTRACT total order, not tied to the Rust derived [Ord]
      (variant order Zero<Input<Lift<Drop<Par, Quote<Var).  The RELATION decided
      here — [canon p = canon q] — is invariant under the choice of total order on
      components (equal iff the component multisets are permutations; this is
      exactly what [sort_par_perm] establishes), so ≡ agrees with the Rust decision
      regardless of which linear order instantiates [pleb].  CAVEAT: if any code
      depends on the specific canonical REPRESENTATIVE (serialized/hashed canonical
      forms crossing the Coq/Rust boundary, or LTS state identity in SPEC §F1),
      [pleb] must be instantiated to Rust's [Ord] — an open obligation, not
      discharged here.

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
    assumption. *)
Parameter pleb : Proc -> Proc -> bool.

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

(** The eventual concrete [pleb] (mirroring the Rust derived [Ord]) must be a
    decidable linear order on canonical processes.  Stated as axioms, these are
    the obligations any instantiation must meet; the AC lemmas below depend on
    them. *)
Axiom pleb_total   : forall x y, pleb x y = true \/ pleb y x = true.
Axiom pleb_antisym : forall x y, pleb x y = true -> pleb y x = true -> x = y.
Axiom pleb_trans   : forall x y z, pleb x y = true -> pleb y z = true -> pleb x z = true.

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
