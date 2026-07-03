
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val compare : nat -> nat -> comparison
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type proc =
| Zero
| Inp of name * proc
| Lift of name * proc
| Drop of name
| Par of proc * proc
and name =
| Var of nat
| Quote of proc

val proc_compare : proc -> proc -> comparison

val name_compare : name -> name -> comparison

val pleb : proc -> proc -> bool

val flatten_par : proc -> proc list

val insert_proc : proc -> proc list -> proc list

val sort_par : proc list -> proc list

val rebuild : proc list -> proc

val norm_par : proc -> proc

val canon : proc -> proc

val canon_name : name -> name

val proc_beq : proc -> proc -> bool

val name_beq : name -> name -> bool

val subst_name : name -> nat -> name -> name

val subst_sem : proc -> nat -> name -> proc

val sync : name -> name -> bool

val selects : proc list -> (proc, proc list) prod list

val comm_reduct : proc -> proc -> proc list -> proc option

val redexes : proc list -> proc list

val step : proc -> proc list
