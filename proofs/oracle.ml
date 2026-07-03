
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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, l0) -> app (f x) (flat_map f l0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, l0) -> f b (fold_right f a0 l0)

type proc =
| Zero
| Inp of name * proc
| Lift of name * proc
| Drop of name
| Par of proc * proc
and name =
| Var of nat
| Quote of proc

(** val proc_compare : proc -> proc -> comparison **)

let rec proc_compare p q =
  match p with
  | Zero -> (match q with
             | Zero -> Eq
             | _ -> Lt)
  | Inp (c1, b1) ->
    (match q with
     | Zero -> Gt
     | Inp (c2, b2) ->
       (match name_compare c1 c2 with
        | Eq -> proc_compare b1 b2
        | x -> x)
     | _ -> Lt)
  | Lift (c1, a1) ->
    (match q with
     | Zero -> Gt
     | Inp (_, _) -> Gt
     | Lift (c2, a2) ->
       (match name_compare c1 c2 with
        | Eq -> proc_compare a1 a2
        | x -> x)
     | _ -> Lt)
  | Drop x1 ->
    (match q with
     | Drop x2 -> name_compare x1 x2
     | Par (_, _) -> Lt
     | _ -> Gt)
  | Par (a1, b1) ->
    (match q with
     | Par (a2, b2) ->
       (match proc_compare a1 a2 with
        | Eq -> proc_compare b1 b2
        | x -> x)
     | _ -> Gt)

(** val name_compare : name -> name -> comparison **)

and name_compare x y =
  match x with
  | Var n -> (match y with
              | Var m -> Nat.compare n m
              | Quote _ -> Lt)
  | Quote p -> (match y with
                | Var _ -> Gt
                | Quote q -> proc_compare p q)

(** val pleb : proc -> proc -> bool **)

let pleb x y =
  match proc_compare x y with
  | Gt -> False
  | _ -> True

(** val flatten_par : proc -> proc list **)

let rec flatten_par p = match p with
| Zero -> Nil
| Par (a, b) -> app (flatten_par a) (flatten_par b)
| _ -> Cons (p, Nil)

(** val insert_proc : proc -> proc list -> proc list **)

let rec insert_proc x l = match l with
| Nil -> Cons (x, Nil)
| Cons (y, ys) ->
  (match pleb x y with
   | True -> Cons (x, l)
   | False -> Cons (y, (insert_proc x ys)))

(** val sort_par : proc list -> proc list **)

let sort_par l =
  fold_right insert_proc Nil l

(** val rebuild : proc list -> proc **)

let rec rebuild = function
| Nil -> Zero
| Cons (x, xs) ->
  (match xs with
   | Nil -> x
   | Cons (_, _) -> Par (x, (rebuild xs)))

(** val norm_par : proc -> proc **)

let norm_par p =
  rebuild (sort_par (flatten_par p))

(** val canon : proc -> proc **)

let rec canon = function
| Zero -> Zero
| Inp (c, b) -> Inp ((canon_name c), (canon b))
| Lift (c, a) -> Lift ((canon_name c), (canon a))
| Drop x -> Drop (canon_name x)
| Par (a, b) -> norm_par (Par ((canon a), (canon b)))

(** val canon_name : name -> name **)

and canon_name = function
| Var n -> Var n
| Quote p -> (match canon p with
              | Drop y -> y
              | x0 -> Quote x0)

(** val proc_beq : proc -> proc -> bool **)

let rec proc_beq p q =
  match p with
  | Zero -> (match q with
             | Zero -> True
             | _ -> False)
  | Inp (c1, b1) ->
    (match q with
     | Inp (c2, b2) ->
       (match name_beq c1 c2 with
        | True -> proc_beq b1 b2
        | False -> False)
     | _ -> False)
  | Lift (c1, a1) ->
    (match q with
     | Lift (c2, a2) ->
       (match name_beq c1 c2 with
        | True -> proc_beq a1 a2
        | False -> False)
     | _ -> False)
  | Drop x1 -> (match q with
                | Drop x2 -> name_beq x1 x2
                | _ -> False)
  | Par (a1, b1) ->
    (match q with
     | Par (a2, b2) ->
       (match proc_beq a1 a2 with
        | True -> proc_beq b1 b2
        | False -> False)
     | _ -> False)

(** val name_beq : name -> name -> bool **)

and name_beq x y =
  match x with
  | Var n -> (match y with
              | Var m -> Nat.eqb n m
              | Quote _ -> False)
  | Quote p -> (match y with
                | Var _ -> False
                | Quote q -> proc_beq p q)

(** val subst_name : name -> nat -> name -> name **)

let subst_name n y repl =
  match n with
  | Var k -> (match Nat.eqb k y with
              | True -> repl
              | False -> Var k)
  | Quote _ -> n

(** val subst_sem : proc -> nat -> name -> proc **)

let rec subst_sem p y repl =
  match p with
  | Zero -> Zero
  | Inp (c, b) -> Inp ((subst_name c y repl), (subst_sem b y repl))
  | Lift (c, a) -> Lift ((subst_name c y repl), (subst_sem a y repl))
  | Drop n ->
    (match n with
     | Var k ->
       (match Nat.eqb k y with
        | True -> (match repl with
                   | Var _ -> Drop repl
                   | Quote q -> q)
        | False -> Drop n)
     | Quote _ -> Drop n)
  | Par (a, b) -> Par ((subst_sem a y repl), (subst_sem b y repl))

(** val sync : name -> name -> bool **)

let sync x0 x1 =
  name_beq (canon_name x0) (canon_name x1)

(** val selects : proc list -> (proc, proc list) prod list **)

let rec selects = function
| Nil -> Nil
| Cons (x, xs) ->
  Cons ((Pair (x, xs)),
    (map (fun p -> Pair ((fst p), (Cons (x, (snd p))))) (selects xs)))

(** val comm_reduct : proc -> proc -> proc list -> proc option **)

let comm_reduct a b rest =
  match a with
  | Lift (x0, q0) ->
    (match b with
     | Inp (x1, p) ->
       (match sync x0 x1 with
        | True ->
          Some (rebuild (app rest (Cons ((subst_sem p O (Quote q0)), Nil))))
        | False -> None)
     | _ -> None)
  | _ -> None

(** val redexes : proc list -> proc list **)

let redexes comps =
  flat_map (fun ar ->
    flat_map (fun br ->
      match comm_reduct (fst ar) (fst br) (snd br) with
      | Some r -> Cons (r, Nil)
      | None -> Nil) (selects (snd ar)))
    (selects comps)

(** val step : proc -> proc list **)

let step p =
  redexes (flatten_par p)
