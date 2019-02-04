Require Export Basics.

(* QUIZ *)
(** To prove the following theorem, which tactics will we need besides
    [intros] and [reflexivity]? *)
(** (1) none *)
(** (2) [rewrite]
    (3) [destruct]
    (4) both [rewrite] and [destruct]
    (5) can't be done with the tactics we've seen.
*)
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Theorem review1: (orb true false) = true.
Proof. reflexivity. Qed.
(* /QUIZ *)

(* QUIZ *)
(** What about the next one? *) 
Theorem review2: forall b, (orb true b) = true.
Proof. intros b. reflexivity. Qed.
(*  Which tactics do we need besides [intros] and [reflexivity]?  (1)
    none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ *)
(** What if we change the order of the arguments of [orb]? *)
Theorem review3: forall b, (orb b true) = true.
Proof. 
intros b. destruct b.
- reflexivity.
- reflexivity.
Qed.
(*  Which tactics do we need besides [intros] and [reflexivity]?  (1)
    none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ *)
(** What about this one?  *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Theorem review4 : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
(*  (1) none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ *)
(** What about this?  *)
Theorem review5 : forall n : nat, n + 0 = n.
Proof. intros n. induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
 Qed.
(*  (1) none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)