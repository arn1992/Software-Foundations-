Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(* What is the type of @nil? *)
Check @nil.

(* What is the type of @cons? *)

Check @cons.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

(* What is the type of @length? *)

Check @length.

Definition mynil := @nil nat.

(* What is the type of mynil? *)

Check mynil.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(* What is the type of @repeat'''? (You will need some type inference.) *)

Check @repeat'''.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(* What is the type of (repeat (plus 3) 4)? *)

Check (repeat''' (plus 3) 4).
Check (repeat''' (repeat''' (plus 3)) 4).
(* What is the type of (repeat''' (repeat''' true 3) 2)? *)
Check ((repeat''' true 3)).

Check (repeat''' (repeat''' true 3) 2).

(* What is the value of (repeat''' (repeat''' true 3) 2)? *)

Compute (repeat''' (repeat''' true 3) 2).

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.
Check @pair.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

(* What is the type of [(1,false);(2,false)]? *)

Check [(1,false);(2,false)].

(* What is the type of ([1;2],[false;false])? *)

Check ([1;2],[false;false]).

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(* What is type of (map negb) *)

Check (map negb).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(* What is the type of (map (fun x => leb x 5))? *)

Check (map (fun x => leb x 5)).

(* What is the value of (map (fun x => leb x 5) [1;7;6;3;5])? *)

Compute (map (fun x => leb x 5) [1;7;6;3;5]).
Check (map (fun x => leb x 5) [1;7;6;3;5]).