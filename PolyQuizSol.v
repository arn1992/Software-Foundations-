(* QUIZ *)
(** Recall the types of [cons] and [nil]:
       nil : forall X : Type, list X 
       cons : forall X : Type, X -> list X -> list X 
    What is the type of [cons bool true (cons nat 3 (nil nat))]?

    (1) [nat -> list nat -> list nat]

    (2) [forall (X:Type), X -> list X -> list X]

    (3) [list nat]
    
    (4) [list bool]

    (5) No type can be assigned.
*)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fail Check (cons bool true (cons nat 3 (nil nat))).

(* The command has indeed failed with message:
The term "cons nat 3 (nil nat)" has type "list nat"
while it is expected to have type "list bool". *)

(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [repeat]: *)
      Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
        match count with
        | 0 => nil X
        | S count' => cons X x (repeat X x count')
        end.
(*  What is the type of [repeat?

    (1) [nat -> nat -> list nat]

    (2) [X -> nat -> list X]

    (3) [forall (X Y:Type), X -> nat -> list Y]

    (4) [forall (X:Type), X -> nat -> list X]

    (5) No type can be assigned.

*)

Check repeat.
(* repeat
     : forall X : Type, X -> nat -> list X *)
(* /QUIZ *)

(* QUIZ *)
(** What is the type of [repeat nat 1 2]?

    (1) [list nat]

    (2) [forall (X:Type), X -> nat -> list X]

    (3) [list bool]

    (4) No type can be assigned.

*)
Check (repeat nat 1 2).
Arguments nil {X}.
Arguments cons {X} _ _.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Check (repeat nat 1 2).
(* repeat nat 1 2
     : list nat *)

(* /QUIZ *)

(* QUIZ *)

(** Which type does Coq assign to the following expression?
    [1;2;3]
    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned 
*)

Check [1;2;3].
(* [1; 2; 3]
     : list nat *)
(* /QUIZ *)

(* QUIZ *)
(** Which type does Coq assign to the following expression?
    [3 + 4] ++ nil
    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check @app.
(* app
     : forall X : Type, list X -> list X -> list X *)

Check ([3 + 4] ++ nil).
(* [3 + 4] ++ [ ]
     : list nat *)
(* /QUIZ *)

(* QUIZ *)
(** What about this one?
    [andb true false ++ nil]
    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)

Fail Check [andb true false ++ nil].
(* The command has indeed failed with message:
The term "(true && false)%bool" has type "bool"
while it is expected to have type "list ?X0" *)

(* /QUIZ *)

(* QUIZ *)
(** What about this one?
    [1; nil]
    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

Fail Check [1;nil].
(* The command has indeed failed with message:
The term "[[ ]]" has type "list (list ?X)" while it is expected to have type
 "list nat". *)

(* /QUIZ *)

(* QUIZ *)
(** What about this one?

        [[1]; nil]


    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
 *)

Check [[1]; nil].
(* [[1]; [ ]]
     : list (list nat) *)

(* /QUIZ *)

(* QUIZ *)
(** And what about this one?

         [1] :: [nil]


    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

Check [1] :: [nil].
(* [[1]; [ ]]
     : list (list nat) *)

(* /QUIZ *)

(* QUIZ *)
(** What about this one?

        @nil bool


    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

Check (@nil bool).
(* [ ]
     : list bool *)

(* /QUIZ *)

(* QUIZ *)
(** What about this one?

        nil bool


    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

Fail Check (nil bool).

(* The command has indeed failed with message:
Illegal application (Non-functional construction): 
The expression "[ ]" of type "list ?X" cannot be applied to the term
 "bool" : "Set" *)

(* /QUIZ *)

(* QUIZ *)
(** What about this one?
   [@nil 3]
    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)
Check nil.
Check @nil.
Check (@nil nat).

Fail Check (@nil 3).
(* The command has indeed failed with message:
The term "3" has type "nat" while it is expected to have type "Type". *)

(* /QUIZ *)

(* QUIZ *)
(** Recall the definition of [map]: *)
      Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
                   : (list Y) :=
        match l with
        | []     => []
        | h :: t => (f h) :: (map f t)
        end.
(*    What is the type of [map]?

    (1) [forall X Y : Type, X -> Y -> list X -> list Y]

    (2) [X -> Y -> list X -> list Y]

    (3) [forall X Y : Type, (X -> Y) -> list X -> list Y]

    (4) [forall X : Type, (X -> X) -> list X -> list X]

*)

Check @map.
(* map
     : forall X Y : Type, (X -> Y) -> list X -> list Y *)

(* /QUIZ *)

(* QUIZ *)
(** Recall that [evenb] has type [nat -> bool].  

    What is the type of [map evenb]?

    (1) [forall X Y : Type, (X -> Y) -> list X -> list Y]

    (2) [list nat -> list bool]

    (3) [list nat -> list Y]

    (4) [forall Y : Type, list nat -> list Y]

*)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Check (map evenb).

(* map evenb
     : list nat -> list bool *)

(* /QUIZ *)

(* QUIZ *)
(** Here is the definition of [fold] again: *)
Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*    What is the type of [fold]?

    (1) [forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y]

    (2) [X -> Y -> (X -> Y -> Y) -> list X -> Y -> Y]

    (3) [forall X Y : Type, X -> Y -> Y -> list X -> Y -> Y]

    (4) [X -> Y->  X -> Y -> Y -> list X -> Y -> Y]

*)

Check @fold.

(* fold
     : forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y *)

(* /QUIZ *)

(* QUIZ *)
(** What is the type of [fold plus]?

    (1) [forall X Y : Type, list X -> Y -> Y]

    (2) [nat -> nat -> list nat -> nat -> nat]

    (3) [forall Y : Type, list nat -> Y -> nat]

    (4) [list nat -> nat -> nat]

    (5) [forall X Y : Type, list nat -> nat -> nat]

*)

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Check (fold plus).
(* fold plus
     : list nat -> nat -> nat *)

(* /QUIZ *)

(* QUIZ *)
(** What does [fold plus [1;2;3;4] 0] simplify to?

   (1) [[1;2;3;4]]

   (2) [0]

   (3) [10]

   (4) [[3;7;0]]

*)

Compute (fold plus [1;2;3;4] 0).
(* 10 : nat *)
(* /QUIZ *)
