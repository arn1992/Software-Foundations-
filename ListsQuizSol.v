Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Inductive id : Type :=
  | Id (n : nat).
Check id.
Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
Check beq_id.
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
Check Some.
Check None.
Inductive natlist : Type :=
  | nil  
  | cons (n : nat) (l : natlist).
Check nil.
Check cons.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  Admitted.

(***********************)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
Check record.
Check empty.
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

(**************************************************************)
(** What does the following function do? *)

Fixpoint foo (n:nat) : natlist :=
  match n with
  | 0 => nil  
  | S n' => n :: (foo n')
  end.

Compute (foo 5).



(** To prove the following theorem, which tactics will we need besides
    [intros], [simpl], [rewrite] and [reflexivity]?  (1) none (2) [destruct],
    (3) [induction on n], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
*)
    Theorem foo1 : forall n :nat, forall l: natlist, 
    repeat n 0 = l -> length l = 0.
Proof.
intros n l. simpl. intros H. rewrite <- H. simpl. reflexivity. Qed.

(** What about the next one? 
    Which tactics do we need besides [intros], [simpl], [rewrite] and
    [reflexivity]?  (1) none (2) [destruct],
    (3) [induction on m], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
*)
    Theorem foo2 :  forall n m:nat, forall l: natlist,
    repeat n m = l -> length l = m.
Proof.
  intros n m l. 
  destruct l as [| n' l'].
  - simpl.
Restart.
  intros n m l. 
  destruct m as [| m'].
  - simpl. intros H. rewrite <- H. simpl. reflexivity.
  - simpl. intros H. rewrite <- H. simpl.
Restart.
intros n m l. induction l as [|n' l' IHl'].
- simpl. destruct m.
  + simpl. intros H. reflexivity.
  + simpl.
Restart.
intros n m. induction m as [| m' IHm']. 
  - intros l. simpl. intros H. rewrite <- H. simpl. reflexivity.
  - simpl. intros l H. rewrite <- H. simpl. rewrite -> IHm'.
    + reflexivity.
    + reflexivity.
Qed.



(** What about the next one? 
    Which tactics do we need besides [intros], [simpl], [rewrite] and
    [reflexivity]?  (1) none (2) [destruct],
    (3) [induction on n], (4) [induction on l1], (5) [induction on l2], 
    or (6) can't be done with the tactics we've seen.
*)
    Theorem foo3 :  forall n :nat, forall l1 l2: natlist,
    l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.
Proof.
  intros n l1 l2 H.
  destruct l1 as [|n' l1'].
  - rewrite <- H. simpl. reflexivity.
  - rewrite <- H. simpl. reflexivity.
Qed.


(** Is the following claim true or false? *)
Theorem quiz1 : forall (d : partial_map)
                       (x : id) (v: nat),
  find x (update d x v) = Some v.

Proof.
  intros d x v. simpl.
  assert (H: forall (y:id), beq_id y y = true).
  { intros y. destruct y.  simpl. rewrite <- eqb_refl. reflexivity. }
  rewrite -> H. reflexivity.
Qed.
(** (1) True
    (2) False 
*)


(** Is the following claim true or false? *)

Theorem quiz2 : forall (d : partial_map)
                       (x y : id) (o: nat),
  beq_id x y = false ->
  find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl. rewrite -> H.  reflexivity.
Qed.
(** (1) True
    (2) False 
*)