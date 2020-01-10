(******************************************************************************)
(*     Postcondition-Preserving Fusion of Postorder Tree Transformations      *)
(*                                                                            *)
(* pairwise fusion & binary trees                                             *)
(*                                                                            *)
(* Eleanor Davies, 2019 (using Coq 8.7.0)                                     *)
(******************************************************************************)

(* Modules to import *)
Require Import List.   (* for Forall *)
Require Import Basics. (* for compose *)

(* Notation to make lists look nicer *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(******************************************************************************)
(* Binary Trees and Transformations                                           *)
(******************************************************************************)

(* Arbitrary sets of tree labels *)
Inductive X. (* labels for inner nodes *)
Inductive Y. (* labels for leafs *)

(* Binary tree type *)
Inductive Tree := Leaf : Y -> Tree | Node : X -> Tree -> Tree -> Tree.

(* Get a list of the children of a tree *)
Definition children (t : Tree) : list Tree :=
  match t with
    | Leaf y     => [ ]
    | Node x L R => [L, R]
  end.

(* Apply a tree transformation recursively, with a postorder traversal *)
Fixpoint transform (f : Tree -> Tree) (t : Tree) : Tree :=
  match t with
    | Leaf y     => f (Leaf y)
    | Node x L R => f (Node x (transform f L) (transform f R))
  end.

(* Apply two tree transformations in the same traversal *)
Definition fused (f1 f2 : Tree -> Tree) (t : Tree) : Tree :=
  transform (compose f2 f1) t.

(******************************************************************************)
(* Postconditions                                                             *)
(******************************************************************************)

(* Recursively check a postcondition on a tree *)
Fixpoint check (p : Tree -> Prop) (t : Tree) : Prop :=
  match t with
    | Leaf y     => p (Leaf y)
    | Node x L R => p (Node x L R) /\ check p L /\ check p R
  end.

(* Assert that a tree transformation satisfies its postcondition *)
Definition satisfies (f : Tree -> Tree) (p : Tree -> Prop) : Prop :=
  forall (t : Tree), Forall (check p) (children t) -> check p (f t).

(******************************************************************************)
(* Criteria for Successful Fusion                                             *)
(******************************************************************************)

(* The second tree transformation should preserve the first postcondition *)
Definition FC1 (f2 : Tree -> Tree) (p1 : Tree -> Prop) : Prop :=
  forall (t : Tree), check p1 t -> check p1 (f2 t).

(* Any children introduced by the first tree transformation should maintain *)
(* the second postcondition                                                 *)
Definition FC2 (f1 : Tree -> Tree) (p2 : Tree -> Prop) : Prop :=
  forall (t : Tree), Forall (check p2) (children t)
    -> Forall (check p2) (children (f1 t)).

(* Subject to FC1, the first postcondition will be preserved *)
Lemma L1: forall (f1 f2 : Tree -> Tree) (p1 : Tree -> Prop) (t : Tree),
  satisfies f1 p1 -> FC1 f2 p1 -> check p1 (fused f1 f2 t).
Proof.
  intros.
  induction t; apply H0; apply H; simpl; auto.
Qed.

(* Subject to FC2, the second postcondition will be preserved *)
Lemma L2: forall (f1 f2 : Tree -> Tree) (p2 : Tree -> Prop) (t : Tree),
  satisfies f2 p2 -> FC2 f1 p2 -> check p2 (fused f1 f2 t).
Proof.
  intros.
  induction t; apply H; apply H0; simpl; auto.
Qed.

(* Successful fusion means that subject to our criteria both postconditions *)
(* are fulfilled by the result                                              *)
Theorem successfulFusion:
  forall (f1 f2 : Tree -> Tree) (p1 p2 : Tree -> Prop) (t : Tree),
    satisfies f1 p1 -> satisfies f2 p2 -> FC1 f2 p1 -> FC2 f1 p2
      -> check p1 (fused f1 f2 t) /\ check p2 (fused f1 f2 t).
Proof.
  intros.
  split.
  { apply L1; auto. }
  { apply L2; auto. }
Qed.
