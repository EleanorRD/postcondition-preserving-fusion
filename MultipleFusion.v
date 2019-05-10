(******************************************************************************)
(*     Postcondition-Preserving Fusion of Postorder Tree Transformations      *)
(*                                                                            *)
(* multiple fusion & binary trees                                             *)
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
Fixpoint apply (f : Tree -> Tree) (t : Tree) : Tree :=
  match t with
    | Leaf y     => f (Leaf y)
    | Node x L R => f (Node x (apply f L) (apply f R))
  end.

(* Compose a list of tree transformations *)
Fixpoint composeList (fs : list (Tree -> Tree)) : Tree -> Tree :=
    match fs with
      | [ ]        => fun t : Tree => t
      | cons f fs' => fun t : Tree => compose (composeList fs') f t
    end.

(* Apply two tree transformations in the same traversal *)
Definition applyFused (fs : list (Tree -> Tree)) (t : Tree) : Tree :=
  apply (composeList fs) t.

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

(* Tree transformation f2 should preserve the postcondition p1 *)
Definition FC1 (f2 : Tree -> Tree) (p1 : Tree -> Prop) : Prop :=
  forall (t : Tree), check p1 t -> check p1 (f2 t).

Definition afterFC1 (p : Tree -> Prop) (fs : list (Tree -> Tree)) : Prop :=
    Forall (fun x => FC1 x p) fs.

(* Any children introduced by the tree transformation f1 should maintain *)
(* the postcondition p2                                                  *)
Definition FC2 (f1 : Tree -> Tree) (p2 : Tree -> Prop) : Prop :=
  forall (t : Tree), Forall (check p2) (children t)
    -> Forall (check p2) (children (f1 t)).

Definition beforeFC2 (p : Tree -> Prop) (fs : list (Tree -> Tree)) : Prop :=
    Forall (fun x => FC2 x p) fs.

Lemma unrollComposeList : forall
  (xs ys : list (Tree -> Tree)) (t : Tree),
    composeList (xs ++ ys) t = (composeList ys) ((composeList xs) t).
Proof.
  intros until xs.
  induction xs.
  { auto. }
  { intros. simpl. apply IHxs. }
Qed.

Lemma afterFC1Preserves: forall (fs : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    check p t -> afterFC1 p fs -> check p (composeList (rev fs) t).
Proof.
  intros until p.
  induction fs.
  { auto. }
  { intros.
    inversion_clear H0.
    simpl.
    rewrite unrollComposeList.
    apply H1.
    apply IHfs; auto.
  }
Qed.

Lemma lemAfter:
  forall (after : list (Tree -> Tree)) (f : Tree -> Tree) (p : Tree -> Prop),
    afterFC1 p after -> satisfies f p
      -> forall (t : Tree), check p (applyFused (cons f (rev after)) t).
Proof.
  intros until f.
  intro.
  intro.
  induction after.
  { induction t; apply H0; simpl; auto. }
  { induction t.
    { unfold applyFused.
      unfold apply.
      simpl.
      unfold compose.
      rewrite unrollComposeList.
      inversion_clear H.
      apply H1.
      apply IHafter with (t := Leaf y); auto.
    }
    { unfold applyFused.
      unfold apply.
      fold apply.
      simpl.
      unfold compose.
      rewrite unrollComposeList.
      inversion_clear H.
      apply H1.
      apply afterFC1Preserves; auto.
      apply H0.
      simpl.
      auto.
    }
  }
Qed.

Lemma beforeFC2Preserves: forall (fs : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    Forall (check p) (children t) -> beforeFC2 p fs 
      -> Forall (check p) (children (composeList fs t)).
Proof.
  intros until p.
  induction fs.
  { auto. }
  { intros.
    inversion_clear H0.
    simpl.
    unfold compose.
    apply IHfs; auto.
  }
Qed.

Lemma successfulMultiFusion : forall (before : list (Tree -> Tree))
  (f : Tree -> Tree) (after : list (Tree -> Tree))
  (p : Tree -> Prop) (t : Tree),
    beforeFC2 p before -> afterFC1 p after -> satisfies f p
      -> check p (applyFused (before ++ [f] ++ (rev after)) t).
Proof.
  intros until after.
  induction before.
  { intros. apply lemAfter; auto. }
  { intros.
    unfold applyFused.
    induction t.
    { unfold apply.
      rewrite 2 unrollComposeList.
      simpl.
      unfold compose.
      inversion_clear H.
      apply afterFC1Preserves; auto.
      apply H1.
      apply beforeFC2Preserves; auto.
      apply H2.
      simpl.
      auto.
    }
    { unfold apply.
      fold apply.
      rewrite 2 unrollComposeList.
      simpl.
      unfold compose.
      inversion_clear H.
      apply afterFC1Preserves; auto.
      apply H1.
      apply beforeFC2Preserves; auto.
      apply H2.
      simpl.
      auto.
    }
  }
Qed.


