Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Import ListNotations.

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Lemma insert_perm: forall x l,
  Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l.
  - auto.
  - simpl. destruct (x <=? a) eqn:?.
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. assumption.
Qed.

Lemma sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l.
  - auto.
  - simpl. apply perm_trans with (a :: (sort l)).
    + apply perm_skip. assumption.
    + apply insert_perm.
Qed.