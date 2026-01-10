Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import ListLib.Core.
Require Import ListLib.Positional.
Require Import ListLib.Basics.
Import ListNotations.

Definition nperm (s : list nat) : Prop := Permutation (seq O (length s)) s.

Definition apply_perm {A : Type} (s : list nat) (l : list A) (d : A) : list A :=
  map (fun n => nth n l d) s.

Definition identity_perm (n : nat) := seq O n.

Fixpoint find_index (l : list nat) (n : nat) : nat :=
  match l with
  | nil => O
  | n' :: l' =>
    if (n' =? n)%nat
    then O
    else S (find_index l' n)
  end.

Definition inverse_nperm (s : list nat) :=
  map (find_index s) (seq O (length s)).

Lemma identity_perm_is_is_nperm : forall n, 
  nperm (identity_perm n).
Proof.
  intros. unfold nperm, identity_perm.
  rewrite length_seq.
  apply Permutation_refl.
Qed.

Lemma identity_perm_refl {A: Type} (d: A) : 
  forall (n : nat) (l : list A),
    length l = n ->
    apply_perm (identity_perm n) l d = l.
Proof.
  unfold apply_perm. induction n; simpl; intros.
  - destruct l; auto. simpl in H. lia.
  - destruct l; simpl in *; try lia.
    inversion H. subst. f_equal.
    rewrite <- seq_shift. rewrite map_map. auto.
Qed.


Lemma find_index_nth : 
  forall l n d,
    NoDup l ->
    n < length l ->
    find_index l (nth n l d) = n.
Proof.
  intros. generalize dependent l.
  induction n; intros; destruct l; simpl in *; auto; try lia.
  - rewrite Nat.eqb_refl. auto.
  - inversion H. subst.
    assert (n < length l) by lia.
    rewrite (IHn _ H4 H1).
    destruct (n0 =? nth n l d) eqn:E; auto.
    rewrite Nat.eqb_eq in E. subst.
    contradict H3.
    apply (nth_In l d H1).
Qed.

Lemma nth_find_index : 
  forall l n d,
    In n l ->
    nth (find_index l n) l d = n.
Proof.
  intros. generalize dependent n.
  induction l; intros; simpl in *.
  - contradiction.
  - destruct (a =? n) eqn:E.
    + rewrite Nat.eqb_eq in E. auto.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      apply IHl. auto.
Qed.

Lemma map_nth_len {A B: Type} : 
  forall (f : A -> B) l n dx dy,
    n < length l ->
    nth n (map f l) dx = f (nth n l dy).
Proof.
  intros. generalize dependent l.
  induction n; intros.
  - destruct l; simpl in *; auto. lia.
  - destruct l; simpl in *; try lia.
    apply IHn. lia.
Qed.

Lemma map_find_index_same : 
  forall l,
    NoDup l ->
    map (find_index l) l = seq O (length l).
Proof.
  intros. apply (nth_ext _ _ O O).
  - rewrite length_map. rewrite length_seq. auto.
  - intros. rewrite length_map in H0.
    rewrite seq_nth; auto. simpl.
    rewrite (map_nth_len _ _ _ _ O); auto.
    rewrite find_index_nth; auto.
Qed.

Lemma length_apply_perm {A: Type} (d: A): 
  forall s l,
    length (apply_perm s l d) = length s.
Proof.
  intros. unfold apply_perm. rewrite length_map. auto.
Qed.

Lemma nperm_range : 
  forall s n0 d,
    nperm s ->
    n0 < (length s) ->
    nth n0 s d < (length s).
Proof.
  intros.
  pose proof (nth_In s d H0).
  unfold nperm in H. symmetry in H.
  apply (Permutation_in _ H) in H1.
  apply in_seq in H1. simpl in *. lia.
Qed.

Lemma nperm_NoDup : 
  forall s,
    nperm s -> NoDup s.
Proof.
  intros.
  apply (Permutation_NoDup H).
  apply seq_NoDup.
Qed.

Lemma map_apply_perm {A B: Type} (dx: A): 
  forall s (f : A -> B) l,
    apply_perm s (map f l) (f dx) = map f (apply_perm s l dx).
Proof.
  intros. unfold apply_perm. rewrite map_map.
  apply map_ext. intros. apply map_nth.
Qed.

Lemma find_index_range : forall l n,
  In n l ->
  find_index l n < length l.
Proof.
  intros. induction l; simpl in *.
  - contradiction.
  - destruct (a =? n) eqn:E.
    + lia.
    + rewrite Nat.eqb_neq in E. destruct H; try congruence.
      specialize (IHl H). lia.
Qed.

Lemma inverse_nperm_nperm : forall s,
  nperm s ->
  nperm (inverse_nperm s).
Proof.
  intros. unfold inverse_nperm, nperm.
  pose proof (Permutation_map (find_index s) H).
  rewrite map_find_index_same in H0.
  - symmetry. rewrite length_map. rewrite length_seq. auto.
  - apply nperm_NoDup. auto.
Qed.

Definition apply_perm_inverse_l {A: Type} (d: A): 
  forall s l,
    nperm s ->
    length l = length s ->
    apply_perm s (apply_perm (inverse_nperm s) l d) d = l.
Proof.
  intros. unfold apply_perm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite length_map. auto. }
  intros. rewrite length_map in H1.
  rewrite <- H0 in H1. rewrite map_map.
  rewrite (map_nth_len _ _ n _ O) by lia.
  rewrite (map_nth_len _ _ _ _ O).
  2:{ rewrite length_seq. apply nperm_range; auto. lia. }
  rewrite seq_nth.
  2:{ apply nperm_range; auto. lia. }
  simpl. rewrite find_index_nth; auto.
  { apply nperm_NoDup. auto. }
  { lia. }
Qed.

Definition apply_perm_inverse_r {A: Type} (d: A): 
  forall s l,
  nperm s ->
  length l = length s ->
  apply_perm (inverse_nperm s) (apply_perm s l d) d = l.
Proof.
  intros. unfold apply_perm, inverse_nperm; simpl.
  apply (nth_ext _ _ d d).
  { rewrite ! length_map. rewrite length_seq. auto. }
  intros. rewrite length_map in H1. rewrite length_map in H1.
  rewrite length_seq in H1.
  rewrite (map_nth_len _ _ n _ O).
  2:{ rewrite length_map. rewrite length_seq. lia. }
  rewrite (map_nth_len _ _ n _ O).
  2:{ rewrite length_seq. lia. }
  rewrite (map_nth_len _ _ _ _ O).
  2:{ rewrite seq_nth; auto. simpl.
      apply find_index_range.
      apply (Permutation_in _ H). apply in_seq. lia. }
  rewrite seq_nth by lia. simpl.
  rewrite nth_find_index; auto.
  { apply (Permutation_in _ H). apply in_seq. lia. }
Qed.

Lemma apply_perm_is_permutation {A: Type} (d: A): 
  forall (s : list nat) (l : list A),
  nperm s ->
  length l = length s ->
  Permutation l (apply_perm s l d).
Proof.
  intros. rewrite <- (identity_perm_refl d (length l) l) at 1; auto.
  unfold apply_perm. apply Permutation_map. rewrite H0. apply H.
Qed.

Lemma Forall2_nperm_congr {A B: Type} (dx: A) (dy: B): 
  forall (P : A -> B -> Prop) xs ys s,
  nperm s ->
  length xs = length s ->
  Forall2 P xs ys ->
  Forall2 P (apply_perm s xs dx) (apply_perm s ys dy).
Proof.
  intros * HPerm **.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy) in H0.
  apply (Forall2_nth_iff _ _ _ _ _ dx dy).
  destruct H0. split.
  - rewrite ! length_apply_perm; auto.
  - intros. unfold apply_perm.
    rewrite length_apply_perm in H2; auto.
    rewrite (map_nth_len _ _ n dx O) by lia.
    rewrite (map_nth_len _ _ n dy O) by lia.
    apply H1; auto.
    pose proof (nperm_range s _ O HPerm H2). lia.
Qed.

Lemma Forall2_nperm_congr_iff {A B: Type} (dx: A) (dy: B): 
  forall (P : A -> B -> Prop) xs ys s,
  nperm s ->
  length xs = length s ->
  length ys = length s ->
  Forall2 P xs ys <->
  Forall2 P (apply_perm s xs dx) (apply_perm s ys dy).
Proof.
  intros * HPerm **. split; intros.
  - apply Forall2_nperm_congr; auto.
  - rewrite <- (apply_perm_inverse_r dx s xs HPerm H).
    rewrite <- (apply_perm_inverse_r dy s ys HPerm H0).
    apply Forall2_nperm_congr; auto.
    + apply inverse_nperm_nperm. auto.
    + rewrite length_apply_perm. unfold inverse_nperm. rewrite length_map.
      rewrite length_seq. auto.
Qed.

Definition swap_seq2 (n1 n2 n3 : nat) :=
  seq 0 n1 ++ 1 + n1 + n2 :: seq (1 + n1) n2 ++ n1 :: seq (2 + n1 + n2) n3.

Lemma swap_seq2_is_nperm : forall (n1 n2 n3 : nat), nperm (swap_seq2 n1 n2 n3).
Proof.
  intros. unfold nperm, swap_seq2.
  rewrite ! length_app. rewrite length_seq. simpl.
  replace (2 + n1 + n2 + n3) with (n1 + (1 + n2 + (1 + n3))) by lia.
  rewrite (seq_app n1). apply Permutation_app; [apply Permutation_refl | ].
  simpl. rewrite length_app. simpl. rewrite ! length_seq.
  rewrite (seq_app n2). simpl.
  rewrite ! (Permutation_app_comm (seq (S n1) n2)).
  simpl. apply perm_swap.
Qed.

Lemma swap_nperm_apply_perm {A: Type} (d: A): 
  forall l1 i l2 j l3,
  apply_perm (swap_seq2 (length l1) (length l2) (length l3))
    (l1 ++ i :: l2 ++ j :: l3) d =
    (l1 ++ j :: l2 ++ i :: l3).
Proof.
  intros. unfold apply_perm, swap_seq2; simpl.
  rewrite map_app. simpl. rewrite map_app. simpl.
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ n d O); auto.
      + rewrite seq_nth; auto. simpl. apply app_nth1. auto.
      + rewrite length_seq. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (S (length l1 + length l2) - length l1) with (S (length l2)) by lia.
    simpl. rewrite app_nth2; try lia.
    replace (length l2 - length l2) with 0 by lia. simpl. auto. }
  f_equal.
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ _ d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (length l1 + n) - length l1) with (S n) by lia.
        simpl. apply app_nth1. auto.
      + rewrite length_seq. auto. }
  f_equal.
  { rewrite app_nth2; try lia.
    replace (length l1 - length l1) with 0 by lia. simpl. auto. }
  { apply (nth_ext _ _ d d).
    - rewrite length_map. rewrite length_seq. auto.
    - intros.
      rewrite length_map in H. rewrite length_seq in H.
      rewrite (map_nth_len _ _ _  d O); auto.
      + rewrite seq_nth; auto. simpl. rewrite app_nth2; try lia.
        replace (S (S (length l1 + length l2 + n)) - length l1) with (2 + length l2 + n) by lia.
        simpl. rewrite app_nth2; try lia.
        replace (S (length l2 + n) - length l2) with (S n) by lia.
        simpl. auto.
      + rewrite length_seq. auto. }
Qed.

Definition swap_seq (n1 n2 : nat) :=
  seq n1 n2 ++ seq 0 n1.

Definition swap_seq_is_nperm : forall (n1 n2 : nat),
  nperm (swap_seq n1 n2).
Proof.
  intros. unfold nperm, swap_seq.
  rewrite length_app. rewrite ! length_seq.
  replace (n2 + n1) with (n1 + n2) by lia.
  rewrite seq_app. simpl. apply Permutation_app_comm.
Defined.

Lemma swap_seq_apply_perm : forall (A : Type) l1 l2 (d : A),
  apply_perm (swap_seq (length l1) (length l2))
    (l1 ++ l2) d = (l2 ++ l1).
Proof.
  intros. unfold apply_perm, swap_seq; simpl.
  rewrite map_app. simpl. f_equal.
  - apply (nth_ext _ _ d d).
    { rewrite length_map. rewrite length_seq. auto. }
    intros. rewrite length_map in H. rewrite length_seq in H.
    rewrite (map_nth_len _ _ n d 0).
    2:{ rewrite length_seq. lia. }
    rewrite seq_nth; auto. rewrite app_nth2; try lia.
    replace (length l1 + n - length l1) with n by lia.
    auto.
  - apply (nth_ext _ _ d d).
    { rewrite length_map. rewrite length_seq. auto. }
    intros. rewrite length_map in H. rewrite length_seq in H.
    rewrite (map_nth_len _ _ n d 0).
    2:{ rewrite length_seq. lia. }
    rewrite seq_nth; auto. simpl. rewrite app_nth1; try lia.
    auto.
Qed.