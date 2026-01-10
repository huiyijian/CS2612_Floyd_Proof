Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import ExListLib.ZList.

Import ListNotations.

Local Open Scope Z_scope.

(* 取值范围 [lo,hi] 的整数列表中任意两个相邻元素的间隔至少为 pace *)
(* 用于散列表 *)
Inductive interval_list (pace lo hi : Z): list Z -> Prop :=
  | interval_list_nil: interval_list pace lo hi []
  | interval_list_cons: forall l x,
      interval_list pace lo hi l ->
      lo <= x -> x + pace <= hi -> 
      Forall (fun x' => x + pace < x' \/ x' + pace < x) l ->
      interval_list pace lo hi (x :: l).

Theorem interval_list_bounded_lt:  
  forall l pace lo hi , 
    interval_list pace lo hi l -> pace > 0 ->
    Forall (fun x => lo <= x < hi) l.
Proof.
  intros. 
  induction H; simpl; auto.
  constructor; auto. lia.
Qed.

Theorem interval_list_NoDup:  
  forall l pace lo hi , 
    interval_list pace lo hi l -> 
    pace > 0 -> 
    NoDup l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
  rewrite Forall_forall in H3.
  intro. 
  apply H3 in H4.
  lia. 
Qed.

Theorem interval_list_bounded_le:  
  forall l pace lo hi , 
    interval_list pace lo hi l -> 
    Forall (fun x => lo <= x /\ x + pace <= hi) l.
Proof.
  intros.
  induction H; simpl; constructor; auto.
Qed.

Theorem interval_perm_keep: 
  forall l l1 pace lo hi, 
    interval_list pace lo hi l -> 
    Permutation l l1 -> 
    interval_list pace lo hi l1.
Proof.
  intros.
  induction H0; auto.
  - inversion H; subst.
    constructor; auto.
    rewrite <- H0. auto.
  - pose proof (interval_list_bounded_le _ _ _ _ H).
    assert (Permutation (x :: y :: l) (y :: x :: l)).
    { constructor; auto. }
    rewrite <- H1 in H0.
    inversion H0. subst.
    inversion H ; subst.
    inversion H5 ; subst.
    inversion H6 ; subst.
    inversion H9 ; subst.
    constructor ; auto ; try lia.
    + constructor ; auto ; try lia.
    + constructor ; auto ; try lia.
Qed.

Inductive Zincreasing : list Z -> Prop :=
  | Zincreasing_nil: Zincreasing []
  | Zincreasing_cons: forall x l',
      Zincreasing l' ->
      Forall (fun x' => x <= x') l' ->
      Zincreasing (x :: l').

Fixpoint Zinsert (i : Z) (l : list Z) :=
  match l with
  | [] => [i]
  | h :: t => if Z_le_gt_dec i h then i :: h :: t else h :: Zinsert i t
  end.

Fixpoint Zsort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => Zinsert h (Zsort t)
  end.      

Lemma Zinsert_In : forall x a l, 
  In x (Zinsert a l) <-> In x l \/ x = a.
Proof.
  intros.
  induction l; simpl in * ; split ; intros.
  - destruct H ; auto.
  - destruct H ; auto.
  - destruct (Z_le_gt_dec a a0).
    + destruct H ; auto.
    + destruct H ; auto. rewrite IHl in H.
      destruct H ; auto.
  - destruct (Z_le_gt_dec a a0) ; simpl.
    + destruct H as [ [? | ?] | ?]; auto.
    + rewrite IHl. 
      destruct H as [[? |?] | ?] ; auto.
Qed. 

Theorem Zsort_Zincreasing : forall l, 
  Zincreasing (Zsort l).
Proof.
  intros.
  induction l ; simpl in *; auto.
  - constructor.
  - remember (Zsort l) as l1.
    clear Heql1 l. rename l1 into l. 
    induction l; simpl in * ; auto.
    + constructor ; auto.
    + destruct (Z_le_gt_dec a a0).
      * constructor ; auto.
        inversion IHl ; subst.
        constructor ; auto.
        rewrite Forall_forall in *.
        intros.
        specialize (H2 _ H).
        lia.
      * inversion IHl ; subst.
        constructor ; auto.
        rewrite Forall_forall in *.
        intros.
        rewrite Zinsert_In in H.
        destruct H ; auto.
        lia.
Qed.

Lemma Zinsert_perm : forall x l, 
  Permutation (x :: l) (Zinsert x l).
Proof.
  intros.
  induction l; simpl in * ; auto.
  destruct (Z_le_gt_dec x a).
  - constructor ; auto.
  - rewrite perm_swap. constructor ; auto.
Qed.

Theorem Zsort_perm : forall l, 
  Permutation l (Zsort l).
Proof.
  intros.
  induction l ; simpl in * ; auto.
  apply perm_trans with (l' := a :: Zsort l) ; auto.
  apply Zinsert_perm.
Qed.

Lemma interval_list_compress : 
  forall l pace lo1 hi1 lo2 hi2, 
    interval_list pace lo1 hi1 l -> 
    lo1 <= lo2 -> 
    hi2 <= hi1 -> 
    Forall (fun x => lo2 <= x /\ x + pace <= hi2) l -> 
    interval_list pace lo2 hi2 l.
Proof.
  intros.
  generalize dependent lo2. generalize dependent hi2.
  induction H; intros ; simpl.
  - constructor.
  - constructor ; auto.
    + apply IHinterval_list ; auto.
      inversion H5 ; auto.
    + inversion H5 ; lia.
    + inversion H5 ; lia.
Qed.   

Theorem increasing_interval_list_range : 
  forall l pace lo hi, 
    pace > 0 ->
    lo <= hi -> 
    interval_list pace lo hi l -> 
    Zincreasing l ->
    lo + (Zlength l) * (pace + 1) <= hi + pace + 1.
Proof.
  intros. generalize dependent lo. 
  induction l; simpl ; intros; auto.
  - lia.
  - inversion H2 ; subst.
    inversion H1 ; subst.
    apply Zle_lt_or_eq in H9.
    destruct H9.
    + specialize (IHl H5 (a + pace + 1) (ltac:(lia))).
      rewrite Zlength_cons.
      assert (interval_list pace (a + pace + 1) hi l).
      {  
        apply interval_list_compress with (lo1 := lo) (hi1 := hi) ; auto ; try lia.
        pose proof (interval_list_bounded_le _ _ _ _ H7).
        rewrite Forall_forall in *.
        intros. 
        specialize (H10 _ H9).
        specialize (H4 _ H9).
        specialize (H6 _ H9).
        lia. 
      }
      specialize (IHl H4).
      lia.
    + destruct l. 
      * replace (Zlength [a]) with 1 by auto.
        lia.
      * exfalso. 
        inversion H7; subst.
        inversion H10; subst.
        inversion H6 ; subst.
        lia.
Qed.

Theorem interval_list_range : 
  forall l pace lo hi, 
    pace > 0 ->
    lo <= hi -> 
    interval_list pace lo hi l -> 
    lo + (Zlength l) * (pace + 1) <= hi + pace + 1.
Proof.
  intros.
  pose proof (Zsort_perm l).
  assert (Zlength l = Zlength (Zsort l)).
  {
     rewrite !Zlength_correct.
     rewrite (Permutation_length H2) ; auto.
  }
  rewrite H3.
  apply (increasing_interval_list_range (Zsort l) pace lo hi) ; auto.
  + apply (interval_perm_keep l) ; auto.
  + apply Zsort_Zincreasing.
Qed. 