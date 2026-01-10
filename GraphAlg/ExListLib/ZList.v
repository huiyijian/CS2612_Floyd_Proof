Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import ListLib.Positional.

Import ListNotations.

Fixpoint Zseq (start : Z) (len : nat) : list Z :=
  match len with
  | 0 => nil
  | S len' => start :: Zseq (Z.succ start) len'
  end.

Lemma Zseq_length : forall s n,
  length (Zseq s n) = n.
Proof.
  intros. revert s. induction n; intros; simpl; auto.
Qed.

Lemma Zseq_nth : forall start len n,
  n < len ->
  (nth n (Zseq start len) 0 = start + (Z.of_nat n))%Z.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros.
  - simpl. destruct len; [lia | ]. simpl. lia.
  - destruct len; [lia | ]. simpl. rewrite IHn; lia.
Qed.

Lemma Zseq_firstn : forall start len n,
  (n <= len)%nat ->
  firstn n (Zseq start len) = Zseq start n.
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl; auto.
  destruct len; [lia | ].
  simpl. rewrite IHn; auto. lia.
Qed.

Lemma Zseq_skipn : forall start len n,
  skipn n (Zseq start len) = Zseq (start + Z.of_nat n) (len - n).
Proof.
  intros. generalize dependent len. revert start.
  induction n; intros; simpl.
  - f_equal; lia.
  - destruct len; simpl; auto.
    rewrite IHn; auto. f_equal; lia.
Qed.

Lemma Zseq_app : forall start len1 len2,
  Zseq start (len1 + len2) = Zseq start len1 ++ Zseq (start + (Z.of_nat len1)) len2.
Proof.
  intros start len1. revert start.
  induction len1; intros; simpl in *.
  - f_equal. lia.
  - rewrite IHlen1. f_equal. f_equal. f_equal. lia.
Qed.

Local Open Scope Z_scope.

Definition Znth {A} (n: Z) (l: list A) (a0: A): A := nth (Z.to_nat n) l a0.

Fixpoint replace_nth {A: Type} (n: nat) (a: A) (l: list A): list A :=
  match l with
  | nil => nil
  | a0 :: l0 =>
      match n with
      | O => a :: l0
      | S n0 => a0 :: replace_nth n0 a l0
      end
  end.

Definition replace_Znth {A} (n: Z) (a: A) (l: list A): list A :=
  replace_nth (Z.to_nat n) a l.

Lemma Znth0_cons: forall {A} (a: A) l a0,
  Znth 0 (a :: l) a0 = a.
Proof.
  intros.
  unfold Znth.
  simpl.
  reflexivity.
Qed.

Lemma Znth_cons: forall {A} (n: Z) (a: A) l a0,
  n > 0%Z ->
  Znth n (a :: l) a0 = Znth (n - 1) l a0.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma replace_Znth_cons: forall {A} n (a b: A) l,
  n > 0 ->
  replace_Znth n a (b :: l) =
  b :: replace_Znth (n - 1) a l.
Proof.
  intros.
  unfold replace_Znth.
  assert (Z.to_nat n = S (Z.to_nat (n - 1))) by lia.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma replace_nth_app_l : forall {A} n (a: A) l1 l2,
  (n < length l1)%nat ->
  replace_nth n a (l1 ++ l2) = replace_nth n a l1 ++ l2.
Proof.
  intros.
  generalize dependent l1.
  revert l2.
  induction n.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + intros.
    destruct l1; simpl in *; try lia.
    simpl.
    f_equal.
    apply IHn.
    lia. 
Qed. 

Lemma replace_nth_app_r: forall {A} n (a: A) l1 l2,
  (n >= length l1)%nat ->
  replace_nth n a (l1 ++ l2) = replace_nth n a l1 ++ replace_nth (n - length l1) a l2.
Proof.
  intros.
  generalize dependent l1.
  revert l2.
  induction n; intros.
  + destruct l1; simpl in *; try lia.
    simpl.
    reflexivity.
  + destruct l1; simpl in *; [ | rewrite IHn ; auto; try lia].
    reflexivity. 
Qed. 

Lemma replace_Znth_app_l : forall {A} n (a: A) l1 l2,
  (0 <= n) -> 
  (n < Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ l2.
Proof.
  intros.
  unfold replace_Znth.
  apply replace_nth_app_l.
  rewrite Zlength_correct in H0.
  lia.
Qed. 

Lemma replace_Znth_app_r : forall {A} n (a: A) l1 l2,
  (n >= Zlength l1) ->
  replace_Znth n a (l1 ++ l2) = replace_Znth n a l1 ++ replace_Znth (n - Zlength l1) a l2.
Proof. 
  intros.
  unfold replace_Znth.
  rewrite Zlength_correct in *.
  replace (Z.to_nat (n - Z.of_nat (length l1))) with (Z.to_nat n - length l1)%nat by lia.
  rewrite replace_nth_app_r ; try lia.
  auto.
Qed.

Lemma replace_Znth_Znth: forall {A} n l (a0: A),
  replace_Znth n (Znth n l a0) l = l.
Proof.
  intros.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat n); clearbody m; clear n.
  revert m; induction l; simpl; intros.
  + destruct m; reflexivity.
  + destruct m.
    - reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
Qed.

Lemma replace_Znth_nothing : forall {A} n (l: list A) (a: A),
  n >= Zlength l -> replace_Znth n a l = l.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold replace_Znth.
  assert (Z.to_nat n >= length l)%nat by lia.
  clear H. 
  set (m := Z.to_nat n) in *; clearbody m ; clear n.
  generalize dependent l.
  induction m; intros. 
  + destruct l; simpl in * ; auto ; lia.
  + destruct l; simpl in * ; auto.
    rewrite IHm ; auto. lia. 
Qed.

Definition Zsublist {A: Type} (lo hi: Z) (l: list A): list A :=
  skipn (Z.to_nat lo) (firstn (Z.to_nat hi) l).

Lemma Zsublist_split_app_l : forall {A : Type} lo hi (l1 l2 : list A),
  0 <= lo <= hi -> hi <= Z.of_nat (length l1) -> Zsublist lo hi (l1 ++ l2) = Zsublist lo hi l1.
Proof.
  intros.
  unfold Zsublist.
  rewrite firstn_app.
  simpl. 
  replace (Z.to_nat hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto. 
Qed. 

Lemma Zsublist_single : forall {A : Type} n (l : list A) (a : A),
  0 <= n < Z.of_nat (length l) -> Zsublist n (n + 1) l = [Znth n l a].
Proof.
  intros.
  rewrite (firstn_skipSn a (Z.to_nat n) l) at 1; try lia.
  unfold Znth. 
  unfold Zsublist.
  rewrite firstn_app.
  assert (length (firstn (Z.to_nat n) l) = Z.to_nat n) by (rewrite length_firstn; lia).
  rewrite firstn_all2; try lia. 
  replace (Z.to_nat (n + 1) - length (firstn (Z.to_nat n) l))%nat with 1%nat by lia.
  rewrite skipn_app.
  replace (Z.to_nat n - length (firstn (Z.to_nat n) l))%nat with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed. 

Lemma Zsublist_split: forall {A : Type} lo hi mid (l : list A),
  0 <= lo <= mid -> mid <= hi <= Z.of_nat (length l) ->
  Zsublist lo hi l = Zsublist lo mid l ++ Zsublist mid hi l.
Proof.
  intros.
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  remember (firstn (Z.to_nat hi) l) as l1.
  remember (skipn (Z.to_nat hi) l) as l2.
  assert (Z.of_nat (length l1) = hi).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  assert (length l = length l1 + length l2)%nat.
  {
    rewrite Heql1, Heql2.
    rewrite length_firstn, length_skipn.
    lia.
  }
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite Zsublist_split_app_l ; try lia).
  unfold Zsublist.
  replace (Z.to_nat hi)%nat with (length l1) by lia.
  assert (mid <= Z.of_nat (length l1)) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2 ; try lia.
  rename l1 into l. 
  rewrite <- (firstn_skipn (Z.to_nat lo) l).
  remember (firstn (Z.to_nat lo) l) as l1.
  remember (skipn (Z.to_nat lo) l) as l2.
  assert (Z.of_nat (length l1) = lo).
  {
    rewrite Heql1.
    rewrite length_firstn.
    lia.
  }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2 ; try lia.
  replace (Z.to_nat lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2 ; try lia).
  rewrite! app_nil_l.
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma Zlength_nonneg:
 forall {A} (l: list A), 0 <= Zlength l.
Proof.
  intros. rewrite Zlength_correct. lia.
Qed.

Lemma Zlength_app: forall {A} (l1 l2: list A),
  Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof.
  intros.
  rewrite !Zlength_correct.
  rewrite length_app.
  lia.
Qed.

Lemma Zlength_app_cons: forall {A} (l: list A) a,
  Zlength (l ++ (a :: nil)) = Zlength l + 1.
Proof.
  intros. 
  rewrite Zlength_app , Zlength_cons, Zlength_nil. 
  lia.
Qed.

Lemma app_Znth1:
  forall A (l l': list A) (i:Z) (d: A),
  0 <= i < Zlength l -> Znth i (l++l') d = Znth i l d.
Proof.
  intros.
  unfold Znth.
  assert (Z.to_nat i < length l)%nat by (pose proof Zlength_correct l; lia).
  set (j := Z.to_nat i) in *; clearbody j; clear i H.
  apply app_nth1; auto.
Qed.

Lemma app_Znth2:
  forall A (l l': list A) (i:Z) (d: A),
  i >= Zlength l -> Znth i (l++l') d = Znth (i-Zlength l) l' d.
Proof.
  intros.
  unfold Znth.
  pose proof (Zlength_nonneg l).
  assert (Z.to_nat i >= length l)%nat by
    (pose proof Zlength_correct l; lia).
  replace (Z.to_nat (i - Zlength l)) with (Z.to_nat i - length l)%nat
    by (pose proof Zlength_correct l; lia).
  apply app_nth2; auto.
Qed.

Lemma Znth_Zsublist:
  forall {A} lo i hi (l: list A) (d: A),
  0 <= lo ->
  0 <= i < hi-lo ->
  Znth i (Zsublist lo hi l) d = Znth (i+lo) l d.
Proof.
  intros.
  unfold Zsublist, Znth.
  rewrite nth_skipn.
  rewrite nth_firstn by lia.
  f_equal.
  lia.
Qed.

Lemma Znth_Zsublist0:
  forall {A} i hi (l: list A) (d: A),
    0 <= i < hi ->
    Znth i (Zsublist 0 hi l) d = Znth i l d.
Proof.
  intros.
  rewrite Znth_Zsublist by lia.
  f_equal.
  lia.
Qed.

Lemma Znth_indep:
  forall {A} (l : list A) n (d d' : A),
    0 <= n < Zlength l ->
    Znth n l d = Znth n l d'.
Proof.
  intros.
  unfold Znth.
  apply nth_indep.
  pose proof Zlength_correct l.
  lia.
Qed.

Lemma Zlength_Zsublist:
  forall {A} lo hi (l: list A),
    0 <= lo <= hi /\ hi <= Zlength l ->
    Zlength (Zsublist lo hi l) = hi-lo.
Proof.
  intros.
  pose proof Zlength_correct l.
  rewrite Zlength_correct.
  unfold Zsublist.
  rewrite length_skipn.
  rewrite firstn_length_le by lia.
  lia.
Qed.

Lemma Zlength_Zsublist0:
  forall {A} hi (l: list A),
    0 <= hi /\ hi <= Zlength l ->
    Zlength (Zsublist 0 hi l) = hi.
Proof.
  intros.
  rewrite Zlength_Zsublist by lia.
  lia.
Qed.

Lemma Zsublist_Zsublist {A} i j k m (l:list A): 
  0<=m -> 0<=k <=i -> 
  i <= j-m ->
  Zsublist k i (Zsublist m j l) = Zsublist (k+m) (i+m) l.
Proof.
  intros.
  unfold Zsublist.
  rewrite ! skipn_firstn_comm.
  rewrite firstn_firstn by lia.
  rewrite skipn_skipn.
  f_equal; [lia | ].
  f_equal; lia.
Qed.

Lemma Zsublist_Zsublist0 {A} i j k (l:list A): 0<=k -> k<=i<=j ->
  Zsublist k i (Zsublist 0 j l) = Zsublist k i l.
Proof. intros. rewrite Zsublist_Zsublist; repeat rewrite Zplus_0_r; trivial; lia. Qed.

Lemma Zsublist_Zsublist00 {A} i j (l:list A): 0<=i<=j ->
  Zsublist 0 i (Zsublist 0 j l) = Zsublist 0 i l.
Proof. intros. apply Zsublist_Zsublist0; lia. Qed.

Lemma Zsublist_app_exact1 {A} (l1 l2: list A):
  Zsublist 0 (Zlength l1) (l1 ++ l2) = l1.
Proof.
  unfold Zsublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  replace (length l1) with (length l1 + O)%nat by lia.
  rewrite (firstn_app_2 O).
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition sum (l: list Z): Z :=
  fold_right Z.add 0 l.

Lemma sum_app: forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.  
  intros.
  revert l2.
  induction l1 ; simpl; intros ; auto.
  rewrite IHl1.
  lia.
Qed.

Lemma sum_bound : forall b l, (forall i, 0 <= i -> 0 <= Znth i l 0 <= b) -> 0 <= sum l <= Z.of_nat (length l) * b.
Proof.
  intros.
  revert H; induction l; intros ; simpl in * ; try lia.
  assert (forall i, 0 <= i -> 0 <= Znth i l 0 <= b). 
  {
    intros.
    specialize (H (i + 1)). unfold Znth in *.
    replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H by (simpl ; lia).
    replace (a :: l) with ([a] ++ l) in H by auto.
    rewrite app_nth2_plus in H. lia.
  }
  pose proof (IHl H0).
  assert (0 <= a <= b) by (apply (H 0); simpl ; lia).
  destruct b ; lia.
Qed. 
  
Lemma sum_bound_lt : forall b l, l <> [] -> (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b) -> 0 <= sum l < Z.of_nat (length l) * b.
Proof.
  intros.
  revert H H0; induction l; intros ; simpl in * ; try lia.
  + contradiction.
  + assert (pureH : 0 <= a < b).
    {
      assert (0 <= 0 < Z.pos (Pos.of_succ_nat (length l))) by lia. simpl in *.
      specialize (H0 0 H1). unfold Znth in H0. simpl in H0.
      lia.
    }
    assert (forall i, 0 <= i < Z.of_nat (length l) -> 0 <= Znth i l 0 < b). 
    {
      intros.
      specialize (H0 (i + 1)). unfold Znth in *.
      replace (Z.to_nat (i + 1)) with (length ([a]) + Z.to_nat i)%nat in H0 by (simpl ; lia).
      replace (a :: l) with ([a] ++ l) in H0 by auto.
      rewrite app_nth2_plus in H0. lia.
    }
    destruct l ; simpl in *.
    * destruct b ; lia. 
    * assert (z :: l <> []).
      { intro. inversion H2. }
        pose proof (IHl H2 H1).
      destruct b ; lia.
Qed. 


Lemma Zsublist_length : forall {A : Type} lo hi (l : list A),
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> length (Zsublist lo hi l) = Z.to_nat (hi - lo).
Proof.
  intros.
  unfold Zsublist.
  rewrite length_skipn, length_firstn.
  lia.
Qed.

Lemma Znth_Zsublist_lt : forall {A : Type} lo hi (l : list A) i a0,
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> 0 <= i < hi - lo -> Znth i (Zsublist lo hi l) a0 = Znth (lo + i) l a0.
Proof. 
  intros. unfold Znth.
  pose proof (firstn_skipn (Z.to_nat lo) l).
  rewrite <- H2 at 2.
  replace (Z.to_nat (lo + i)) with (length (firstn (Z.to_nat lo) l) + Z.to_nat i)%nat by (rewrite length_firstn ; lia).
  rewrite app_nth2_plus.
  replace (skipn (Z.to_nat lo) l) with (Zsublist lo hi l ++ Zsublist hi (Z.of_nat (length l)) l) .
  - rewrite app_nth1 ; auto. 
    rewrite Zsublist_length ; try lia.
  - replace (skipn (Z.to_nat lo) l) with (Zsublist lo (Z.of_nat (length l)) l).
    + rewrite <- Zsublist_split ; auto ; lia. 
    + unfold Zsublist. rewrite firstn_all2 ; auto. lia.
Qed.

Lemma Znth_Zsublist_ge : forall {A : Type} lo hi (l : list A) i a0,
  0 <= lo <= hi -> hi <= Z.of_nat (length l) -> hi - lo <= i -> Znth i (Zsublist lo hi l) a0 = a0.
Proof.
  intros. unfold Znth.
  rewrite nth_overflow ; auto.
  rewrite Zsublist_length ; lia.
Qed.

Lemma list_eq_ext: forall {A: Type} d (l1 l2: list A),
  l1 = l2 <->
  (Zlength l1 = Zlength l2 /\
   forall i, 0 <= i < Zlength l1 -> Znth i l1 d = Znth i l2 d).
Proof.
  intros.
  split; [intros; subst; auto |].
  intros [? ?].
  revert l2 H H0; induction l1; simpl; intros.
  + destruct l2.
    - reflexivity.
    - rewrite Zlength_cons in H.
      rewrite Zlength_nil in H.
      pose proof Zlength_nonneg l2.
      lia.
  + destruct l2.
    - rewrite Zlength_cons in H.
      rewrite Zlength_nil in H.
      pose proof Zlength_nonneg l1.
      lia.
    - rewrite !Zlength_cons in H.
      specialize (IHl1 l2 ltac:(lia)).
      pose proof Zlength_nonneg l1.
      rewrite Zlength_cons in H0.
      pose proof H0 0 ltac:(lia).
      rewrite !Znth0_cons in H2.
      subst a0.
      f_equal.
      apply IHl1.
      intros.
      specialize (H0 (i + 1) ltac:(lia)).
      rewrite !Znth_cons in H0 by lia.
      replace (i + 1 - 1) with i in H0 by lia.
      tauto.
Qed.

Lemma list_snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.

Lemma Zsublist_nil {A: Type}:
  forall (l : list A) a b,
    b <= a -> Zsublist a b l = [].
Proof.
  intros. unfold Zsublist.
  apply skipn_all2.
  rewrite length_firstn; lia.
Qed.

Lemma Zsublist_of_nil {A: Type}:
  forall i j,
    Zsublist i j (@nil A) = [].
Proof.
  intros. unfold Zsublist.
  rewrite firstn_nil, skipn_nil. auto.
Qed.

Lemma Zsublist_self {A: Type}:
  forall (l1: list A) x,
    x = Zlength l1 ->
    Zsublist 0 x l1 = l1.
Proof.
  intros. unfold Zsublist; subst.
  rewrite skipn_O. rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length l1))) with (length l1) by lia.
  apply firstn_all.
Qed.

Lemma Zlength_Zsublist' {A: Type}:
  forall (l: list A) i j,
    Zlength (Zsublist i j l) = 
    Z.of_nat (min (Z.to_nat j) (length l) - Z.to_nat i).
Proof.
  intros.
  rewrite Zlength_correct.
  unfold Zsublist.
  rewrite length_skipn.
  rewrite length_firstn.
  reflexivity.
Qed.

Lemma Zsublist_split_app_r {A: Type}:
  forall lo hi len (l1 l2: list A),
    Zlength l1 = len ->
    len <= lo <= hi ->
    Zsublist lo hi (l1 ++ l2) = Zsublist (lo - len) (hi - len) l2.
Proof.
  intros.
  unfold Zsublist.
  repeat rewrite skipn_firstn_comm.
  rewrite skipn_app.
  pose proof (length_skipn (Z.to_nat lo) l1).
  rewrite Zlength_correct in H.
  replace (length l1 - Z.to_nat lo)%nat with O in H1 by lia.
  rewrite length_zero_iff_nil in H1; rewrite H1.
  simpl.
  replace (Z.to_nat (hi - len) - Z.to_nat (lo - len))%nat with (Z.to_nat hi - Z.to_nat lo)%nat by lia.
  replace (Z.to_nat lo - Datatypes.length l1)%nat with (Z.to_nat (lo - len)) by lia.
  auto.
Qed.

Lemma Zsublist_cons1 {A: Type}:
  forall n a (l: list A),
    1 <= n -> Zsublist 0 n (a::l) = a :: (Zsublist 0 (n-1) l).
Proof.
  intros.
  unfold Zsublist.
  repeat rewrite skipn_firstn_comm.
  repeat rewrite skipn_O.
  replace (Z.to_nat n - Z.to_nat 0)%nat with (S(Z.to_nat (n - 1) - Z.to_nat 0)) by lia.
  apply firstn_cons.
Qed.

Lemma Zsublist_cons2 {A: Type}:
  forall m n a (l: list A),
    1 <= m <= n -> n  <= Zlength (a::l) ->
    Zsublist m n (a::l) = Zsublist (m-1) (n-1) l.
Proof.
  intros.
  unfold Zsublist.
  repeat rewrite skipn_firstn_comm.
  replace (Z.to_nat m) with (S (Z.to_nat (m - 1))) at 2 by lia.
  rewrite skipn_cons.
  replace (Z.to_nat (n - 1) - Z.to_nat (m - 1))%nat with (Z.to_nat n - Z.to_nat m)%nat by lia.
  reflexivity.
Qed.
