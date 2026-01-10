Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
From GraphLib Require Import GraphLib path.

Import SetsNotation.

Local Open Scope sets.

Section VPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {A: Type}
        {path: Path G V E A}
        {emptypath: EmptyPath G V E A path}
        {singlepath: SinglePath G V E A path}
        {concatpath: ConcatPath G V E A path}
        {destruct1npath: Destruct1nPath G V E A path emptypath singlepath concatpath}
        {destructn1path: Destructn1Path G V E A path emptypath singlepath concatpath}
        {ind1npath: PathInd1n G V E A path emptypath singlepath concatpath}
        {indn1path: PathIndn1 G V E A path emptypath singlepath concatpath}.

Definition valid_vpath: 
  G -> V -> list V -> V -> Prop := 
  fun g u p v => exists P: A, path_valid g P /\ vertex_in_path P = p /\ head P = u /\ tail P = v.

Lemma empty_vpath_valid:
  forall g v,
  valid_vpath g v (v :: nil) v.
Proof.
  intros. exists (empty_path v). split; [|split; [|split]].
  - apply empty_path_valid; auto.
  - apply empty_path_vertex.
  - pose proof head_valid g (empty_path v) (empty_path_valid g v). 
    rewrite empty_path_vertex in H. 
    simpl in H. 
    inversion H; subst. 
    repeat f_equal; auto. 
  - pose proof tail_valid g (empty_path v) (empty_path_valid g v). 
    rewrite empty_path_vertex in H.
    unfold tl_error in H.
    simpl in H. 
    inversion H; subst. 
    repeat f_equal; auto. 
Qed.

Lemma single_vpath_valid:
  forall g u v,
  step g u v ->
  valid_vpath g u (u :: v :: nil) v.
Proof.
  intros. 
  destruct H as [e ?]. 
  exists (single_path u v e). split; [|split; [|split]].
  - apply single_path_valid. auto.
  - apply single_path_vertex.
  - pose proof head_valid g (single_path u v e) (single_path_valid g u v e H). 
    rewrite single_path_vertex in H0. 
    simpl in H0. 
    inversion H0; subst. 
    repeat f_equal; auto. 
  - pose proof tail_valid g (single_path u v e) (single_path_valid g u v e H). 
    rewrite single_path_vertex in H0. 
    unfold tl_error in H0.
    simpl in H0. 
    inversion H0; subst. 
    repeat f_equal; auto. 
Qed.

Lemma valid_vpath_app:
  forall g u p1 v p2 w,
  valid_vpath g u p1 v ->
  valid_vpath g v p2 w ->
  valid_vpath g u (p1 ++ tl p2) w.
Proof.
  intros.
  destruct H as [P1 [? [? []]]].
  destruct H0 as [P2 [? [? []]]].
  subst.
  exists (concat_path P1 P2).
  assert (Hc: path_valid g (concat_path P1 P2)) by (apply concat_path_valid; auto). 
  split; [|split; [|split]]; auto.
  - apply concat_path_vertex.
  - assert (Hsome: Some (head (concat_path P1 P2)) = Some (head P1)). {
      repeat erewrite head_valid; eauto. 
      rewrite concat_path_vertex. 
      assert (Some (head P2) = Some (tail P1)) by (rewrite H5; auto). 
      erewrite head_valid in H1; eauto. 
      erewrite tail_valid in H1; eauto.
      unfold tl_error in H1. 
      destruct (vertex_in_path P1); simpl in *; auto. 
      destruct (vertex_in_path P2); simpl in *; auto. 
      inversion H1. } 
      inversion Hsome; reflexivity. 
  - assert (Hsome: Some (tail (concat_path P1 P2)) = Some (tail P2)). {
      repeat erewrite tail_valid; eauto.
      rewrite concat_path_vertex. 
      unfold tl_error. 
      assert (Some (head P2) = Some (tail P1)) by (rewrite H5; auto). 
      erewrite head_valid in H1; eauto. 
      erewrite tail_valid in H1; eauto. 
      unfold tl_error in H1. 
      destruct (vertex_in_path P2); simpl in *; auto. 
      {
        destruct (vertex_in_path P1); simpl in *; auto. 
        rewrite app_nil_r; auto. 
      } 
      {
        destruct l.
        { 
          simpl in *. 
          rewrite app_nil_r; auto. 
        }
        {
          rewrite length_app. 
          rewrite nth_error_app2. 
          2: simpl; lia. 
          simpl. 
          replace ((length (vertex_in_path P1) + S (length l) - 1 - length (vertex_in_path P1))) with (length l) by lia. auto. 
        }
      }
    }
    inversion Hsome; reflexivity.
Qed.

Lemma valid_vpath_not_nil:
  forall g u p v,
  valid_vpath g u p v ->
  p <> nil.
Proof.
  intros.
  destruct H as [P [? [? []]]].
  destruct p. 
  assert (Some (head P) = Some u) by (rewrite H1; auto).
  erewrite head_valid in H3; eauto.
  rewrite H0 in H3; inversion H3.
  symmetry.
  apply nil_cons.
Qed.

Lemma valid_vpath_empty_inv:
  forall g u x v,
  valid_vpath g u (x :: nil) v ->
  u = x /\ v = x.
Proof.
  intros.
  destruct H as [P [? [? []]]].
  simpl in *. 
  assert (Some (head P) = Some u) by (rewrite H1; auto).
  erewrite head_valid in H3; eauto.
  rewrite H0 in H3; inversion H3.
  assert (Some (tail P) = Some v) by (rewrite H2; auto).
  erewrite tail_valid in H4; eauto.
  rewrite H0 in H4; inversion H4.
  subst; auto.
Qed.

Lemma valid_vpath_single_inv:
  forall g u x y v,
  valid_vpath g u (x :: y :: nil) v ->
  u = x /\ v = y /\ step g x y.
Proof.
  intros.
  destruct H as [P [? [? []]]].
  simpl in *. 
  inversion H1 ; inversion H2; subst.
  split; [|split]; auto.
  - assert (Some (head P) = Some x). {
    repeat erewrite head_valid; eauto. 
    rewrite H0; simpl. 
    reflexivity.
    }
    inversion H1; reflexivity.
  - assert (Some (tail P) = Some y). {
    repeat erewrite tail_valid; eauto.
    unfold tl_error. 
    rewrite H0; simpl. 
    reflexivity.
    }
    inversion H1; reflexivity.
  - destruct (edge_in_path P) eqn: Hle. 
    {
      exfalso. 
      pose proof vpath_iff_epath g P H as [? _]. 
      rewrite H0, Hle in *. 
      simpl in *. 
      lia.
    }
    {
      pose proof vpath_iff_epath g P H as [_ Hpstep]. 
      specialize (Hpstep g 0 x y e ltac:(rewrite Hle; simpl; lia) ltac:(rewrite Hle; simpl; auto) ltac:(rewrite H0; simpl; auto) ltac:(rewrite H0; simpl; auto) ). 
      eapply step_trivial; eauto.
    }
Qed.

Lemma valid_vpath_app_inv:
  forall g u p1 v p2 w,
  valid_vpath g u (p1 ++ v :: p2) w ->
  valid_vpath g u (p1 ++ v :: nil) v /\ valid_vpath g v (v :: p2) w. 
Proof.
  (* 整体的证明结构需要优化 *)
Admitted.

Lemma valid_vpath_inv_1n:
  forall g u p v,
  valid_vpath g u p v ->
  (u = v /\ p = u :: nil) \/
  (exists w p', p = u :: p' /\ step g u w /\ valid_vpath g w p' v).
Proof.
  intros.
  destruct p as [ | x [ | y p ] ].
  - apply valid_vpath_not_nil in H. congruence.
  - pose proof (valid_vpath_empty_inv _ _ _ _ H) as (-> & ->).
    auto.
  - pose proof (valid_vpath_app_inv g u (x :: nil) y p v H) as (? & ?).
    pose proof (valid_vpath_single_inv _ _ _ _ _ H0) as (? & ? & ?). subst.
    right. eauto.
Qed.

Lemma valid_vpath_start:
  forall g u p v,
  valid_vpath g u p v ->
  exists p', p = u :: p'.
Proof.
  intros.
  pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ->) | (w & p' & -> & ? & ?)].
  eauto. eauto.
Qed.

Lemma valid_vpath_ind_1n:
  forall g (P : V -> list V -> V -> Prop),
  (forall v, P v (v :: nil) v) ->
  (forall u v p w,
   step g u v -> valid_vpath g v p w -> P v p w ->
   P u (u :: p) w) ->
  forall u p v, valid_vpath g u p v -> P u p v.
Proof.
  intros g P IH1 IH2 u p' v H.
  pose proof (valid_vpath_start _ _ _ _ H) as (p & ->).
  revert u v H. induction p; intros.
  - pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ?) | (w & p' & ? & ? & ?)].
    apply IH1.
    inversion H0. subst.
    pose proof (valid_vpath_inv_1n _ _ _ _ H2) as [(? & ?) | (? & ? & ? & ? & ?)].
    congruence. congruence.
  - pose proof (valid_vpath_inv_1n _ _ _ _ H) as [(-> & ?) | (w & p' & ? & ? & ?)].
    congruence.
    inversion H0. subst. 
    pose proof (valid_vpath_start _ _ _ _ H2) as (p' & ?). inversion H3. subst.
    eapply IH2; eauto.
Qed.

Lemma valid_vpath_step_1n:
  forall g u v p w,
  step g u v ->
  valid_vpath g v p w ->
  valid_vpath g u (u :: p) w.
Proof.
  intros.
  pose proof (valid_vpath_start _ _ _ _ H0) as (p' & ->).
  eapply (valid_vpath_app g u (u :: v :: nil) v (v :: p') w).
  apply single_vpath_valid. auto. auto.
Qed.

Lemma valid_vpath_ind_n1:
  forall g (P : V -> list V -> V -> Prop),
  (forall v, P v (v :: nil) v) ->
  (forall u p v w,
   valid_vpath g u p v -> P u p v -> step g v w ->
   P u (p ++ w :: nil) w) ->
  forall u p v, valid_vpath g u p v -> P u p v.
Proof.
  intros g P IH1 IH2.
  enough (forall u p1 v p2 w,
          valid_vpath g u p1 v ->
          P u p1 v ->
          valid_vpath g v p2 w ->
          P u (p1 ++ tl p2) w).
  { intros. specialize (H u (u :: nil) u p v).
    pose proof (valid_vpath_start _ _ _ _ H0) as (p' & ->).
    apply H; auto. apply empty_vpath_valid.  }
  intros * Hp1 Hp1' Hp2.
  revert u p1 Hp1 Hp1'.
  pattern v, p2, w. revert v p2 w Hp2.
  eapply valid_vpath_ind_1n; eauto.
  - simpl. intros. rewrite app_nil_r. auto.
  - simpl. intros.
    pose proof (valid_vpath_start _ _ _ _ H0) as (p2 & ->).
    replace (p1 ++ v :: p2) with ((p1 ++ v :: nil) ++ p2).
    2:{ rewrite <- app_assoc. auto. }
    apply H1.
    eapply valid_vpath_app with (p2 := u :: v :: nil); eauto.
    apply single_vpath_valid; auto.
    eapply IH2; eauto.
Qed.

Lemma valid_vpath_inv_n1:
  forall g u p v,
  valid_vpath g u p v ->
  (u = v /\ p = u :: nil) \/
  (exists p' w, p = p' ++ v :: nil /\ valid_vpath g u p' w /\ step g w v).
Proof.
  intros.
  revert u p v H. eapply valid_vpath_ind_n1; eauto.
  intros. right. eauto.
Qed.

Lemma valid_vpath_end:
  forall g u p v,
  valid_vpath g u p v ->
  exists p', p = p' ++ v :: nil.
Proof.
  intros.
  pose proof (valid_vpath_inv_n1 _ _ _ _ H) as [(-> & ->) | (w & p' & -> & ? & ?)].
  exists nil. easy. eauto.
Qed.

Lemma valid_vpath_step_n1:
  forall g u p v w,
  valid_vpath g u p v ->
  step g v w ->
  valid_vpath g u (p ++ w :: nil) w.
Proof.
  intros.
  pose proof (valid_vpath_end _ _ _ _ H) as (p' & ->).
  eapply (valid_vpath_app g u (p' ++ v :: nil) v (v :: w :: nil) w).
  auto. apply single_vpath_valid. auto.
Qed.

Lemma valid_vpath_reachable:
  forall g u p v,
  valid_vpath g u p v ->
  reachable g u v.
Proof.
  intros g. eapply valid_vpath_ind_1n; intros.
  - reflexivity.
  - unfold reachable.
    pose proof (rt_trans_1n (step g)). sets_unfold in H2.
    apply H2. eauto.
Qed.

Lemma reachable_valid_vpath:
  forall g u v,
  reachable g u v ->
  exists p, valid_vpath g u p v.
Proof.
  intros. unfold reachable in H.
  induction_1n H.
  - exists (v :: nil). apply empty_vpath_valid.
  - destruct IHrt as (p & ?).
    exists (u :: p). eapply valid_vpath_step_1n; eauto.
Qed.

End VPATH.

