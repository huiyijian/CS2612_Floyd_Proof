Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
Require Import ListLib.Base.Inductive.
From GraphLib Require Import graph_basic reachable_basic path.

Import SetsNotation.

Local Open Scope sets.

Section EPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {P: Type}
        {path: @Path G V E pg gv P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

(* 基于原始Type Class destruct1n的导出定义valid_epath在list E上的归纳法 *)

Definition valid_epath: 
  G -> V -> list E -> V -> Prop := 
  fun g u p v => exists P: P, 
    path_valid g P /\ 
    edge_in_path P = p /\ 
    hd_error (vertex_in_path P) = Some u /\ 
    tl_error (vertex_in_path P)= Some v.

(* 我们也可以基于epath而不是path进行定义和证明。 *)
Definition is_epath_through_vset:
  G -> V -> list E -> V -> (V -> Prop) -> Prop :=
  fun g u p v vset =>
    valid_epath g u p v /\ 
    forall x, x ∈ vset <-> exists p1 p2, p1 <> nil /\ p2 <> nil /\ p1 ++ p2 = p /\ 
    valid_epath g x p1 v /\ valid_epath g v p2 x.



Lemma empty_path_edge: forall (g: G) v,
  edge_in_path (empty_path v) = nil.
Proof.
  intros. 
  pose proof (vpath_iff_epath g (empty_path v) (empty_path_valid g v)) as [Hlen _].
  rewrite empty_path_vertex in Hlen.
  simpl in Hlen.
  assert (length (edge_in_path (empty_path v)) = 0) by lia.
  rewrite length_zero_iff_nil in H. 
  auto.
Qed.

Lemma valid_epath_nil_inv:
  forall g u v,
  valid_epath g u nil v ->
  u = v.
Proof.
  intros.
  destruct H as [path_obj [H_pval [H_edges [H_hd H_tl]]]].
  pose proof (vpath_iff_epath g path_obj H_pval) as [Hlen _].
  rewrite H_edges in Hlen. simpl in Hlen.
  destruct (vertex_in_path path_obj) as [| x [| y l]].
  - simpl in Hlen; lia.
  - simpl in H_hd; injection H_hd as Hu; subst.
    simpl in H_tl; injection H_tl as Hv; subst.
    reflexivity.
  - simpl in Hlen; lia.
Qed.

Lemma valid_epath_cons_inv:
  forall g u e p w,
  valid_epath g u (e :: p) w ->
  exists v, step_aux g e u v /\ valid_epath g v p w.
Proof. 
  (* 我们使用 destruct_1n来完成证明。 *)
  intros.
  destruct H as [p0 [Hp [Hedge [Hhd Htl]]]].
  pose proof (destruct_1n_spec g p0 Hp).
  destruct (destruct_1n_path p0).
  - (* Base Case: P implies empty edges *)
    subst. rewrite (empty_path_edge g) in Hedge. discriminate.
  - (* Step Case *)
    destruct H as [Hp' [Hhd' [Hstep Heq]]].
    subst p0.
    rewrite concat_path_edge in Hedge.
    rewrite single_path_edge in Hedge.
    simpl in Hedge. injection Hedge as He Hp_eq. subst.
    
    rewrite concat_path_vertex in Hhd.
    rewrite single_path_vertex in Hhd.
    simpl in Hhd. injection Hhd as Hu. subst u0.

    exists (head p1). split; auto.
    
    (* 构造剩余部分的 valid_epath *)
    exists p1. split; auto.
    split; auto.
    split.
    + erewrite head_valid; eauto.
    + (* Tail 处理 *)
      rewrite concat_path_vertex in Htl.
      rewrite single_path_vertex in Htl.
      (* 利用 list 性质： tl_error ( [u; v0] ++ rest ) = tl_error rest *)
      (* 注意 vertex_in_path p0 至少有一个点 (v0) *)
      pose proof (vpath_iff_epath g p1 Hp') as [Hlen' _].
      destruct (vertex_in_path p1) eqn:Hvpath.
      * simpl in Hlen'. lia. (* 长度不能为0 *)
      * (* 既然不为空，tl_error (l1 ++ l2) = tl_error l2 *)

        destruct (list_snoc_destruct l); [subst; simpl in *|].
        { unfold tl_error in Htl; simpl in Htl.
          unfold tl_error; simpl.
          erewrite head_valid in Htl; eauto. 
          rewrite Hvpath in Htl; simpl in Htl. 
          auto. }
        { destruct H as [? []]; subst. 
          rewrite app_comm_cons.
          rewrite tl_error_last.
          simpl in Htl. 
          rewrite! app_comm_cons in Htl.
          rewrite tl_error_last in Htl.
          auto. }
Qed.

(* 辅助引理：empty_path 对应空的 epath *)
Lemma valid_epath_empty: forall g v,
  valid_epath g v nil v.
Proof.
  intros.
  unfold valid_epath.
  exists (empty_path v).
  assert (path_valid g (empty_path v)) by (apply empty_path_valid).
  split; [auto|].
  split.
  - apply (empty_path_edge g).
  - rewrite empty_path_vertex. simpl. auto.
Qed.

(* 辅助引理：single_path 对应单步 epath *)
Lemma valid_epath_single: forall g u v e,
  step_aux g e u v ->
  valid_epath g u (e :: nil) v.
Proof.
  intros.
  unfold valid_epath.
  exists (single_path u v e). split; [apply single_path_valid; auto|].
  split; [apply single_path_edge|].
  split; [rewrite single_path_vertex; simpl; auto|].
  rewrite single_path_vertex; simpl; auto.
Qed.

Lemma valid_epath_single_inv:
  forall g u v e,
  valid_epath g u (e :: nil) v ->
  step_aux g e u v.
Proof.
  intros.
  apply valid_epath_cons_inv in H.
  destruct H as [v' [Hstep Hrest]].
  apply valid_epath_nil_inv in Hrest.
  subst. auto.
Qed.

Lemma valid_epath_app:
  forall g u p1 v p2 w,
  valid_epath g u p1 v ->
  valid_epath g v p2 w ->
  valid_epath g u (p1 ++ p2) w.
Proof.
  intros.
  destruct H as [P1 [Hp1 [Hedge1 [Hhd1 Htl1]]]].
  destruct H0 as [P2 [Hp2 [Hedge2 [Hhd2 Htl2]]]].
  
  exists (concat_path P1 P2).
  
  assert (tail P1 = head P2).
  {
    assert (Hg: Some (tail P1) = Some (head P2)). 
    2:{ inversion Hg; auto. }
    erewrite tail_valid by eauto.
    erewrite head_valid by eauto.
    rewrite Htl1, Hhd2. reflexivity.
  }
  
  split.
  - apply concat_path_valid; auto.
  - split.
    + rewrite concat_path_edge. rewrite Hedge1, Hedge2. reflexivity.
    + split.
      * rewrite concat_path_vertex.
        destruct (vertex_in_path P1); [discriminate|].
        simpl. auto.
      * rewrite concat_path_vertex.
        destruct (vertex_in_path P2); [discriminate|]. 
        simpl in *.
        destruct (list_snoc_destruct l); [subst; simpl in *|].
        { unfold tl_error in Htl2; simpl in Htl2. 
          inversion Hhd2 ; inversion Htl2; subst. 
          rewrite app_nil_r; auto. }
        { destruct H0 as [? []]; subst. 
          rewrite! app_assoc.
          rewrite tl_error_last.
          rewrite app_comm_cons in Htl2.
          rewrite tl_error_last in Htl2.
          auto. }
Qed.

Lemma valid_epath_cons:  
  forall g u e p v w,
  step_aux g e u v ->
  valid_epath g v p w ->
  valid_epath g u (e :: p) w.
Proof.
  intros.
  replace (e :: p) with ((e :: nil) ++ p) by auto.
  eapply valid_epath_app; [| apply H0].
  apply valid_epath_single; auto.
Qed.

Lemma valid_epath_app_inv:
  forall g u p1 p2 w,
  valid_epath g u (p1 ++ p2) w ->
  exists v, valid_epath g u p1 v /\ valid_epath g v p2 w.
Proof.
  intros g u p1.
  revert u.
  induction p1; intros u p2 w H.
  - (* p1 = nil *)
    simpl in H.
    exists u. split.
    + apply valid_epath_empty.
    + assumption.
  - (* p1 = a :: p1 *)
    rewrite <- app_comm_cons in H.
    apply valid_epath_cons_inv in H.
    destruct H as [v' [Hstep Hvalid_rest]].
    apply IHp1 in Hvalid_rest.
    destruct Hvalid_rest as [target [Hsub1 Hsub2]].
    exists target. split.
    + (* 重组头部: u --a--> v' --p1--> target *)
      apply (valid_epath_app g u (a::nil) v' p1 target).
      * apply valid_epath_single; auto.
      * assumption.
    + assumption.
Qed.


Lemma valid_epath_ind_1n:
  forall g (X : V -> list E -> V -> Prop)
  (Hbase: forall v, X v nil v)
  (Hind: forall u v e p w,
    step_aux g e u v -> 
    valid_epath g v p w -> 
    X v p w ->
    X u (e :: p) w),
  forall u p v, valid_epath g u p v -> X u p v.
Proof.
  intros g X Hbase Hind u l v Hvalid.
  revert u v Hvalid.
  induction l as [| e l' IH]; intros u v Hvalid.
  
  (* Case 1: l = [] *)
  - destruct Hvalid as [path_obj [H_pval [H_edges [H_hd H_tl]]]].
    pose proof (destruct_1n_spec g path_obj H_pval) as Hspec.
    destruct (destruct_1n_path path_obj) as [v_base | p_rest u_step v_step e_step].
    + subst.
      rewrite empty_path_vertex in *.
      simpl in H_hd, H_tl.
      injection H_hd as Hu.
      injection H_tl as Hv.
      subst.
      apply Hbase.
    + destruct Hspec as [_ [_ [_ H_eq]]].
      subst path_obj.
      rewrite concat_path_edge in H_edges.
      rewrite single_path_edge in H_edges.
      simpl in H_edges.
      discriminate H_edges.

  (* Case 2: l = e :: l' *)
  - destruct Hvalid as [path_obj [H_pval [H_edges [H_hd H_tl]]]].
    pose proof (destruct_1n_spec g path_obj H_pval) as Hspec.
    destruct (destruct_1n_path path_obj) as [v_base | p_rest u_step v_step e_step].
    + subst. 
      rewrite empty_path_vertex in *.
      pose proof (vpath_iff_epath g (empty_path v_base) (empty_path_valid g v_base)) as Hlen.
      rewrite empty_path_vertex in Hlen.
      destruct Hlen as [Hlen_eq _].
      simpl in Hlen_eq.
      rewrite H_edges in Hlen_eq.
      simpl in Hlen_eq.
      lia. 
    + destruct Hspec as [Hp_rest_valid [H_head_rest [H_step H_path_eq]]].
      subst path_obj.
      
      rewrite concat_path_edge in H_edges.
      rewrite single_path_edge in H_edges.
      simpl in H_edges.
      injection H_edges as He Hedges_rest.
      subst e_step.
      
      rewrite concat_path_vertex in H_hd.
      rewrite single_path_vertex in H_hd.
      simpl in H_hd.
      injection H_hd as Hu. subst u_step.

      (* 处理尾部节点 v *)
      rewrite concat_path_vertex in H_tl.
      (* 准备使用新的 lemma *)
      (* l1 = vertex_in_path (single_path u v_step e) = [u; v_step] *)
      (* l2 = vertex_in_path p_rest *)
      
      pose proof (vpath_iff_epath g p_rest Hp_rest_valid) as Hlen_rest.
      destruct Hlen_rest as [Hlen_rest_eq _].
      assert (vertex_in_path p_rest <> nil) as H_l2_nn.
      { intro Hnil. rewrite Hnil in Hlen_rest_eq. simpl in Hlen_rest_eq. lia. }

      rewrite single_path_vertex in H_tl.
      
      (* 证明连接条件: tl_error [u; v_step] = hd_error (vertex_in_path p_rest) *)
      assert (tl_error (u :: v_step :: nil) = hd_error (vertex_in_path p_rest)) as H_connect.
      {
          unfold tl_error. simpl.
          rewrite <- (head_valid g p_rest Hp_rest_valid).
          f_equal. symmetry. assumption.
      }

      rewrite tl_error_app_skipn_connected in H_tl; [| discriminate | assumption | assumption].
      
      (* H_tl 现在是 tl_error (vertex_in_path p_rest) = Some v *)
      (* 构造归纳假设需要的前提 *)
      assert (hd_error (vertex_in_path p_rest) = Some v_step).
      { rewrite <- (head_valid g p_rest Hp_rest_valid). f_equal. assumption. }
      
      assert (valid_epath g v_step l' v).
      {
        exists p_rest.
        repeat split; auto.
      }

      apply Hind with (v := v_step).
      * assumption. 
      * assumption. 
      * apply IH. assumption.
Qed.

Lemma valid_epath_snoc:
  forall g u p v w e,
  valid_epath g u p v ->
  step_aux g e v w ->
  valid_epath g u (p ++ e :: nil) w.
Proof.
  intros.
  eapply valid_epath_app.
  - apply H.
  - apply valid_epath_single; auto.
Qed.

Lemma valid_epath_snoc_inv:
  forall g u p e w,
  valid_epath g u (p ++ e :: nil) w ->
  exists v, valid_epath g u p v /\ step_aux g e v w.
Proof.
  intros.
  apply valid_epath_app_inv in H.
  destruct H as [v [Hpre Hsuf]].
  apply valid_epath_single_inv in Hsuf.
  exists v. auto.
Qed.

Lemma valid_epath_reachable:
  forall g u p v,
  valid_epath g u p v ->
  reachable g u v.
Proof.
  intros.
  revert u p v H.
  apply valid_epath_ind_1n.
  - (* Base: nil *)
    intros. reflexivity.
  - (* Step: e :: p *)
    intros.
    eapply step_reachable_reachable.
    exists e. eauto. auto.
Qed.

(* 对应 reachable_valid_vpath *)
Lemma reachable_valid_epath:
  forall g u v,
  reachable g u v ->
  exists p, valid_epath g u p v.
Proof.
  intros.
  unfold reachable in H.
  induction_1n H.
  - exists nil. apply valid_epath_empty.
  - destruct IHrt as [p Hvalid].
    destruct H0 as [e Hstep].
    exists (e :: p).
    eapply valid_epath_cons; eauto.
Qed.

(* 下面是关于简单路径的部分，要求不经过重复的边。这一定义可能在最小生成树时有用 *)

Definition simple_epath (g: G) (u: V) (p: list E) (v: V): Prop :=
  NoDup p /\ valid_epath g u p v.

Definition simple_circuit (g: G) (e: list E) (u: V): Prop :=
  simple_epath g u e u.

Definition have_simple_circuit (g: G) : Prop :=
  exists u p, simple_epath g u p u.

Lemma valid_path_evalid: forall g p u v,
  valid_epath g u p v ->
  forall e, In e p -> evalid g e.
Proof.
Admitted.

Lemma path_simplfier 
  {stepuniqueundirected: StepUniqueUndirected G V E}: 
  forall g p u v,
  valid_epath g u p v ->
  exists q, simple_epath g u q v.
Proof.
Admitted.

End EPATH.