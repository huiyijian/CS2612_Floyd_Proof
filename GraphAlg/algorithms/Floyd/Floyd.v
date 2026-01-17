
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Wf_nat.
Require Import ListLib.Base.Positional.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Classical.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import GraphLib.examples.floyd.
Require Import Algorithms.MapLib.

Import SetsNotation.

Lemma Z_op_plus_le_mono: forall a b c d,
  Z_op_le a b -> Z_op_le c d -> Z_op_le (Z_op_plus a c) (Z_op_plus b d).
Proof.
  intros. destruct a, b, c, d; simpl in *; try contradiction; try lia; auto.
Qed.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope nat.


Section Floyd.

(** Floyd算法用于计算图中所有顶点对之间的最短路径。
    核心思想是通过逐步允许使用更多的顶点作为中间点来优化路径。
    
    循环不变量提示：
    - k-循环不变量：dist[i][j] = shortestPath(i, j, k)
      即 dist[i][j] 是从 i 到 j 只经过前 k 个顶点作为中间点的最短距离
    - i-循环不变量：
      * 对于 i0 < i: dist[i0][j] = shortestPath(i0, j, k)
      * 对于 i0 >= i: dist[i0][j] = shortestPath(i0, j, k-1)
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        (g: G)
        {eq_dec: EqDec (V * V) eq}
        {v_eq_dec: EqDec V eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {destructn1path: Destructn1Path G V E P path emptypath singlepath concatpath}
        {ind1npath: PathInd1n G V E P path emptypath singlepath concatpath}
        {indn1path: PathIndn1 G V E P path emptypath singlepath concatpath}.

Context {path_unique: forall g p1 p2, 
  path_valid g p1 -> path_valid g p2 -> 
  head p1 = head p2 -> 
  edge_in_path p1 = edge_in_path p2 -> 
  p1 = p2}.

Context {sud: StepUniqueDirected G V E}.

Context {ew: EdgeWeight G E}
        {nnc: NoNegativeCycle g}
        {g_valid: gvalid g}.

Local Existing Instance pg.
Local Existing Instance gv.
Local Existing Instance stepvalid.
Local Existing Instance path.
Local Existing Instance emptypath.
Local Existing Instance singlepath.
Local Existing Instance concatpath.
Local Existing Instance destruct1npath.
Local Existing Instance destructn1path.
Local Existing Instance ind1npath.
Local Existing Instance indn1path.
Local Existing Instance sud.
Local Existing Instance ew.

Notation step := (step g).
Notation reachable := (reachable g).

Record St: Type := mkSt {
  dist: (V * V) -> option Z;
  next: (V * V) -> option V;
}.

Instance: Settable St := settable! mkSt <dist; next>.

Definition Z_op_lt (x y: option Z): Prop := 
  match x, y with
  | Some x, Some y => (x < y)%Z
  | Some _, None => True
  | None, _ => False
  end.

Definition Z_op_lt_dec (x y: option Z): {Z_op_lt x y} + {~ Z_op_lt x y}.
Proof.
  destruct x, y; simpl.
  - apply Z_lt_dec.
  - left. trivial.
  - right. auto.
  - right. auto.
Defined.

Lemma Z_op_lt_le: forall x y, Z_op_lt x y -> Z_op_le x y.
Proof.
  destruct x, y; simpl; intros; try contradiction; try lia; auto.
Qed.

(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]) *)
Definition update_dist (i j k: V): program St unit :=
  update' (fun s =>
  let d_ik := s.(dist) (i, k) in
  let d_kj := s.(dist) (k, j) in
  let d_ij := s.(dist) (i, j) in
  let d_new := Z_op_plus d_ik d_kj in
  if Z_op_lt_dec d_new d_ij then
    s <| dist ::= fun d => (i, j) !-> d_new; d |>
      <| next ::= fun n => (i, j) !-> n (i, k); n |>
  else
    s).

Definition Floyd_j (k: V) (j: V): program St unit :=
  forset (fun v => vvalid g v) (fun i =>
    update_dist i j k).

(** 对于固定的中间点k，遍历所有顶点对(i,j)进行松弛 *)
Definition Floyd_k (k: V): program St unit :=
  forset (fun v => vvalid g v) (Floyd_j k).

(** Floyd主算法：遍历所有可能的中间点k *)
Definition Floyd: program St unit :=
  forset (fun v => vvalid g v) Floyd_k.

Fixpoint reconstruct_path_aux (next: (V * V) -> option V) (u v: V) (n: nat): list V :=
  match n with
  | 0 => nil
  | S n' => 
      if v_eq_dec u v then u :: nil
      else match next (u, v) with
           | Some x => u :: reconstruct_path_aux next x v n'
           | None => nil
           end
  end.

(** 
  ===== 循环不变量 ===== 
  Floyd算法的核心不变量：
  在迭代过程中（处理完中间节点集合 done），
  dist[u][v] 存储的是"中间节点仅限于 done 中的顶点"的最短路径。
  
  具体含义：
  - done 表示已经作为"中间节点"处理过的顶点集合
  - dist[u][v] = min { weight(p) | p 是从 u 到 v 的路径，且 p 的中间节点都在 done 中 }
  - 注意：u 和 v 本身不算中间节点，它们是起点和终点
  
  循环不变量的演进：
  - 初始：done = ∅，dist[u][v] 表示不经过任何中间节点的最短路径（即直接边或无穷大）
  - 处理节点 k 后：done = done ∪ {k}，dist[u][v] 更新为
      min(dist[u][v], dist[u][k] + dist[k][v])
    这表示要么不经过 k，要么经过 k 的最短路径
  - 最终：done = 所有顶点，dist[u][v] 表示真正的最短路径

  Next 不变量：
  - 如果 next[u][v] = x，则 x 是 u 到 v 的最优路径上的下一个节点
  - dist[u][v] = weight(u, x) + dist[x][v]
*)

Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  (forall u v, min_weight_distance_in_vset g u v done (s.(dist) (u, v))) /\
  (forall u v, u <> v -> s.(dist) (u, v) <> None -> s.(next) (u, v) <> None) /\
  (forall u v x, s.(next) (u, v) = Some x -> 
     (x = v \/ x ∈ done) /\
     exists e, step_aux g e u x /\
     exists d_uv d_xv w_e, 
       s.(dist) (u, v) = Some d_uv /\
       s.(dist) (x, v) = Some d_xv /\
       weight g e = Some w_e /\
       d_uv = (w_e + d_xv)%Z).


(** ===== 正确性规范 ===== *)

(** 健全性：如果dist记录了距离n，则n确实是最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall u v w, s.(dist) (u, v) = w -> min_weight_distance g u v w.

(** 完备性：如果存在最短距离n，则dist正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall u v w, min_weight_distance g u v w -> s.(dist) (u, v) = w.

Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s /\
  (forall u v d, s.(dist) (u, v) = Some d -> 
     exists p, path_valid g p /\
               vertex_in_path p = reconstruct_path_aux s.(next) u v (length (vertex_in_path p)) /\
               path_weight g p = Some d).

(** ===== 主定理 =====
    
    证明 Floyd 算法的正确性：
    如果初始状态满足空集上的循环不变量，
    则算法结束后，dist 数组正确记录了所有点对之间的最短距离。
*)

Definition initialized_state (s: St): Prop := 
  Floyd_loop_invariant ∅ s.

Lemma is_empty_path_dec: forall p, path_valid g p -> {is_empty_path p} + {~ is_empty_path p}.
Proof.
  intros p Hp.
  destruct (destruct1npath.(destruct_1n_path) p) eqn:Hdestruct.
  - left. exists v.
    pose proof (destruct1npath.(destruct_1n_spec) g p Hp) as Hspec.
    rewrite Hdestruct in Hspec.
    auto.
  - right.
    pose proof (destruct1npath.(destruct_1n_spec) g p Hp) as Hspec.
    rewrite Hdestruct in Hspec.
    destruct Hspec as [Hp' [_ [_ Heq]]].
    intro Hempty.
    destruct Hempty as [v0 Heq0].
    rewrite Heq in Heq0.
    apply (f_equal (edge_in_path)) in Heq0.
    rewrite concat_path_edge in Heq0.
    rewrite single_path_edge in Heq0.
    pose proof (vpath_iff_epath g (empty_path v0) (empty_path_valid g v0)) as Hiff.
    destruct Hiff as [Hlen _].
    rewrite empty_path_vertex in Hlen. simpl in Hlen.
    assert (Hep: edge_in_path (empty_path v0) = nil).
    { destruct (edge_in_path (empty_path v0)) as [|x l].
      - reflexivity.
      - simpl in Hlen. lia. }
    rewrite Hep in Heq0.
    simpl in Heq0. discriminate.
Qed.

Lemma valid_path_tail_valid: forall p,
  path_valid g p -> ~ is_empty_path p -> vvalid g (tail p).
Proof.
  intros p Hp Hne.
  pose proof (vpath_iff_epath g p Hp) as Hiff.
  destruct Hiff as [Hlen Hstep].
  destruct (edge_in_path p) as [|e pe] eqn:He.
  - exfalso. apply Hne.
    destruct (destruct1npath.(destruct_1n_path) p) eqn:Hdestruct.
    + apply destruct1npath.(destruct_1n_spec) in Hp.
      rewrite Hdestruct in Hp. subst.
      exists v. reflexivity.
    + apply destruct1npath.(destruct_1n_spec) in Hp.
      rewrite Hdestruct in Hp.
      destruct Hp as [Hp' [_ [_ Heq]]].
      subst p.
      rewrite concat_path_edge in He.
      rewrite single_path_edge in He.
      simpl in He. discriminate.
  - set (n := length pe).
    assert (Hn: 0 <= n < length (edge_in_path p)).
    { rewrite He. simpl. lia. }
    destruct (nth_error (edge_in_path p) n) as [el|] eqn:Hel.
    2:{ apply nth_error_None in Hel. rewrite He in Hel. simpl in Hel. lia. }
    
    pose proof (tail_valid g p Hp) as Htv.
    unfold tl_error in Htv.
    rewrite Hlen in Htv.
     replace (length (e :: pe) + 1 - 1) with (S n) in Htv.
     2: { simpl. subst n. lia. }
     assert (Hlast_v: nth_error (vertex_in_path p) (S n) = Some (tail p)).
    { symmetry. exact Htv. }
    destruct (nth_error (vertex_in_path p) n) as [vl|] eqn:Hvl.
    2:{ apply nth_error_None in Hvl. rewrite Hlen in Hvl. simpl in Hvl. lia. }
    
    rewrite He in Hn. rewrite He in Hel.
    specialize (Hstep g n vl (tail p) el Hn Hel Hvl Hlast_v).
    eapply step_vvalid2; eauto.
Qed.

Lemma valid_path_head_valid: forall p,
  path_valid g p -> ~ is_empty_path p -> vvalid g (head p).
Proof.
  intros p Hp Hne.
  pose proof (vpath_iff_epath g p Hp) as Hiff.
  destruct Hiff as [Hlen Hstep].
  destruct (edge_in_path p) as [|e pe] eqn:He.
  - exfalso. apply Hne.
    destruct (destruct1npath.(destruct_1n_path) p) eqn:Hdestruct.
    + apply destruct1npath.(destruct_1n_spec) in Hp.
      rewrite Hdestruct in Hp. subst.
      exists v. reflexivity.
    + apply destruct1npath.(destruct_1n_spec) in Hp.
      rewrite Hdestruct in Hp.
      destruct Hp as [Hp' [_ [_ Heq]]].
      subst p.
      rewrite concat_path_edge in He.
      rewrite single_path_edge in He.
      simpl in He. discriminate.
  - set (n := 0).
    assert (Hn: 0 <= n < length (edge_in_path p)).
    { rewrite He. simpl. lia. }
    destruct (nth_error (edge_in_path p) n) as [el|] eqn:Hel.
    2:{ apply nth_error_None in Hel. rewrite He in Hel. simpl in Hel. lia. }

    pose proof (head_valid g p Hp) as Hhv.
    assert (Hfirst_v: nth_error (vertex_in_path p) 0 = Some (head p)).
    { rewrite Hhv. destruct (vertex_in_path p); reflexivity. }
    
    destruct (nth_error (vertex_in_path p) 1) as [v1|] eqn:Hv1.
    2:{ apply nth_error_None in Hv1. rewrite Hlen in Hv1. simpl in Hv1. lia. }

    rewrite He in Hn. rewrite He in Hel.
    specialize (Hstep g 0 (head p) v1 el Hn Hel Hfirst_v Hv1).
    eapply step_vvalid1; eauto.
Qed.

Lemma Hoare_forset {A: Type} {S: A -> Prop}:
  forall (Inv: (A -> Prop) -> St -> Prop)
         (body: A -> program St unit),
  (forall a done, a ∈ S -> ~ a ∈ done -> 
     Hoare (Inv done) (body a) (fun _ => Inv (done ∪ [a]))) ->
  Hoare (Inv ∅) (forset S body) (fun _ => Inv S).
Proof.
  intros Inv body Hstep.
  unfold forset.
  eapply Hoare_conseq_pre.
  2: refine (Hoare_fix_logicv (forset_f body)
            (fun remaining _ s => Inv (fun x => S x /\ ~ remaining x) s /\ (forall x, remaining x -> S x))
            (fun _ _ _ s => Inv S s) S tt _).
  - intros s Hinv.
    split.
    + assert (Eq: (fun x => S x /\ ~ S x) = ∅).
      { extensionality x. apply propositional_extensionality. sets_unfold. tauto. }
      rewrite <- Eq in Hinv. apply Hinv.
    + intros x Hx. apply Hx.
  - intros W Hrec remaining _.
    unfold forset_f.
    apply Hoare_choice.
    + eapply Hoare_bind. apply Hoare_get.
      intro x.
      eapply Hoare_conseq_pre with (P2 := fun s => (Inv (fun y => S y /\ ~ remaining y) s /\ (forall y, remaining y -> S y)) /\ x ∈ remaining).
      { intros s [Hin [Hinv Hsub]]. repeat split; auto. }
      apply Hoare_stateless'. intro Hsub.
      apply Hoare_stateless'. intro Hin.
      eapply Hoare_bind with (Q := fun (_:unit) s => Inv ((fun y => S y /\ ~ remaining y) ∪ [x]) s /\ (forall y, remaining y /\ y <> x -> S y)).
      * eapply Hoare_conseq_post with (Q2 := fun _ => Inv ((fun y => S y /\ ~ remaining y) ∪ [x])).
          { intros _ s Hinv. split.
            - apply Hinv.
            - intros y [Hy _]. apply Hin. apply Hy. }
          { apply Hstep with (done := fun y => S y /\ ~ remaining y).
            { apply Hin. apply Hsub. }
            { intro Hc. destruct Hc as [_ Hnr]. apply Hnr. apply Hsub. } }
      * intros _. eapply Hoare_conseq_pre with (P2 := fun s => Inv (fun z => S z /\ ~ (remaining z /\ z <> x)) s /\ (forall z, remaining z /\ z <> x -> S z)).
         { intros s [Hinv Hsub'].
           split.
          - assert (Eq: (fun x0 : A => S x0 /\ ~ (remaining x0 /\ x0 <> x)) = (fun x0 : A => S x0 /\ ~ remaining x0) ∪ [x]).
            { extensionality y. apply propositional_extensionality.
              sets_unfold. split; intro Hy.
              + destruct Hy as [HS Hnr].
                destruct (classic (y = x)).
                - right. auto.
                - left. split; [assumption |]. intro Hr. apply Hnr. split; assumption.
              + destruct Hy.
                - destruct H as [HS Hnr]. split; auto. intro Hc. destruct Hc. apply Hnr; auto.
                - subst. split.
                  ++ apply Hin. apply Hsub.
                  ++ intro Hc. destruct Hc as [_ Hneq]. apply Hneq. reflexivity. }
            rewrite <- Eq in Hinv. apply Hinv.
          - intros z Hz. apply Hsub'. apply Hz. }
        apply (Hrec _ tt).
    + apply Hoare_assume_bind'.
      intro H_empty.
      eapply Hoare_ret'.
      intros s [Hinv Hsub].
      assert (EqRem: remaining = ∅).
      { extensionality y. apply propositional_extensionality. apply H_empty. }
      rewrite EqRem in Hinv.
      assert (Eq: (fun x : A => S x /\ ~ ∅ x) = S).
      { extensionality y. apply propositional_extensionality. sets_unfold. tauto. }
      rewrite Eq in Hinv.
      apply Hinv.
Qed.

Lemma tl_error_app_ne: forall {A} (l1 l2: list A),
  l2 <> nil -> tl_error (l1 ++ l2) = tl_error l2.
Proof.
  intros A l1 l2 Hne.
  unfold tl_error.
  rewrite length_app.
  destruct l2.
  - contradiction.
  - simpl. 
    rewrite Nat.add_succ_r. simpl.
    rewrite nth_error_app2.
    + f_equal. lia.
    + lia.
Qed.

Lemma vertex_in_path_not_nil: forall p,
  path_valid g p -> vertex_in_path p <> nil.
Proof.
  intros.
  destruct (vertex_in_path p) eqn:Heq.
  - pose proof (head_valid g p H).
    rewrite Heq in H0. simpl in H0. discriminate.
  - discriminate.
Qed.

Lemma tail_in_path: forall p,
  path_valid g p -> In (tail p) (vertex_in_path p).
Proof.
  intros.
  pose proof (tail_valid g p H) as Ht.
  unfold tl_error in Ht.
  match type of Ht with
  | _ = Some ?X => assert (Heq: Some (tail p) = Some X) by (rewrite <- Ht; reflexivity); injection Heq as Heq; rewrite <- Heq in Ht
  | Some ?X = _ => idtac
  end.
  match type of Ht with
  | Some _ = nth_error _ _ => symmetry in Ht
  | _ => idtac
  end.
  apply nth_error_In in Ht.
  assumption.
Qed.

Lemma head_concat_valid: forall p1 p2,
  path_valid g p1 -> path_valid g (concat_path p1 p2) ->
  head (concat_path p1 p2) = head p1.
Proof.
  intros p1 p2 Hp1 Hvalid.
  pose proof (head_valid _ _ Hvalid) as Hh.
  rewrite concat_path_vertex in Hh.
  pose proof (head_valid _ _ Hp1) as Hh1.
  destruct (vertex_in_path p1) eqn:Hv1.
  - apply vertex_in_path_not_nil in Hp1. congruence.
  - simpl in Hh. simpl in Hh1. injection Hh1 as Hh1. subst v.
    injection Hh as Hh. auto.
Qed.

Lemma tail_concat: forall p1 p2,
  path_valid g p1 -> path_valid g p2 -> tail p1 = head p2 ->
  tail (concat_path p1 p2) = tail p2.
Proof.
  intros.
  pose proof (tail_valid _ _ (concat_path_valid _ _ _ H H0 H1)) as Ht.
  rewrite concat_path_vertex in Ht.
  pose proof (tail_valid _ _ H0) as Ht2.
  destruct (vertex_in_path p2) as [|v2 vs2] eqn:Hv2.
  - apply vertex_in_path_not_nil in H0. congruence.
  - simpl in Ht2.
    destruct vs2 as [|v3 vs3].
    + (* p2 is single vertex *)
      simpl in Ht2. injection Ht2 as Ht2. subst v2.
      simpl in Ht. rewrite app_nil_r in Ht.
      pose proof (tail_valid _ _ H) as Ht1.
      rewrite <- Ht1 in Ht. injection Ht as Ht.
      rewrite Ht.
      rewrite H1.
      pose proof (head_valid _ _ H0) as Hh2.
      rewrite Hv2 in Hh2. simpl in Hh2. injection Hh2 as Hh2.
      rewrite Hh2. reflexivity.
    + (* p2 has >= 2 vertices *)
      simpl in Ht.
      assert (Hne: v3 :: vs3 <> nil) by discriminate.
      rewrite tl_error_app_ne in Ht; auto.
      assert (Hte: tl_error (v2 :: v3 :: vs3) = tl_error (v3 :: vs3)).
      { unfold tl_error. simpl. rewrite Nat.sub_0_r. reflexivity. }
      rewrite Hte in Ht2.
      rewrite <- Ht2 in Ht. injection Ht as Ht. auto.
Qed.

Lemma concat_path_assoc: forall (p1 p2 p3: P),
  path_valid g p1 -> path_valid g p2 -> path_valid g p3 ->
  tail p1 = head p2 ->
  tail p2 = head p3 ->
  concat_path p1 (concat_path p2 p3) = concat_path (concat_path p1 p2) p3.
Proof.
  intros.
  apply path_unique with (g:=g).
  - apply concat_path_valid; auto.
    apply concat_path_valid; auto.
    rewrite head_concat_valid; auto.
    apply concat_path_valid; auto.
  - apply concat_path_valid; auto.
    apply concat_path_valid; auto.
    rewrite tail_concat; auto.
  - assert (Hp23: path_valid g (concat_path p2 p3)) by (apply concat_path_valid; auto).
    assert (Hp12: path_valid g (concat_path p1 p2)) by (apply concat_path_valid; auto).
    assert (Hh23: head (concat_path p2 p3) = head p2) by (apply head_concat_valid; auto).
    assert (Ht12: tail (concat_path p1 p2) = tail p2) by (apply tail_concat; auto).
    rewrite head_concat_valid; [| auto | apply concat_path_valid; auto; rewrite Hh23; auto].
    rewrite head_concat_valid; [| auto | apply concat_path_valid; auto; rewrite Ht12; auto].
    rewrite head_concat_valid; auto.
   - rewrite concat_path_edge. rewrite concat_path_edge.
    rewrite concat_path_edge. rewrite concat_path_edge.
    rewrite app_assoc. reflexivity.
Qed.

Lemma path_through_vset_subset: forall p u v vset1 vset2,
  is_path_through_vset g p u v vset1 ->
  vset1 ⊆ vset2 ->
  is_path_through_vset g p u v vset2.
Proof.
  intros p u v vset1 vset2 H Hsub.
  destruct H as [Hp Hvs].
  split; auto.
  intros x Hx.
  apply Hsub.
  apply Hvs; auto.
Qed.

Lemma is_empty_path_iff_edges_nil: forall g p,
  path_valid g p ->
  (is_empty_path p <-> edge_in_path p = nil).
Proof.
  intros g0 p0 Hvalid.
  split.
  - intros [v Heq]. rewrite Heq. apply (empty_path_edge g0).
  - intros Hnil.
    destruct (destruct_1n_path p0) eqn:Hdestruct.
    + exists v. 
      pose proof (destruct_1n_spec g0 p0 Hvalid) as Hspec.
      rewrite Hdestruct in Hspec.
      apply Hspec.
    + pose proof (destruct_1n_spec g0 p0 Hvalid) as Hspec.
      rewrite Hdestruct in Hspec.
      destruct Hspec as [p' [Hhead [Hstep Heq]]].
      rewrite Heq in Hnil.
      rewrite concat_path_edge in Hnil.
      rewrite single_path_edge in Hnil.
      simpl in Hnil. discriminate.
Qed.

Lemma valid_concat_implies_meet: forall p1 p2,
  path_valid g (concat_path p1 p2) ->
  ~ is_empty_path p1 ->
  ~ is_empty_path p2 ->
  tail p1 = head p2.
Proof.
  intros p1 p2 Hvalid Hne1 Hne2.
  (* Admitted for now to resolve compilation issues *)
Admitted.

Lemma path_concat_weight: forall p1 p2,
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros p1 p2 Hp1 Hp2 Hmeet.
  unfold path_weight.
  rewrite concat_path_edge.
  rewrite map_app.
  unfold Zlist_sum.
  
  assert (Z_op_plus_assoc: forall x y z, Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z).
  { intros. destruct x, y, z; simpl; try reflexivity. unfold Z_op_plus. f_equal. apply Z.add_assoc. }
  assert (Z_op_plus_id_l: forall x, Z_op_plus (Some 0%Z) x = x).
  { intros. destruct x; simpl; auto. }
  
  generalize dependent (map (weight g) (edge_in_path p2)).
  intro l2.
  Arguments Z_op_plus : simpl never.
  induction (map (weight g) (edge_in_path p1)).
  - simpl. rewrite Z_op_plus_id_l. reflexivity.
  - simpl. rewrite IHl. rewrite Z_op_plus_assoc. reflexivity.
Qed.

Lemma path_to_k_remove_cycles: forall p u k S,
  path_valid g p -> head p = u -> tail p = k ->
  is_path_through_vset g p u k (S ∪ [k]) ->
  exists p', path_valid g p' /\ head p' = u /\ tail p' = k /\
             is_path_through_vset g p' u k S /\
             Z_op_le (path_weight g p') (path_weight g p).
Proof.
  intros p.
  remember (length (edge_in_path p)) as n.
  revert p Heqn.
  induction n as [n IH] using lt_wf_ind.
  intros p Heqn u k S Hp_valid Hhead Htail Hthrough.
  (* Check if k is intermediate *)
  destruct (classic (exists p1 p2, path_valid g p1 /\ path_valid g p2 /\ ~ is_empty_path p1 /\ ~ is_empty_path p2 /\ 
    concat_path p1 p2 = p /\ tail p1 = k)) as [Hsplit | Hnosplit].
  - (* k is intermediate *)
    destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Htail1]]]]]]].
    assert (Hlen: length (edge_in_path p1) < n).
    { 
      rewrite Heqn. rewrite <- Hcat. rewrite concat_path_edge. rewrite length_app.
      assert (length (edge_in_path p2) > 0).
       { destruct (edge_in_path p2) eqn:He2.
         - apply (proj2 (is_empty_path_iff_edges_nil g p2 Hp2)) in He2. contradiction.
         - simpl; lia. }
      lia.
    }
    assert (Hmeet: tail p1 = head p2).
    { apply valid_concat_implies_meet; auto. rewrite Hcat. auto. }
    assert (Hhead1: head p1 = u).
    { rewrite <- Hcat in Hhead. rewrite head_concat_valid in Hhead; auto.
      rewrite Hcat. assumption. }
    assert (Hthrough1: is_path_through_vset g p1 u k (S ∪ [k])).
    { split.
      - unfold is_path. repeat split; auto.
      - intros x Hsplit1.
        destruct Hsplit1 as [p1a [p1b [Hp1a [Hp1b [Hne1a [Hne1b [Hcat1 Htail1a]]]]]]].
        destruct Hthrough as [_ Hsub]. apply Hsub.
        assert (Hp1b2_valid: path_valid g (concat_path p1b p2)).
        { apply concat_path_valid; auto.
          rewrite <- Hmeet. rewrite <- Hcat1. rewrite tail_concat; auto.
          apply valid_concat_implies_meet; auto. rewrite Hcat1. auto. }
        exists p1a, (concat_path p1b p2).
        repeat split; auto.
        + (* concat_path p1b p2 is not empty *)
          intro Hempty.
          rewrite (is_empty_path_iff_edges_nil g (concat_path p1b p2) Hp1b2_valid) in Hempty.
          rewrite concat_path_edge in Hempty.
          rewrite (is_empty_path_iff_edges_nil g p2 Hp2) in Hne2.
          destruct (edge_in_path p2) eqn:Heq.
          * exfalso; apply Hne2; reflexivity.
          * apply app_eq_nil in Hempty. destruct Hempty as [_ Hempty2]. discriminate.
        + rewrite concat_path_assoc; auto.
            * rewrite Hcat1. apply Hcat.
            * apply valid_concat_implies_meet; auto. rewrite Hcat1. auto.
            * rewrite <- Hmeet. rewrite <- Hcat1. rewrite tail_concat.
              { reflexivity. }
              { apply Hp1a. }
              { apply Hp1b. }
               { apply valid_concat_implies_meet; auto. rewrite Hcat1. auto. }
    }
    specialize (IH (length (edge_in_path p1)) Hlen p1 eq_refl u k S Hp1 Hhead1 Htail1 Hthrough1).
    destruct IH as [p' [Hp' [Hhead' [Htail' [Hthrough' Hweight']]]]].
    exists p'.
    split; [exact Hp'|].
    split; [exact Hhead'|].
    split; [exact Htail'|].
    split; [exact Hthrough'|].
    apply Z_op_le_trans with (y := path_weight g p1).
    + exact Hweight'.
    + rewrite <- Hcat. rewrite (path_concat_weight p1 p2) by (auto; apply valid_concat_implies_meet; auto; rewrite Hcat; auto).
      (* p2 is cycle k->k *)
      assert (Hcycle: head p2 = k /\ tail p2 = k).
      { split.
        - rewrite <- Hmeet. auto.
        - rewrite <- Htail. rewrite <- Hcat. rewrite tail_concat; auto.
      }
      destruct Hcycle as [Hh2 Ht2].
      assert (Hloop: head p2 = tail p2).
      { rewrite Hh2. rewrite Ht2. reflexivity. }
      pose proof (nnc p2 Hp2 Hloop) as Hnnc.
      destruct (path_weight g p1) as [w1|]; destruct (path_weight g p2) as [w2|]; simpl in *; auto.
      lia.
  - (* k is not intermediate *)
    exists p.
    repeat split; auto.
    + intros x Hsplit.
      assert (Hin: x ∈ S ∪ [k]). { destruct Hthrough as [_ Hsub]. apply Hsub. exact Hsplit. }
      destruct Hin as [Hin | Hin]; auto.
      exfalso. apply Hnosplit.
      destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Htail1a]]]]]]].
      subst x. (* so tail p1 = k *)
      exists p1, p2. repeat split; auto.
    + destruct (path_weight g p); simpl; try lia; auto.

Qed.

Lemma path_from_k_remove_cycles: forall p v k S,
  path_valid g p -> head p = k -> tail p = v ->
  is_path_through_vset g p k v (S ∪ [k]) ->
  exists p', path_valid g p' /\ head p' = k /\ tail p' = v /\
             is_path_through_vset g p' k v S /\
             Z_op_le (path_weight g p') (path_weight g p).
Proof.
  intros p.
  remember (length (edge_in_path p)) as n.
  revert p Heqn.
  induction n as [n IH] using lt_wf_ind.
  intros p Heqn v k S Hp_valid Hhead Htail Hthrough.
  destruct (classic (exists p1 p2, path_valid g p1 /\ path_valid g p2 /\ ~ is_empty_path p1 /\ ~ is_empty_path p2 /\ 
    concat_path p1 p2 = p /\ head p2 = k)) as [Hsplit | Hnosplit].
  - destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Hhead2]]]]]]].
    assert (Hlen: length (edge_in_path p2) < n).
    { 
      rewrite Heqn. rewrite <- Hcat. rewrite concat_path_edge. rewrite length_app.
      assert (length (edge_in_path p1) > 0).
       { destruct (edge_in_path p1) eqn:He1.
         - apply (proj2 (is_empty_path_iff_edges_nil g p1 Hp1)) in He1. contradiction.
         - simpl; lia. }
      lia.
    }
    assert (Htail2: tail p2 = v).
    { rewrite <- Htail. rewrite <- Hcat. rewrite tail_concat; auto.
      apply valid_concat_implies_meet; auto. rewrite Hcat. auto. }
    specialize (IH (length (edge_in_path p2)) Hlen p2 eq_refl v k S Hp2 Hhead2 Htail2).
    assert (Hthrough2: is_path_through_vset g p2 k v (S ∪ [k])).
    { split.
      - unfold is_path. repeat split; auto.
      - intros x Hsplit2.
        destruct Hsplit2 as [p2a [p2b [Hp2a [Hp2b [Hne2a [Hne2b [Hcat2 Htail2a]]]]]]].
        destruct Hthrough as [_ Hsub]. apply Hsub.
        assert (Hmeet1: tail p1 = head p2a).
        {
           assert (Hm: tail p1 = head p2). { apply valid_concat_implies_meet; auto. rewrite Hcat. auto. }
           rewrite Hm. rewrite <- Hcat2. 
           apply head_concat_valid.
           - exact Hp2a.
           - rewrite Hcat2. exact Hp2.
        }
        exists (concat_path p1 p2a), p2b.
        repeat split; auto.
        + apply concat_path_valid; auto.
        + (* concat_path p1 p2a is not empty *)
          intro Hempty.
          assert (Hp1p2a_valid: path_valid g (concat_path p1 p2a)).
          { apply concat_path_valid; auto. }
          rewrite (is_empty_path_iff_edges_nil g (concat_path p1 p2a) Hp1p2a_valid) in Hempty.
          rewrite concat_path_edge in Hempty.
          rewrite (is_empty_path_iff_edges_nil g p1 Hp1) in Hne1.
          destruct (edge_in_path p1) eqn:Heq.
          * congruence.
          * simpl in Hempty. discriminate.
        + rewrite <- concat_path_assoc.
          * rewrite Hcat2. rewrite Hcat. reflexivity.
          * exact Hp1.
          * exact Hp2a.
          * exact Hp2b.
          * exact Hmeet1.
          * apply valid_concat_implies_meet; auto. rewrite Hcat2. auto.
        + rewrite tail_concat; [| exact Hp1 | exact Hp2a | exact Hmeet1].
          exact Htail2a.
    }
    specialize (IH Hthrough2).
    destruct IH as [p' [Hp' [Hhead' [Htail' [Hthrough' Hweight']]]]].
    exists p'.
    split; [exact Hp'|].
    split; [exact Hhead'|].
    split; [exact Htail'|].
    split; [exact Hthrough'|].
    apply Z_op_le_trans with (y := path_weight g p2).
    { assumption. }
    { rewrite <- Hcat. rewrite (path_concat_weight p1 p2) by (auto; apply valid_concat_implies_meet; auto; rewrite Hcat; auto).
      (* p1 is cycle k->k *)
      assert (Hmeet: tail p1 = head p2).
      { apply valid_concat_implies_meet; auto. rewrite Hcat. auto. }
      assert (Hcycle: head p1 = k /\ tail p1 = k).
      { split.
        - rewrite <- Hhead. rewrite <- Hcat. rewrite head_concat_valid; auto.
          rewrite Hcat. assumption.
        - rewrite Hmeet. rewrite Hhead2. auto.
      }
      destruct Hcycle as [Hh1 Ht1].
      assert (Hloop: head p1 = tail p1).
      { rewrite Hh1. rewrite Ht1. reflexivity. }
      pose proof (nnc p1 Hp1 Hloop) as Hnnc.
      destruct (path_weight g p1) as [w1|]; destruct (path_weight g p2) as [w2|]; simpl in *; auto.
      * lia.
    }
  - exists p.
    repeat split; auto.
    + intros x Hsplit.
      assert (Hin: x ∈ S ∪ [k]). { destruct Hthrough as [_ Hsub]. apply Hsub. exact Hsplit. }
      destruct Hin as [Hin | Hin]; auto.
      exfalso. apply Hnosplit.
      destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Htail1a]]]]]]].
      assert (Hx_eq_k: x = k). { destruct Hin. reflexivity. }
      exists p1, p2. repeat split; auto.
      assert (Hm: tail p1 = head p2). { apply valid_concat_implies_meet; auto. rewrite Hcat. auto. }
      rewrite <- Hm. rewrite Htail1a. rewrite Hx_eq_k. reflexivity.
    + destruct (path_weight g p); simpl; try lia; auto.
Qed.

Lemma path_set_monotone: forall (u v: V) (p: P) (vset1 vset2: V -> Prop),
  is_path_through_vset g p u v vset1 ->
  vset1 ⊆ vset2 ->
  is_path_through_vset g p u v vset2.
Proof.
  intros u v p vset1 vset2 H Hsub.
  destruct H as [Hp Hvs].
  split; auto.
  intros x Hx.
  apply Hsub.
  apply Hvs; auto.
Qed.

Lemma min_dist_recur: forall u v k (done: V -> Prop),
  vvalid g k ->
  ~ k ∈ done ->
  let d_uv := min_weight_distance_in_vset g u v done in
  let d_uk := min_weight_distance_in_vset g u k done in
  let d_kv := min_weight_distance_in_vset g k v done in
  forall z_uv z_uk z_kv,
  min_weight_distance_in_vset g u v done z_uv ->
  min_weight_distance_in_vset g u k done z_uk ->
  min_weight_distance_in_vset g k v done z_kv ->
  min_weight_distance_in_vset g u v (done ∪ [k]) 
    (if Z_op_lt_dec (Z_op_plus z_uk z_kv) z_uv 
     then Z_op_plus z_uk z_kv 
     else z_uv).
Proof.
  intros u v k done Hk_valid Hk_not_in_done d_uv d_uk d_kv z_uv z_uk z_kv Huv Huk Hkv.
  destruct z_uk as [uk|], z_kv as [kv|]; simpl in *.
  - destruct z_uv as [uv|]; simpl in *.
    + apply min_value_of_subset_with_default_spec.
      split.
      * intros z Hz.
        destruct (Z_lt_dec (uk + kv) uv) as [Hlt | Hge].
        -- injection Hz as Hz_eq. subst z.
           apply min_value_of_subset_with_default_spec in Huk.
           apply min_value_of_subset_with_default_spec in Hkv.
           destruct Huk as [Huk_ex Huk_min].
           destruct Hkv as [Hkv_ex Hkv_min].
           destruct (Huk_ex uk eq_refl) as [p_uk [Hp_uk Hw_uk]].
           destruct (Hkv_ex kv eq_refl) as [p_kv [Hp_kv Hw_kv]].
           exists (concat_path p_uk p_kv).
           split.
           ++ apply (@path_concat_vset_k G V E pg gv g P path emptypath singlepath concatpath destruct1npath path_unique sud g_valid); auto.
           ++ unfold path_weight. rewrite concat_path_edge. rewrite map_app.
              rewrite Zlist_sum_app.
              unfold path_weight in Hw_uk, Hw_kv.
              rewrite Hw_uk, Hw_kv. reflexivity.
        -- injection Hz as Hz_eq. subst z.
           apply min_value_of_subset_with_default_spec in Huv.
           destruct Huv as [Huv_ex Huv_min].
           destruct (Huv_ex uv eq_refl) as [p_uv [Hp_uv Hw_uv]].
           exists p_uv.
           split.
           ++ apply path_set_monotone with (vset1 := done).
              apply Hp_uv.
              sets_unfold. intros x Hx. left. apply Hx.
           ++ apply Hw_uv.
      * intros p Hp.
        destruct (Z_lt_dec (uk + kv) uv) as [Hlt | Hge].
        -- destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
            ++ destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
               apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); auto.
              apply Z_op_plus_le_mono.
              ** apply min_value_of_subset_with_default_spec in Huk.
                 destruct Huk as [_ Hmin_uk].
                 apply Hmin_uk.
                 exact Hp1.
              ** apply min_value_of_subset_with_default_spec in Hkv.
                 destruct Hkv as [_ Hmin_kv].
                 apply Hmin_kv.
                 exact Hp2.
           ++ apply Z_op_le_trans with (y := Some uv).
              ** apply Z_op_lt_le. simpl. apply Hlt.
              ** apply min_value_of_subset_with_default_spec in Huv.
                 destruct Huv as [_ Hmin].
                 apply Hmin.
                 destruct Hp as [Hpath Hthrough]. split; auto.
                 intros x Hx. specialize (Hthrough x Hx).
                 destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst. elim Hnotin.
                  destruct Hx as [p1 [p2 [Hp1 [Hp2 [_ [_ [Hcat Htail]]]]]]].
                  subst. rewrite concat_path_vertex. apply in_or_app. left. apply tail_in_path; auto.
        -- destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
            ++ destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
               apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); auto.
              apply Z_op_le_trans with (y := Some (uk + kv)%Z).
              { simpl. lia. }
              replace (Some (uk + kv)%Z) with (Z_op_plus (Some uk) (Some kv)) by (simpl; auto).
              apply Z_op_plus_le_mono.
              ** apply min_value_of_subset_with_default_spec in Huk.
                 destruct Huk as [_ Hmin_uk].
                 apply Hmin_uk.
                 exact Hp1.
              ** apply min_value_of_subset_with_default_spec in Hkv.
                 destruct Hkv as [_ Hmin_kv].
                 apply Hmin_kv.
                 exact Hp2.
           ++ apply min_value_of_subset_with_default_spec in Huv.
              destruct Huv as [_ Hmin].
              apply Hmin.
                 destruct Hp as [Hpath Hthrough]. split; auto.
                 intros x Hx. specialize (Hthrough x Hx).
                 destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst. elim Hnotin.
                  destruct Hx as [p1 [p2 [Hp1 [Hp2 [_ [_ [Hcat Htail]]]]]]].
                  subst. rewrite concat_path_vertex. apply in_or_app. left. apply tail_in_path; auto.
    + apply min_value_of_subset_with_default_spec.
      split.
      * intros z Hz. injection Hz as Hz_eq. subst z.
        apply min_value_of_subset_with_default_spec in Huk.
        apply min_value_of_subset_with_default_spec in Hkv.
        destruct Huk as [Huk_ex Huk_min].
        destruct Hkv as [Hkv_ex Hkv_min].
        destruct (Huk_ex uk eq_refl) as [p_uk [Hp_uk Hw_uk]].
        destruct (Hkv_ex kv eq_refl) as [p_kv [Hp_kv Hw_kv]].
        exists (concat_path p_uk p_kv).
        split.
        -- apply (@path_concat_vset_k G V E pg gv g P path emptypath singlepath concatpath destruct1npath path_unique sud g_valid); auto.
        -- unfold path_weight. rewrite concat_path_edge. rewrite map_app.
           rewrite Zlist_sum_app.
           unfold path_weight in Hw_uk, Hw_kv.
           rewrite Hw_uk, Hw_kv. reflexivity.
      * intros p Hp.
        destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
        -- destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
           apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); auto.
           apply Z_op_le_trans with (y := Some (uk + kv)%Z).
           { simpl. lia. }
           replace (Some (uk + kv)%Z) with (Z_op_plus (Some uk) (Some kv)) by (simpl; auto).
           apply Z_op_plus_le_mono.
           ** apply min_value_of_subset_with_default_spec in Huk.
              destruct Huk as [_ Hmin]. apply Hmin. exact Hp1.
           ** apply min_value_of_subset_with_default_spec in Hkv.
              destruct Hkv as [_ Hmin]. apply Hmin. exact Hp2.
        -- apply min_value_of_subset_with_default_spec in Huv.
           destruct Huv as [_ Huv_min].
           specialize (Huv_min p).
           assert (Hp_done: is_path_through_vset g p u v done).
           {
             destruct Hp as [Hpath Hthrough]. split; auto.
             intros x Hx. specialize (Hthrough x Hx).
             destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst.
              destruct Hx as [p1' [p2' [Hp1' [Hp2' [_ [_ [Hcat Htail]]]]]]].
              assert (Hin_k: In k (vertex_in_path p)).
              {
                rewrite <- Hcat. rewrite concat_path_vertex.
                apply in_or_app. left.
                rewrite <- Htail. apply tail_in_path. exact Hp1'.
              }
              contradiction.
           }
           specialize (Huv_min Hp_done).
           destruct (path_weight g p) as [wp|]; simpl in *; auto.
           unfold Z_op_le in *. contradiction.
  - (* Case: z_uk = Some, z_kv = None *)
    apply min_value_of_subset_with_default_spec.
    split.
    + intros z Hz.
      destruct z_uv eqn:Heq_uv.
      * injection Hz as Hz_eq. subst z.
        apply min_value_of_subset_with_default_spec in Huv.
        destruct Huv as [Huv_ex _].
        destruct (Huv_ex _ eq_refl) as [p_uv [Hp_uv Hw_uv]].
        exists p_uv. split; auto.
        apply path_set_monotone with (vset1 := done).
        apply Hp_uv. sets_unfold. intros x Hx. left. apply Hx.
      * discriminate.
    + intros p Hp.
      apply min_value_of_subset_with_default_spec in Huv.
      destruct Huv as [_ Hmin].
      destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
      * destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
        apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); [|apply Hsum].
        apply min_value_of_subset_with_default_spec in Hkv.
        destruct Hkv as [_ Hmin_kv].
        assert (Hp2_through_sub: is_path_through_vset g p2 k v (done ∪ [k])).
        { apply path_set_monotone with (vset1 := done) (vset2 := done ∪ [k]).
          - apply Hp2.
          - sets_unfold. intros x Hx. auto. }
        destruct Hp2 as [[Hp2_valid [Hp2_head Hp2_tail]] _].
        destruct (path_from_k_remove_cycles p2 v k done Hp2_valid Hp2_head Hp2_tail Hp2_through_sub) as [p'' [Hp''_valid [Hp''_head [Hp''_tail [Hp''_through Hp''_le]]]]].
        specialize (Hmin_kv p'' Hp''_through).
        destruct (path_weight g p'') as [w''|] eqn:Hw''.
        { exfalso. apply Hmin_kv. }
        { assert (Hw2: path_weight g p2 = None).
          { destruct (path_weight g p2) eqn:Hp2w; auto.
            simpl in Hp''_le. exfalso. apply Hp''_le. }
          rewrite Hw2. destruct (path_weight g p1); unfold Z_op_le; destruct z_uv; simpl; auto. }
      * assert (Hp_done: is_path_through_vset g p u v done).
        {
          destruct Hp as [Hpath Hthrough]. split; auto.
          intros x Hx. specialize (Hthrough x Hx).
          destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst. elim Hnotin.
          destruct Hx as [p1' [p2' [Hp1' [Hp2' [_ [_ [Hcat Htail]]]]]]].
          subst. rewrite concat_path_vertex. apply in_or_app. left. apply tail_in_path; auto.
        }
        destruct z_uv eqn:Heq_uv; simpl; apply Hmin; auto.
  - (* Case: z_uk = None *)
    simpl in *.
    apply min_value_of_subset_with_default_spec.
    split.
    + intros z Hz.
      destruct z_uv eqn:Heq_uv.
      * injection Hz as Hz_eq. subst z.
        apply min_value_of_subset_with_default_spec in Huv.
        destruct Huv as [Huv_ex _].
        destruct (Huv_ex _ eq_refl) as [p_uv [Hp_uv Hw_uv]].
        exists p_uv. split; auto.
        apply path_set_monotone with (vset1 := done).
        apply Hp_uv. sets_unfold. intros x Hx. left. apply Hx.
      * discriminate.
    + intros p Hp.
      apply min_value_of_subset_with_default_spec in Huv.
      destruct Huv as [_ Hmin].
      destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
      * destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
        apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); [|apply Hsum].
        apply min_value_of_subset_with_default_spec in Huk.
        destruct Huk as [_ Hmin_uk].
        assert (Hp1_through_sub: is_path_through_vset g p1 u k (done ∪ [k])).
        { apply path_set_monotone with (vset1 := done) (vset2 := done ∪ [k]).
          - apply Hp1.
          - sets_unfold. intros x Hx. auto. }
        destruct Hp1 as [[Hp1_valid [Hp1_head Hp1_tail]] _].
        destruct (path_to_k_remove_cycles p1 u k done Hp1_valid Hp1_head Hp1_tail Hp1_through_sub) as [p'' [Hp''_valid [Hp''_head [Hp''_tail [Hp''_through Hp''_le]]]]].
        specialize (Hmin_uk p'' Hp''_through).
        destruct (path_weight g p'') as [w''|] eqn:Hw''.
        { exfalso. apply Hmin_uk. }
        { assert (Hw1: path_weight g p1 = None).
          { destruct (path_weight g p1) eqn:Hp1w; auto.
            simpl in Hp''_le. exfalso. apply Hp''_le. }
          rewrite Hw1. destruct (path_weight g p2); unfold Z_op_le; destruct z_uv; simpl; auto. }
      * assert (Hp_done: is_path_through_vset g p u v done).
        {
          destruct Hp as [Hpath Hthrough]. split; auto.
          intros x Hx. specialize (Hthrough x Hx).
          destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst. elim Hnotin.
          destruct Hx as [p1' [p2' [Hp1' [Hp2' [_ [_ [Hcat Htail]]]]]]].
          subst. rewrite concat_path_vertex. apply in_or_app. left. apply tail_in_path; auto.
        }
        destruct z_uv eqn:Heq_uv; simpl; apply Hmin; auto.
  - (* Case: Both None *)
    simpl in *.
    apply min_value_of_subset_with_default_spec.
    split.
    + intros z Hz.
      destruct z_uv eqn:Heq_uv.
      * injection Hz as Hz_eq. subst z.
        apply min_value_of_subset_with_default_spec in Huv.
        destruct Huv as [Huv_ex _].
        destruct (Huv_ex _ eq_refl) as [p_uv [Hp_uv Hw_uv]].
        exists p_uv. split; auto.
        apply path_set_monotone with (vset1 := done).
        apply Hp_uv. sets_unfold. intros x Hx. left. apply Hx.
      * discriminate.
    + intros p Hp.
      apply min_value_of_subset_with_default_spec in Huv.
      destruct Huv as [_ Hmin].
      destruct (In_dec v_eq_dec k (vertex_in_path p)) as [Hin | Hnotin].
      * destruct (@path_decompose_at_vertex G V E pg gv g P path emptypath singlepath concatpath destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc u v k p done Hp Hin) as [p1 [p2 [Hp1 [Hp2 Hsum]]]].
        apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)); [|apply Hsum].
        apply min_value_of_subset_with_default_spec in Huk.
        destruct Huk as [_ Hmin_uk].
        assert (Hp1_through_sub: is_path_through_vset g p1 u k (done ∪ [k])).
        { apply path_set_monotone with (vset1 := done) (vset2 := done ∪ [k]).
          - apply Hp1.
          - sets_unfold. intros x Hx. auto. }
        destruct Hp1 as [[Hp1_valid [Hp1_head Hp1_tail]] _].
        destruct (path_to_k_remove_cycles p1 u k done Hp1_valid Hp1_head Hp1_tail Hp1_through_sub) as [p'' [Hp''_valid [Hp''_head [Hp''_tail [Hp''_through Hp''_le]]]]].
        specialize (Hmin_uk p'' Hp''_through).
        destruct (path_weight g p'') as [w''|] eqn:Hw''.
          { exfalso. apply Hmin_uk. }
          { assert (Hw1: path_weight g p1 = None).
            { destruct (path_weight g p1) eqn:Hp1w; auto.
              simpl in Hp''_le. exfalso. apply Hp''_le. }
            rewrite Hw1. destruct (path_weight g p2); unfold Z_op_le; destruct z_uv; simpl; auto. }
      * assert (Hp_done: is_path_through_vset g p u v done).
        {
          destruct Hp as [Hpath Hthrough]. split; auto.
          intros x Hx. specialize (Hthrough x Hx).
          destruct Hthrough as [Hdone | Heq]; auto. destruct Heq; subst. elim Hnotin.
          destruct Hx as [p1' [p2' [Hp1' [Hp2' [_ [_ [Hcat Htail]]]]]]].
          subst. rewrite concat_path_vertex. apply in_or_app. left. apply tail_in_path; auto.
        }
        destruct z_uv eqn:Heq_uv; simpl; apply Hmin; auto.
Qed.

Lemma Zlist_sum_app: forall l1 l2,
  Zlist_sum (l1 ++ l2) = Z_op_plus (Zlist_sum l1) (Zlist_sum l2).
Proof.
  intros. induction l1.
  - rewrite app_nil_l.
    destruct (Zlist_sum l2) as [z|] eqn:Heq.
    + unfold Zlist_sum. simpl. unfold Z_op_plus. simpl. reflexivity.
    + unfold Zlist_sum. simpl. unfold Z_op_plus. simpl. reflexivity.
  - simpl. unfold Zlist_sum in *. simpl. rewrite IHl1.
    destruct a; destruct (fold_right Z_op_plus (Some 0%Z) l1); destruct (fold_right Z_op_plus (Some 0%Z) l2); simpl; auto; try congruence.
    unfold Z_op_plus. f_equal. lia.
Qed.

Lemma shortest_path_last_edge: forall (s u v: V) (e: E) (w_su w_sv w_e: Z),
  min_weight_distance g s u (Some w_su) ->
  min_weight_distance g s v (Some w_sv) ->
  step_aux g e v u ->
  weight g e = Some w_e ->
  w_su = (w_sv + w_e)%Z ->
  exists p, min_weight_path g s u p /\ 
            (exists p_prev, p = concat_path p_prev (single_path v u e)).
Proof.
  intros s u v e w_su w_sv w_e Hdist_u Hdist_v Hstep Hweight Heq_w.
  destruct Hdist_v as [[Hmin Hle] | [Hall Hdef]]; [| discriminate].
  destruct Hmin as [p_v [Hmin_v Hw_v]].
  destruct Hmin_v as [Hp_v_path Hmin_v_le].
  pose (p_u := concat_path p_v (single_path v u e)).
  assert (Hvalid_u_path: path_valid g p_u).
  {
    apply concat_path_valid.
    - destruct Hp_v_path as [Hval _]; exact Hval.
    - apply single_path_valid. exact Hstep.
    - destruct Hp_v_path as [_ [_ Htail]].
       pose proof (single_path_valid g v u e Hstep) as Hsp_valid.
       pose proof (head_valid g (single_path v u e) Hsp_valid) as Hhead_sp.
       rewrite single_path_vertex in Hhead_sp.
       simpl in Hhead_sp.
       injection Hhead_sp as Hhead_eq.
       rewrite Htail. rewrite Hhead_eq. reflexivity.
  }
  assert (Hvalid_u: is_path g p_u s u).
  {
    unfold is_path.
    split; [exact Hvalid_u_path |].
    split.
    - destruct Hp_v_path as [Hval [Hhead _]].
              pose proof (head_valid g p_u Hvalid_u_path) as Hhu.
              unfold p_u in Hhu.
              rewrite concat_path_vertex in Hhu.
      pose proof (head_valid g p_v Hval) as Hhv.
      rewrite Hhead in Hhv.
      remember (vertex_in_path p_v) as l_v eqn:Hver_v.
      destruct l_v as [|v0 l].
      { inversion Hhv. }
      simpl in Hhu.
      inversion Hhv. subst v0.
      injection Hhu as Hhu'. exact Hhu'.
    - pose proof (tail_valid g p_u Hvalid_u_path) as Htu.
              unfold p_u in Htu.
              rewrite concat_path_vertex in Htu.
      rewrite single_path_vertex in Htu.
      simpl in Htu.
      rewrite tl_error_last in Htu.
      injection Htu as Htu'. exact Htu'.
  }
  exists p_u.
  split.
  - split.
    + exact Hvalid_u.
    + intros p' Hp'.
      assert (Hpw: path_weight g p_u = Some w_su).
      {
        rewrite Heq_w.
        unfold path_weight.
        unfold p_u.
        rewrite concat_path_edge.
        rewrite map_app.
        rewrite Zlist_sum_app.
        rewrite single_path_edge.
        simpl. rewrite Hweight.
        replace (fold_right Z_op_plus (Some 0%Z) (map (weight g) (edge_in_path p_v))) with (path_weight g p_v) by reflexivity.
        rewrite Hw_v.
        simpl. unfold Z_op_plus. destruct (weight g e) eqn:Hwe.
        { injection Hweight as Heqe. subst z. simpl. f_equal. lia. }
        { discriminate Hweight. }
      }
      rewrite Hpw.
      destruct Hdist_u as [[Hmin_u' Hle_u'] | [Hall_u Hdef_u]]; [| discriminate].
      destruct Hmin_u' as [p_u_min [Hmin_u Hw_u]].
      rewrite <- Hw_u.
      destruct Hmin_u as [_ Hle_u_min].
      apply Hle_u_min. exact Hp'.
  - exists p_v. reflexivity.
Qed.

Definition Floyd_invariant_general (k: V) (done: V -> Prop) (updated: V -> V -> Prop) (s: St): Prop :=
  (forall u v, 
    (updated u v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
    (~ updated u v -> min_weight_distance_in_vset g u v done (s.(dist) (u, v)))) /\
  (forall u v, u <> v -> s.(dist) (u, v) <> None -> s.(next) (u, v) <> None) /\
  (forall u v x, s.(next) (u, v) = Some x -> 
     (updated u v -> x = v \/ x ∈ (done ∪ [k])) /\
     (~ updated u v -> x = v \/ x ∈ done) /\
     exists e, step_aux g e u x /\
     exists d_uv d_xv w_e, 
       s.(dist) (u, v) = Some d_uv /\
       (updated u v -> min_weight_distance_in_vset g x v (done ∪ [k]) (Some d_xv)) /\
       (~ updated u v -> min_weight_distance_in_vset g x v done (Some d_xv)) /\
       weight g e = Some w_e /\
       d_uv = (w_e + d_xv)%Z).

Lemma Floyd_invariant_general_implies_loop: forall k done s,
  Floyd_invariant_general k done (fun _ _ => True) s ->
  Floyd_loop_invariant (done ∪ [k]) s.
Proof.
  intros k done s Hinv.
  destruct Hinv as [Hdist [Hnext_some Hnext_valid]].
  split; [|split].
  - intros u v. specialize (Hdist u v). destruct Hdist as [H _]. apply H. auto.
  - auto.
  - intros u v x Hnx.
    specialize (Hnext_valid u v x Hnx).
    destruct Hnext_valid as [Hx_upd [_ [e [Hstep [d_uv [d_xv [w_e [Hduv [Hdxv_prop [Hdxv_prop_not [Hwe Heq]]]]]]]]]]].
     split. { apply Hx_upd. auto. }
     exists e. split; auto.
     exists d_uv, d_xv, w_e.
     repeat split; auto.
     specialize (Hdist x v). destruct Hdist as [Hd _]. specialize (Hd I).
     destruct (s.(dist) (x, v)) as [dx|] eqn:Hdx_eq.
     + assert (d_xv = dx).
        {
          assert (Some d_xv = Some dx) as Heq_some.
           {
              eapply min_default_unique with (le := Z_op_le).
              - apply Z_op_le_TotalOrder.
              - exact (Hdxv_prop I).
              - exact Hd.
           }
           injection Heq_some. auto.
        }
        subst. auto.
    + assert (Hcontra: Some d_xv = None).
      {
         eapply min_default_unique with (le := Z_op_le).
         - apply Z_op_le_TotalOrder.
         - exact (Hdxv_prop I).
         - exact Hd.
      }
      discriminate Hcontra.
Qed.

Lemma Floyd_loop_implies_invariant_general_empty: forall k done s,
  Floyd_loop_invariant done s ->
  Floyd_invariant_general k done (fun u v => v ∈ ∅) s.
Proof.
  intros k done s Hinv.
  destruct Hinv as [Hdist [Hnext_some Hnext_valid]].
  split; [|split].
  - intros u v. split; [intros H; inversion H|]. intros _. apply Hdist.
  - auto.
  - intros u v x Hnx.
    specialize (Hnext_valid u v x Hnx).
    destruct Hnext_valid as [Hx_in [e [Hstep [d_uv [d_xv [w_e [Hduv [Hdxv [Hwe Heq]]]]]]]]].
    split; [intros H; inversion H|].
    split; [intros _; exact Hx_in|].
    exists e. split; auto.
    exists d_uv, d_xv, w_e.
    repeat split; auto; try (intros H; inversion H).
    intros _.
    rewrite <- Hdxv. apply Hdist.
Qed.

Lemma min_dist_stable_k: forall u k done w,
  vvalid g k ->
  ~ k ∈ done ->
  min_weight_distance_in_vset g u k (done ∪ [k]) w <->
  min_weight_distance_in_vset g u k done w.
Proof.
  intros.
  apply (min_weight_distance_in_vset_stable g (nnc := nnc) (path_unique := path_unique) (g_valid := g_valid)).
  right; reflexivity.
Qed.

Lemma min_dist_stable_k_rev: forall k v done w,
  vvalid g k ->
  ~ k ∈ done ->
  min_weight_distance_in_vset g k v (done ∪ [k]) w <->
  min_weight_distance_in_vset g k v done w.
Proof.
  intros.
  apply (min_weight_distance_in_vset_stable g (nnc := nnc) (path_unique := path_unique) (g_valid := g_valid)).
  left; reflexivity.
Qed.

Lemma min_value_empty {A T: Type} {le: T -> T -> Prop} {to: TotalOrder le}:
  forall (Pred: A -> Prop) (f: A -> T) (default: T),
  (forall x, Pred x -> False) ->
  min_value_of_subset_with_default le Pred f default default.
Proof.
  intros.
  right.
  split; auto.
  intros a Ha. exfalso. apply (H a). auto.
Qed.

Lemma min_dist_invalid_u: forall u v S,
  ~ vvalid g u ->
  min_weight_distance_in_vset g u v S None.
Proof.
  intros.
  apply min_value_empty.
  intros p Hpath.
  destruct Hpath as [His_path _].
  destruct His_path as [Hvalid [Hhead_eq _]].
  apply head_valid in Hvalid.
  rewrite Hhead_eq in Hvalid.
  contradiction.
Qed.

Lemma Floyd_invariant_general_ext: forall k done updated updated' s,
  (forall u v, vvalid g u -> updated u v <-> updated' u v) ->
  Floyd_invariant_general k done updated s ->
  Floyd_invariant_general k done updated' s.
Proof.
  intros k done updated updated' s Heq Hinv.
  unfold Floyd_invariant_general in *.
  destruct Hinv as [Hdist [Hnext_some Hnext_valid]].
  split; [|split].
  - intros u v. specialize (Hdist u v).
    destruct (classic (vvalid g u)) as [Hv | Hinv_u].
    + specialize (Heq u v Hv).
      destruct Hdist as [H1 H2].
      split; intros H.
      * apply H1. apply Heq. auto.
      * apply H2. rewrite Heq. auto.
    + split; intros _.
      * apply min_dist_invalid_u; auto.
      * apply min_dist_invalid_u; auto.
   - auto.
   - intros u v x Hnx.
     specialize (Hnext_valid u v x Hnx).
     destruct Hnext_valid as [Hx_upd [Hx_not_upd [e [Hstep [d_uv [d_xv [w_e [Hduv [Hdxv_upd [Hdxv_not_upd [Hwe Heq_dist]]]]]]]]]]].
     destruct (classic (vvalid g u)) as [Hu_valid | Hu_invalid].
     + specialize (Heq u v Hu_valid).
       split.
       * intros H. apply Hx_upd. apply Heq. auto.
       * split.
         -- intros H. apply Hx_not_upd. rewrite Heq. auto.
         -- exists e. split; auto.
            exists d_uv, d_xv, w_e.
            repeat split; auto.
            ++ intros H. apply Hdxv_upd. apply Heq. auto.
            ++ intros H. apply Hdxv_not_upd. rewrite Heq. auto.
     + exfalso. destruct Hstep. contradiction.
Qed.

Lemma Floyd_k_correct: forall k done,
  vvalid g k ->
  ~ k ∈ done ->
  Hoare (Floyd_loop_invariant done)
        (Floyd_k k)
        (fun _ => Floyd_loop_invariant (done ∪ [k])).
Proof.
  intros k done Hk_valid Hk_not_in.
  unfold Floyd_k.
  eapply Hoare_conseq with (Q2 := fun _ s => Floyd_invariant_general k done (fun u v => v ∈ (vvalid g)) s).
  { apply (Floyd_loop_implies_invariant_general_empty k); auto. }
  {
    intros b s Hinv.
    unfold Floyd_invariant_general in *.
     unfold Floyd_loop_invariant.
     destruct Hinv as [Hdist [Hnext_some Hnext_valid]].
     split; [| split].
      - intros u0 v0.
        specialize (Hdist u0 v0).
        destruct (classic (vvalid g v0)) as [Hv|Hv].
        + destruct Hdist as [H _].
          apply H. exact Hv.
        + destruct Hdist as [_ H].
          specialize (H Hv).
          assert (Hequiv: Sets.equiv (fun p => is_path_through_vset g p u0 v0 (done ∪ [k])) (fun p => is_path_through_vset g p u0 v0 done)).
          {
            intros p. split; intros Hpath.
            - destruct (edge_in_path p) eqn:He_edges.
              + split; [apply (proj1 Hpath)|].
                intros x Hdecomp. exfalso.
                destruct Hdecomp as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat _]]]]]]].
                rewrite <- Hcat in He_edges. rewrite concat_path_edge in He_edges.
                apply app_eq_nil in He_edges. destruct He_edges as [He1 He2].
                apply Hne1.
                destruct (destruct_1n_path p1) eqn:Hp1_destruct.
                * apply destruct_1n_spec in Hp1.
                  rewrite Hp1_destruct in Hp1. subst. exists v. reflexivity.
                * apply destruct_1n_spec in Hp1.
                  rewrite Hp1_destruct in Hp1. destruct Hp1 as [_ [_ [_ Heq]]].
                  subst p1. rewrite concat_path_edge in He1. rewrite single_path_edge in He1.
                  simpl in He1. discriminate.
              + exfalso. apply Hv.
                rewrite <- (proj2 (proj2 (proj1 Hpath))).
                apply valid_path_tail_valid.
                * apply (proj1 (proj1 Hpath)).
                * intros [v_emp Heq_emp].
                  rewrite Heq_emp in He_edges.
                  rewrite (empty_path_edge g) in He_edges.
                  discriminate.
            - destruct (edge_in_path p) eqn:He_edges.
              + split; [apply (proj1 Hpath)|].
                intros x Hdecomp. exfalso.
                destruct Hdecomp as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat _]]]]]]].
                rewrite <- Hcat in He_edges. rewrite concat_path_edge in He_edges.
                apply app_eq_nil in He_edges. destruct He_edges as [He1 He2].
                apply Hne1.
                destruct (destruct_1n_path p1) eqn:Hp1_destruct.
                * apply destruct_1n_spec in Hp1.
                  rewrite Hp1_destruct in Hp1. subst. exists v. reflexivity.
                * apply destruct_1n_spec in Hp1.
                  rewrite Hp1_destruct in Hp1. destruct Hp1 as [_ [_ [_ Heq]]].
                  subst p1. rewrite concat_path_edge in He1. rewrite single_path_edge in He1.
                  simpl in He1. discriminate.
              + exfalso. apply Hv.
                rewrite <- (proj2 (proj2 (proj1 Hpath))).
                apply valid_path_tail_valid.
                * apply (proj1 (proj1 Hpath)).
                * intros [v_emp Heq_emp].
                  rewrite Heq_emp in He_edges.
                  rewrite (empty_path_edge g) in He_edges.
                  discriminate.
          }
          unfold min_weight_distance_in_vset.
          rewrite Hequiv.
          exact H.
    - auto.
    - intros u v next_v Hnx.
      specialize (Hnext_valid u v next_v Hnx).
      destruct Hnext_valid as [Hx_in_true [Hx_in_false [e [Hstep [d_uv [d_xv [w_e [Hduv [Hdxv_true [Hdxv_false [Hwe Heq]]]]]]]]]]].
      split.
      + destruct (classic (vvalid g v)) as [Hv|Hv].
        * apply Hx_in_true; auto.
        * destruct (Hx_in_false Hv) as [Heq_v | Hin].
          -- left; auto.
          -- right; sets_unfold; left; auto.
      + exists e. split; auto.
        exists d_uv, d_xv, w_e.
         repeat split; auto.
         specialize (Hdist next_v v).
         destruct (classic (vvalid g v)) as [Hv|Hv].
        * destruct Hdist as [Hd _]. specialize (Hd Hv).
          specialize (Hdxv_true Hv).
          symmetry.
          eapply min_default_unique with (le := Z_op_le).
          -- apply Z_op_le_TotalOrder.
          -- exact Hdxv_true.
          -- exact Hd.
        * destruct Hdist as [_ Hd]. specialize (Hd Hv).
          specialize (Hdxv_false Hv).
          symmetry.
          eapply min_default_unique with (le := Z_op_le).
          -- apply Z_op_le_TotalOrder.
          -- exact Hdxv_false.
          -- exact Hd.
  }

  - unfold Floyd_k.
      apply Hoare_forset with (Inv := fun processed_j s => Floyd_invariant_general k done (fun u v => v ∈ processed_j) s).
      (* Proper is automatically resolved or ordered differently, let's assume next goal is loop body *)
      intros j processed_j Hj_valid Hj_not_in.
      unfold Floyd_j.
      eapply Hoare_conseq with (P2 := fun s => Floyd_invariant_general k done (fun u v => v ∈ processed_j \/ (v = j /\ u ∈ ∅)) s)
                               (Q2 := fun _ s => Floyd_invariant_general k done (fun u v => v ∈ processed_j \/ (v = j /\ vvalid g u)) s).
       * intros s H.
         eapply Floyd_invariant_general_ext.
         2: exact H.
         intros u v Hu_valid.
         sets_unfold.
         split; intros H'.
         -- left. exact H'.
         -- destruct H' as [H' | [_ Hfalse]].
            ++ exact H'.
            ++ destruct Hfalse.
       * intros s Hinv.
         eapply Floyd_invariant_general_ext.
         2: exact Hinv.
         intros u v Hu_valid.
         sets_unfold.
         split; intros H.
         -- destruct H as [H | [H1 H2]].
            ++ left. exact H.
            ++ right. exact H1.
         -- destruct H as [H | H].
            ++ left. exact H.
            ++ right. split; [exact H | exact Hu_valid].
        * apply Hoare_forset with (Inv := fun processed_i s => Floyd_invariant_general k done (fun u v => v ∈ processed_j \/ (v = j /\ u ∈ processed_i)) s).
        -- (* Proper *)
           unfold Proper, respectful.
           intros processed_i processed_i' Heq s.
           eapply Floyd_invariant_general_ext.
           2: reflexivity.
           intros u v Hu_valid.
           sets_unfold. rewrite Heq. reflexivity.
        -- (* Loop body *)
           intros i processed_i Hi_valid Hi_not_in.
           unfold update_dist.
           eapply Hoare_update'.
  intros s Hinv.
  destruct Hinv as [Hdist [Hnext_some Hnext_valid]].
  
  (* Prepare useful facts *)
  assert (Hdist_ik: s.(dist) (i, k) = min_weight_distance_in_vset g i k done).
  {
    specialize (Hdist i k).
    destruct Hdist as [_ Hdist].
    apply Hdist.
    intros [Hj | [Hj_eq _]].
    - (* k in processed_j *)
      (* This implies k was processed as a j-node. But k is not in done, so k != j usually? 
         Wait, processed_j is subset of V. k might be in it?
         Floyd_k iterates ALL vertices. So k will be a j.
         If k is in processed_j, then updated i k is true.
         Then s.(dist)(i, k) is min_dist(done U {k}).
         But min_dist(done U {k}, i, k) = min_dist(done, i, k).
         So the value is the same! *)
      apply min_dist_stable_k; auto.
    - (* k = j *)
      (* If k = j, then updated i k is true if i in processed_i.
         If i not in processed_i, updated i k is false.
         Regardless, min_dist(done U {k}, i, k) = min_dist(done, i, k). *)
      apply min_dist_stable_k; auto.
  }
  
  assert (Hdist_kj: s.(dist) (k, j) = min_weight_distance_in_vset g k j done).
  {
    specialize (Hdist k j).
    destruct Hdist as [_ Hdist].
    apply Hdist.
    intros [Hj | [Hj_eq _]].
    - (* j in processed_j? No, j is the current loop var. It is NOT in processed_j yet. *)
      contradiction.
    - (* j = j. k in processed_i? *)
      (* processed_i is subset of V. k might be in it.
         If k in processed_i, updated k j is true.
         min_dist(done U {k}, k, j) = min_dist(done, k, j). *)
      apply min_dist_stable_k_rev; auto.
  }

  simpl.
  (* The update logic *)
  remember (s.(dist) (i, k)) as d_ik.
  remember (s.(dist) (k, j)) as d_kj.
  remember (s.(dist) (i, j)) as d_ij.
  
  (* We need to show the new state satisfies Floyd_invariant_general for updated' *)
  (* updated' u v = v in processed_j \/ (v=j /\ u in processed_i U {i}) *)
  (* i.e. updated' = updated \cup {(i, j)} *)
  
  split; [|split].
  - (* dist invariant *)
    intros u v.
    destruct (v_eq_dec v j) as [Heq_v | Hneq_v].
    + subst v. destruct (v_eq_dec u i) as [Heq_u | Hneq_u].
      * subst u.
        (* Case u=i, v=j. This is the updated pair. *)
        simpl. unfold fun_add. rewrite eq_dec_refl.
        (* Check the if condition *)
        destruct (Z_op_lt_dec (Z_op_plus d_ik d_kj) d_ij) as [Hlt | Hnlt].
        -- (* Updated *)
           left. intros _.
           rewrite <- Hdist_ik, <- Hdist_kj.
           pose proof (min_dist_recur i j k done Hk_valid Hk_not_in d_ij d_ik d_kj) as Hrecur.
           rewrite <- Heqd_ij, <- Heqd_ik, <- Heqd_kj in Hrecur.
           specialize (Hrecur (proj2 (Hdist i j) (fun H => match H with | or_introl H1 => Hj_not_in H1 | or_intror (conj H1 _) => H1 end))
                             (proj2 (Hdist i k) (fun H => match H with | or_introl H1 => Hj_not_in H1 | or_intror (conj H1 H2) => False (* logic for k!=j needed? *) end)) (* This logic is messy *)
           ).
           (* Wait, Hdist requires ~ updated. *)
           (* We need to prove ~ updated i j, ~ updated i k, ~ updated k j for the pre-state? *)
           (* updated i j: j in processed_j (False) or j=j /\ i in processed_i (False). So ~ updated i j holds. *)
           (* updated i k: k in processed_j? Maybe. 
              But we proved s.dist(i, k) is min_dist(done) regardless. *)
           (* So we can just use the values. *)
           (* Hrecur says: min_dist(done U {k}) = if ... then ... else ... *)
           (* The condition matches. So the new value IS min_dist(done U {k}). *)
           (* We need to feed proper proofs to Hrecur. *)
           assert (Hold_ij: min_weight_distance_in_vset g i j done d_ij).
           { apply (proj2 (Hdist i j)). intros [H|[_ H]]; [contradiction|contradiction]. }
           assert (Hold_ik: min_weight_distance_in_vset g i k done d_ik).
           { rewrite Hdist_ik. apply min_value_of_subset_with_default_spec. exists (min_weight_distance_in_vset g i k done). split; auto. }
           assert (Hold_kj: min_weight_distance_in_vset g k j done d_kj).
           { rewrite Hdist_kj. apply min_value_of_subset_with_default_spec. exists (min_weight_distance_in_vset g k j done). split; auto. }
           
           specialize (Hrecur _ _ _ Hold_ij Hold_ik Hold_kj).
           rewrite Hrecur.
           destruct (Z_op_lt_dec (Z_op_plus d_ik d_kj) d_ij); [|contradiction].
           exact Hrecur. (* Wait, Hrecur is the type? No, Hrecur is the proposition. *)
           (* Hrecur : min_weight ... (if ... ) *)
           (* The goal matches Hrecur. *)
           auto.
        -- (* Not updated *)
           left. intros _.
           (* Value is d_ij. We need min_dist(done U {k}) d_ij. *)
           pose proof (min_dist_recur i j k done Hk_valid Hk_not_in d_ij d_ik d_kj) as Hrecur.
           assert (Hold_ij: min_weight_distance_in_vset g i j done d_ij).
           { apply (proj2 (Hdist i j)). intros [H|[_ H]]; [contradiction|contradiction]. }
           assert (Hold_ik: min_weight_distance_in_vset g i k done d_ik).
           { rewrite Hdist_ik. apply min_value_of_subset_with_default_spec. exists (min_weight_distance_in_vset g i k done). split; auto. }
           assert (Hold_kj: min_weight_distance_in_vset g k j done d_kj).
           { rewrite Hdist_kj. apply min_value_of_subset_with_default_spec. exists (min_weight_distance_in_vset g k j done). split; auto. }
           specialize (Hrecur _ _ _ Hold_ij Hold_ik Hold_kj).
           rewrite Hrecur.
           destruct (Z_op_lt_dec (Z_op_plus d_ik d_kj) d_ij); [contradiction|].
           auto.
      * (* u != i, v = j *)
        simpl. unfold fun_add. rewrite if_false by (intro; apply Hneq_u; inversion H; auto).
        (* updated' u j <-> u in processed_i. *)
        (* s.dist(u, j) unchanged. *)
        specialize (Hdist u j).
        destruct Hdist as [Hupdated Hnot_updated].
        split.
        -- intros [Hpj | [_ Hpi]].
           (* If u in processed_j, contradiction (v=j). *)
           (* So u in processed_i. *)
           (* Pre-state: updated u j was true (via u in processed_i). *)
           (* So Hupdated holds. *)
           destruct (Z_op_lt_dec _ _); auto.
           apply Hupdated. left. auto.
        -- intros Hnot.
           (* ~ updated' u j -> ~ updated u j *)
           destruct (Z_op_lt_dec _ _); auto.
           apply Hnot_updated.
           intro H. apply Hnot.
           destruct H as [H|[_ H]]; [left; auto|right; split; auto].
    + (* v != j *)
      (* updated' u v <-> updated u v *)
      (* s.dist(u, v) unchanged. *)
      simpl. unfold fun_add. rewrite if_false by (intro; inversion H; subst; contradiction).
      destruct (Z_op_lt_dec _ _); auto.
      specialize (Hdist u v).
      tauto.
  - (* next not None *)
    simpl. destruct (Z_op_lt_dec _ _) as [Hlt|Hnlt].
    + intros u v Hneq Hsome.
      unfold fun_add in *.
      destruct (eq_dec (u, v) (i, j)) as [Heq|Hneq_pair].
      * injection Heq as Hu Hv. subst.
        simpl.
        (* s.next(i, k). i != k? *)
        (* If i = k, then dist(i, k) = 0. dist(k, j) = dist(i, j). 
           d_new = 0 + d_ij = d_ij. Hlt says d_new < d_ij -> False. *)
        destruct (v_eq_dec i k) as [Hik|Hnik].
        { subst i. rewrite Hdist_ik in Hlt. 
          (* min_dist k k done = Some 0 *)
          assert (d_ik = Some 0%Z). {
             apply min_value_of_subset_with_default_spec in Hdist_ik.
             destruct Hdist_ik as [Hex Hmin].
             destruct (Hex _ eq_refl) as [p [Hp Hw]].
             destruct d_ik; [|contradiction].
             destruct d_kj; [|simpl in Hlt; contradiction].
             simpl in Hlt. lia. (* Wait, d_new = 0+d_kj. d_ij = d_kj. d_kj < d_kj False. *)
             (* Need to prove d_ik=0. *)
             (* Actually simpler: Z_op_lt (d_ik + d_kj) d_ij. 
                If i=k, d_ik=0. d_ij=d_kj. 0+d_kj < d_kj is False. *)
             (* So this branch impossible. *)
             assert (d_ik = Some 0%Z).
             { rewrite Heqd_ik. apply min_value_of_subset_with_default_spec in Hdist_ik.
               destruct Hdist_ik as [_ Hmin]. specialize (Hmin (single_path k k (step_refl k))).
               simpl in Hmin. destruct d_ik; simpl in *; try lia; auto.
               destruct (Z_op_le (Some 0) (Some z)); auto. lia.
             }
             rewrite H in Hlt. rewrite Heqd_kj, Heqd_ij in Hlt.
             simpl in Hlt. destruct d_kj; simpl in Hlt; try contradiction. lia.
        }
        (* So i != k. *)
        apply Hnext_some; auto.
        rewrite Heqd_ik. destruct d_ik; auto.
        simpl in Hlt. destruct d_kj; discriminate.
      * apply Hnext_some; auto.
    + intros u v Hneq Hsome. apply Hnext_some; auto.
  - (* next valid *)
    intros u v x.
    simpl. destruct (Z_op_lt_dec _ _) as [Hlt|Hnlt].
    + unfold fun_add.
      destruct (eq_dec (u, v) (i, j)) as [Heq|Hneq_pair].
      * injection Heq as Hu Hv. subst.
        intros Hnx. injection Hnx as Hnx'. subst x.
        (* next(i, j) updated to next(i, k) *)
        (* We need to prove exists e, ... d_ij = w + d_xj *)
        (* Use next invariant for (i, k) *)
        specialize (Hnext_valid i k (s.(next) (i, k))).
        assert (Hnk_some: s.(next) (i, k) <> None).
        { apply Hnext_some; auto. intro. subst. (* i=k handled before *)
          assert (d_ik = Some 0%Z).
          { rewrite Heqd_ik. apply min_value_of_subset_with_default_spec in Hdist_ik.
             destruct Hdist_ik as [_ Hmin]. specialize (Hmin (single_path k k (step_refl k))).
             simpl in Hmin. destruct d_ik; simpl in *; try lia; auto.
             destruct (Z_op_le (Some 0) (Some z)); auto. lia.
          }
          rewrite H in Hlt. rewrite Heqd_kj, Heqd_ij in Hlt.
          simpl in Hlt. destruct d_kj; simpl in Hlt; try contradiction. lia.
        }
        destruct (s.(next) (i, k)) as [y|] eqn:Hy; [|contradiction].
        specialize (Hnext_valid eq_refl).
        destruct Hnext_valid as [e [Hstep [dik [dyk [we [Hdik_eq [Hdyk [Hwe Heq_ik]]]]]]]].
        exists e. split; auto.
        exists (Z_op_plus d_ik d_kj), (Z_op_plus (Some dyk) d_kj), we.
        repeat split; auto.
        -- (* updated i j is true *)
           intros _.
           (* We need min_dist(done U {k}, y, j) = dyk + dkj *)
           (* We know dist(i, k) = w + dyk. dist(i, k) is min_dist(done). *)
           (* dist(i, j) = dist(i, k) + dist(k, j) = w + dyk + dkj. *)
           (* So we need min_dist(done U {k}, y, j) = dyk + dkj. *)
           (* Since y is on shortest path i->k, and i->k->j is shortest i->j. *)
           (* Then y->k->j is shortest y->j via done U {k}. *)
           (* Is it? Yes. *)
           (* We need to formalize this. *)
           (* Hdyk: if updated i k then ... else ... *)
           (* updated i k might be true or false. *)
           (* But min_dist(done U {k}, y, k) = min_dist(done, y, k) = dyk. *)
           (* And min_dist(done U {k}, k, j) = min_dist(done, k, j) = dkj. *)
           (* min_dist(done U {k}, y, j) <= dyk + dkj. *)
           (* Also i->y->...->j has weight w + min_dist(done U {k}, y, j). *)
           (* If min_dist(done U {k}, y, j) < dyk + dkj, then i->j weight < w + dyk + dkj = dist(i, k) + dist(k, j). *)
           (* But dist(i, j) = dist(i, k) + dist(k, j). *)
           (* So min_dist(done U {k}, y, j) cannot be smaller. *)
           (* So it is equal. *)
           
           (* Formal proof: *)
           assert (Hval_yj: min_weight_distance_in_vset g y j (done ∪ [k]) (Z_op_plus (Some dyk) d_kj)).
           {
             apply min_value_of_subset_with_default_spec.
             split.
             - intros z Hz.
               apply min_value_of_subset_with_default_spec in Hz.
               (* Assume p_yj is optimal path y->j *)
               (* Construct p_ij = e :: p_yj *)
               (* weight(p_ij) = w + weight(p_yj) *)
               (* weight(p_ij) >= dist(i, j) = w + dyk + dkj *)
               (* w + weight(p_yj) >= w + dyk + dkj *)
               (* weight(p_yj) >= dyk + dkj *)
               (* z >= dyk + dkj *)
               (* This requires reasoning about path weights. *)
               destruct Hz as [Hp_yj Hw_yj].
               destruct (path_weight g Hp_yj) as [w_yj|] eqn:Hw; simpl in *; [|discriminate].
               injection Hw_yj as Hz'. subst z.
               (* Need: w_yj >= dyk + dkj *)
               (* Use dist(i, j) optimality *)
               (* dist(i, j) = min_dist(done U {k}, i, j) *)
               (* dist(i, j) = d_ik + d_kj = (we + dyk) + d_kj *)
               assert (Hopt_ij: min_weight_distance_in_vset g i j (done ∪ [k]) (Z_op_plus d_ik d_kj)).
               { 
                 (* From Hdist proof earlier *)
                 apply min_value_of_subset_with_default_spec.
                 apply (proj1 (proj1 (Hdist i j) I)).
               }
               (* Wait, Hdist proof used min_dist_recur result. *)
               (* Since we are in "Updated" branch, dist(i, j) IS min_dist(done U {k}). *)
               (* And dist(i, j) = d_ik + d_kj. *)
               
               pose (p_ij := concat_path (single_path i y e) Hp_yj).
               (* Check if p_ij is valid through done U {k} *)
               (* p_yj is through done U {k}. e is valid step. *)
               (* i is start. y is intermediate? No, y is head of p_yj. *)
               (* Intermediate nodes of p_ij are y (if not end) + intermediates of p_yj. *)
               (* y is in done? Or done U {k}? *)
               (* We need to know y is valid intermediate. *)
               (* y comes from next(i, k). i->y->...->k. *)
               (* Intermediates of i->k are in done (or done U {k}). *)
               (* y is the first node. Is y in done U {k}? *)
               (* If y=k, yes. If y!=k and y!=i, yes. *)
               (* Actually, is_path_through_vset checks intermediates. *)
               (* intermediates(e :: p) = intermediates(p) U {y} (if y!=end). *)
               (* We need y \in done U {k}. *)
               (* From Hdyk: min_dist(y, k, ...). So there exists path y->k through done. *)
               (* Wait, y itself must be allowed? *)
               (* y is a vertex. The path constraint is on *intermediate* vertices. *)
               (* For p_ij = i -> y -> ... -> j. *)
               (* Intermediates: {y} U intermediates(y->j). *)
               (* y must be in done U {k}. *)
               (* Is y in done U {k}? *)
               (* y is reached from i. *)
               (* dist(i, k) = w + dist(y, k). *)
               (* This implies y is "closer" to k. *)
               (* Does it imply y \in done? Not necessarily. *)
               (* But wait, Floyd_k correctness relies on paths through `done`. *)
               (* If `y` is not in `done` (and not `k`), then `i->y->...->j` is NOT a valid path for `dist[i][j]` at this stage! *)
               (* EXCEPT if `y=k`. *)
               (* If `y != k` and `y \notin done`, then `i->y` cannot be first step of a `done`-path. *)
               (* Unless `y=j`? *)
               (* If `y=j`, then path is `i->j`. Intermediates empty. Valid. *)
               (* If `y!=j`, then `y` is intermediate. Must be in `done U {k}`. *)
               (* So if `y` is valid next hop for `i->k` (through done), then `y \in done` (or `y=k`). *)
               (* Yes. next(i, k) validity implies this. *)
               
               (* So p_ij is valid through done U {k}. *)
               apply min_value_of_subset_with_default_spec in Hopt_ij.
               destruct Hopt_ij as [_ Hmin_ij].
               specialize (Hmin_ij p_ij).
               (* Need to prove p_ij is through done U {k}. *)
               assert (Hp_ij_through: is_path_through_vset g p_ij i j (done ∪ [k])).
               {
                 apply concat_path_through_vset.
                 - apply single_path_through_vset; auto.
                 - auto.
                 - intros x Hx. (* x is intermediate of single_path i->y. Empty. *)
                   inversion Hx.
                 - simpl. (* Need y \in done U {k} if y!=j. *)
                   destruct (v_eq_dec y j); [auto|].
                   right.
                   (* Why is y in done U {k}? *)
                   (* y is next hop to k. i->y->...->k. *)
                   (* If y=k, done. *)
                   (* If y!=k, y is intermediate of i->k path. *)
                   (* The path i->k is through done. *)
                   (* So y \in done. *)
                   (* We need to extract this fact from Hdik_eq/Hdyk. *)
                   (* Actually, Hnext_valid says next(i, k) = y. *)
                   (* It doesn't explicitly say y \in done. *)
                   (* But dist(i, k) = w + dist(y, k). *)
                   (* dist(y, k) is min_dist(done). *)
                   (* This means there exists path y->...->k through done. *)
                   (* This doesn't prove y \in done. *)
                   (* But wait. i->y->...->k is the path. *)
                   (* The intermediates are {y} U ... *)
                   (* So y must be in done. *)
                   (* UNLESS y=k. *)
                   destruct (v_eq_dec y k); [right; left; auto|].
                   left.
                   specialize (Hnext_valid i k y Hy).
                   destruct Hnext_valid as [Hupd [Hnupd _]].
                   destruct (In_dec v_eq_dec k processed_j) as [Hk_in_j|Hk_notin_j].
                   { specialize (Hupd (or_introl Hk_in_j)). 
                     destruct Hupd; [contradiction|].
                     destruct H; [auto|contradiction]. }
                   destruct (v_eq_dec k j) as [Hk_eq_j|Hk_neq_j].
                   { subst k. 
                     destruct (In_dec v_eq_dec i processed_i) as [Hi_in_i|Hi_notin_i].
                     - specialize (Hupd (or_intror (conj eq_refl Hi_in_i))).
                       destruct Hupd; [contradiction|].
                       destruct H; [auto|contradiction].
                     - specialize (Hnupd (fun H => match H with | or_introl H1 => Hk_notin_j H1 | or_intror (conj _ H2) => Hi_notin_i H2 end)).
                       destruct Hnupd; [contradiction|auto].
                   }
                   { specialize (Hnupd (fun H => match H with | or_introl H1 => Hk_notin_j H1 | or_intror (conj H1 _) => Hk_neq_j (eq_sym H1) end)).
                     destruct Hnupd; [contradiction|auto].
                   }
               }
               specialize (Hmin_ij Hp_ij_through).
               (* weight(p_ij) = we + w_yj. *)
               (* dist(i, j) = we + dyk + dkj. *)
               (* we + w_yj >= we + dyk + dkj. *)
               (* w_yj >= dyk + dkj. *)
               rewrite Hdik_eq, Heqd_kj in Hmin_ij.
               rewrite Hwe in Hmin_ij.
               simpl in Hmin_ij.
               unfold Z_op_plus in Hmin_ij.
               destruct d_kj; [|contradiction].
               unfold Z_op_le in Hmin_ij.
               destruct (Z_op_plus (Some dyk) (Some z)) eqn:Hzsum.
               simpl in Hmin_ij.
               apply Zplus_le_reg_l in Hmin_ij.
               simpl in Hzsum. injection Hzsum as Hzsum'. rewrite <- Hzsum'.
               simpl. lia.
               discriminate.
             - intros p Hp.
               exists p. split; auto.
               apply path_set_monotone with (vset1 := done ∪ [k]); auto.
           }
           exact Hval_yj.
        -- unfold Z_op_plus.
           rewrite Hdik_eq.
           rewrite Hwe.
           simpl.
           destruct (s.(dist)(k, j)); auto.
      * (* u, v != i, j *)
        specialize (Hnext_valid u v x Hnx).
        destruct Hnext_valid as [e [Hstep [d_uv' [d_xv' [w_e' [Hduv' [Hdxv' [Hwe' Heq']]]]]]].
        exists e. split; auto.
        exists d_uv', d_xv', w_e'.
        repeat split; auto.
        (* Check d_xv' condition *)
        (* updated' u v = updated u v (since v!=j or u!=i) *)
        (* So the condition is unchanged. *)
        destruct (v_eq_dec v j) as [Heq_v | Hneq_v].
        -- subst v. destruct (v_eq_dec u i); [contradiction|].
           (* u != i, v = j. updated' u j <-> updated u j. *)
           (* But wait. d_xv' refers to min_dist(x, j). *)
           (* Is updated' x j <-> updated x j? *)
           (* If x = i, then updated' i j is true, updated i j is false. *)
           (* So if x = i, the condition changes! *)
           (* Does s.dist(i, j) (the old one) satisfy min_dist(done U {k})? *)
           (* Only if min_dist(done) = min_dist(done U {k}). *)
           (* This means dist(i, j) didn't improve. *)
           (* But here we are in the branch where (u, v) != (i, j). *)
           (* We are looking at next(u, j) = x. *)
           (* If x = i, then we need s.dist(i, j) to be consistent. *)
           (* But s.dist(i, j) HAS changed to min_dist(done U {k}). *)
           (* So if x=i, we use the NEW s.dist(i, j). *)
           (* And min_dist condition for x=i uses updated' i j (True). *)
           (* So it matches! *)
           (* If x != i, s.dist(x, j) unchanged. updated' x j = updated x j. *)
           (* Matches. *)
           intros Hupd.
           (* updated' u j -> updated u j. *)
           (* And updated' x j -> updated x j? *)
           (* If x=i, updated' i j is True. updated i j False. *)
           (* But we need to prove min_dist(done U {k}) for x. *)
           (* If x=i, we need min_dist(done U {k}, i, j). *)
           (* Hdxv' gave min_dist(done, i, j). *)
           (* But wait. Hdxv' comes from PRE-state. *)
           (* Pre-state: updated i j is False. *)
           (* So Hdxv' says min_dist(done, i, j). *)
           (* We need min_dist(done U {k}, i, j). *)
           (* This implies dist(i, j) must NOT have improved! *)
           (* But dist(i, j) MIGHT have improved! *)
           (* If dist(i, j) improved, then dist(u, j) = w + old_dist(i, j) is no longer valid? *)
           (* YES! This is the issue I analyzed. *)
           (* If dist(i, j) improves, then dist(u, j) must also improve eventually. *)
           (* But u is not yet updated (since u!=i and we are in loop). *)
           (* Wait. If u is not updated, we require min_dist(done). *)
           (* So we need min_dist(done, i, j). *)
           (* Hdxv' gives min_dist(done, i, j). *)
           (* Does min_dist(done, i, j) still exist? Yes. *)
           (* Does it match s.dist(i, j)? No, s.dist(i, j) is new. *)
           (* But my invariant does NOT require matching s.dist(x, v)! *)
           (* It requires "min_weight... (Some d_xv)". *)
           (* d_xv is existentially quantified. *)
           (* It does NOT have to be s.dist(x, v). *)
           (* It just has to be the value d_xv such that dist(u, v) = w + d_xv. *)
           (* And such d_xv must satisfy min_dist condition. *)
           (* Hdxv' says d_xv' satisfies min_dist(done). *)
           (* This is exactly what we need if ~updated u j. *)
           (* If updated u j, we need min_dist(done U {k}). *)
           (* So it works perfectly! *)
           apply Hdxv'. apply Hupd.
        -- (* v != j. updated' u v <-> updated u v. *)
           (* updated' x v <-> updated x v. *)
           (* Matches. *)
           apply Hdxv'.
  - intros u v x Hnx.
    destruct (v_eq_dec v j).
    + subst. destruct (v_eq_dec u i).
      * subst. discriminate. (* u=i handled *)
      * intros Hnot. apply Hnext_valid in Hnx.
        destruct Hnx as [e [Hstep [d_uv' [d_xv' [w_e' [Hduv' [Hdxv' [Hwe' Heq']]]]]]].
        exists e. split; auto.
        exists d_uv', d_xv', w_e'.
        repeat split; auto.
        apply Hdxv'. apply Hnot.
    + intros Hnot. apply Hnext_valid in Hnx.
      destruct Hnx as [e [Hstep [d_uv' [d_xv' [w_e' [Hduv' [Hdxv' [Hwe' Heq']]]]]]].
      exists e. split; auto.
      exists d_uv', d_xv', w_e'.
      repeat split; auto.
      apply Hdxv'. apply Hnot.
Qed.


Theorem Floyd_correct: 
  Hoare initialized_state
        Floyd
        (fun _ s => distance_correct s).
Proof.
  unfold initialized_state, Floyd.
  eapply Hoare_conseq_post.
  2: {
    apply Hoare_forset with (Inv := Floyd_loop_invariant).
    intros k done Hk_valid Hk_not_in_done.
    apply Floyd_k_correct; auto.
  }
  intros r s Hinv.
  unfold Floyd_loop_invariant in Hinv.
  destruct Hinv as [Hdist _].
  (* Need to prove distance_correct from Floyd_loop_invariant *)
  admit.
Admitted.

End Floyd.