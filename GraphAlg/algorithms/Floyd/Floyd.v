
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ListLib.Base.Positional.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import GraphLib.examples.floyd.
Require Import Algorithms.MapLib.

Import SetsNotation.
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
        {eq_dec: EqDec (V * V) eq}.

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

Notation step := (step g).
Notation reachable := (reachable g).

Record St: Type := mkSt {
  dist: (V * V) -> option Z;
}.

Instance: Settable St := settable! mkSt <dist>.


(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]) *)
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (Z_op_min (dist0 (i, j)) (Z_op_plus (dist0 (i, k)) (dist0 (k, j)))); dist0 |>).

Definition Floyd_j (k: V) (j: V): program St unit :=
  forset (fun v => vvalid g v) (fun i =>
    update_dist i j k).

(** 对于固定的中间点k，遍历所有顶点对(i,j)进行松弛 *)
Definition Floyd_k (k: V): program St unit :=
  forset (fun v => vvalid g v) (Floyd_j k).

(** Floyd主算法：遍历所有可能的中间点k *)
Definition Floyd: program St unit :=
  forset (fun v => vvalid g v) Floyd_k.


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
*)

Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v,
    min_weight_distance_in_vset g u v done (s.(dist) (u, v)).

(** ===== 正确性规范 ===== *)

(** 健全性：如果dist记录了距离n，则n确实是最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall u v w, s.(dist) (u, v) = w -> min_weight_distance g u v w.

(** 完备性：如果存在最短距离n，则dist正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall u v w, min_weight_distance g u v w -> s.(dist) (u, v) = w.

Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s.

(** ===== 主定理 =====
    
    证明 Floyd 算法的正确性：
    如果初始状态满足空集上的循环不变量，
    则算法结束后，dist 数组正确记录了所有点对之间的最短距离。
*)

Definition initialized_state (s: St): Prop := 
  Floyd_loop_invariant ∅ s.

(** ===== 辅助引理：路径相关 ===== *)

(** 
  判断路径是否为空的可判定性 
  对于任意有效路径p，可以判定它是否为空路径
*)
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

(**
  非空路径的尾节点是有效的
  如果路径p有效且非空，则其尾节点在图中有效
*)
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

(**
  非空路径的首节点是有效的
  如果路径p有效且非空，则其首节点在图中有效
*)
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

(** ===== Floyd算法正确性证明的辅助引理 ===== *)

(**
  引理1：循环不变量的Proper性质
  证明循环不变量在等价集合上的良定义性
*)
Lemma Floyd_loop_invariant_Proper:
  Proper (Sets.equiv ==> eq ==> iff) (fun s st => Floyd_loop_invariant s st).
Proof.
  intros s1 s2 Hs st1 st2 Hst.
  subst st2.
  unfold Floyd_loop_invariant.
  split; intros Hinv u v; specialize (Hinv u v).
  - unfold min_weight_distance_in_vset in *.
    assert (Hpaths: (fun p => is_path_through_vset g p u v s1) == (fun p => is_path_through_vset g p u v s2)).
    {
      intros p. unfold is_path_through_vset.
      split; intros [Hp Hthrough]; split; auto;
      intros x Hsplit; apply Hs; apply Hthrough; auto.
    }
    apply (min_value_of_subset_with_default_congr Z_op_le _ _ Hpaths _ _ eq_refl _ _ eq_refl _ _ eq_refl); auto.
  - unfold min_weight_distance_in_vset in *.
    assert (Hpaths: (fun p => is_path_through_vset g p u v s2) == (fun p => is_path_through_vset g p u v s1)).
    {
      intros p. unfold is_path_through_vset.
      split; intros [Hp Hthrough]; split; auto;
      intros x Hsplit; apply Hs; apply Hthrough; auto.
    }
    apply (min_value_of_subset_with_default_congr Z_op_le _ _ Hpaths _ _ eq_refl _ _ eq_refl _ _ eq_refl); auto.
Qed.

(**
  引理2：更新距离操作的正确性
  证明update_dist操作维护了内层循环的不变量
*)
Lemma update_dist_correct:
  forall (done: V -> Prop) (k j: V) (processed_j processed_i: V -> Prop) (i: V),
    (forall v : V, processed_j v -> vvalid g v) ->
    vvalid g j ->
    ~ processed_j j ->
    (forall v : V, processed_i v -> vvalid g v) ->
    vvalid g i ->
    ~ processed_i i ->
    Hoare
      (fun s' =>
        (forall u,
           (processed_i u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s'.(dist) (u, j))) /\
           (~ processed_i u -> min_weight_distance_in_vset g u j done (s'.(dist) (u, j)))) /\
        (forall u v, v <> j ->
           (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
           (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v)))))
      (update_dist i j k)
      (fun _ s =>
        (forall u,
           ((processed_i ∪ [i]) u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s.(dist) (u, j))) /\
           (~ (processed_i ∪ [i]) u -> min_weight_distance_in_vset g u j done (s.(dist) (u, j)))) /\
        (forall u v, v <> j ->
           (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
           (~ processed_j v -> min_weight_distance_in_vset g u v done (s.(dist) (u, v))))).
Proof.
  intros done k j processed_j processed_i i Hsubset_j Hvalid_j Hnotin_j Hsubset_i Hvalid_i Hnotin_i.
  unfold update_dist.
  eapply Hoare_conseq.
  3: apply Hoare_update.
  - intros s_pre H_pre; exact H_pre.
  - intros _ s [s' [Hupd [Hinv_j Hinv_rest]]].
    subst s.
    (* 辅助引理：当起点或终点是k时，done和done∪{k}的最短距离等价 *)
    assert (Hstable: forall u v w, (u = k \/ v = k) ->
      min_weight_distance_in_vset g u v (done ∪ [k]) w <->
      min_weight_distance_in_vset g u v done w).
    {
      intros u0 v0 w0 H_end0.
      rewrite (min_weight_distance_in_vset_stable g (nnc := nnc) (g_valid := g_valid) (path_unique := path_unique) u0 v0 k done w0 H_end0).
      repeat match goal with
      | [ |- _ <-> _ ] => reflexivity
      | [ |- Destruct1nPath _ _ _ _ _ _ _ _ ] => exact destruct1npath
      | [ |- Destructn1Path _ _ _ _ _ _ _ _ ] => exact destructn1path
      | [ |- PathInd1n _ _ _ _ _ _ _ _ ] => exact ind1npath
      | [ |- PathIndn1 _ _ _ _ _ _ _ _ ] => exact indn1path
      | [ |- NoNegativeCycle _ ] => exact nnc
      | [ |- gvalid _ ] => exact g_valid
      | [ |- StepUniqueDirected _ _ _ ] => exact sud
      | [ |- EmptyPath _ _ _ _ _ ] => exact emptypath
      | [ |- SinglePath _ _ _ _ _ ] => exact singlepath
      | [ |- ConcatPath _ _ _ _ _ ] => exact concatpath
      | [ |- EdgeWeight _ _ ] => exact ew
      | [ |- Graph _ _ _ ] => exact pg
      | [ |- GValid _ ] => exact gv
      | [ |- Path _ _ _ _ ] => exact path
      | [ |- EqDec _ _ ] => exact eq_dec
      | [ |- _ ] => try exact path_unique; assumption
      end.
    }
    split.
    + (* 目标列j已为i更新 *)
      intros u.
      split.
      * intros Hin_i.
        destruct (eq_dec (u, u) (i, i)) as [Heq | Hneq].
        -- assert (u = i) by congruence. subst u.
           simpl. rewrite t_update_eq.
           apply (floyd_relaxation_correct g (nnc := nnc) (g_valid := g_valid) (path_unique := path_unique)).
           { (* i -> k *)
             destruct (eq_dec (k, k) (j, j)) as [Heq_kj | Hneq_kj].
             - (* k = j *)
               assert (k = j) by congruence. subst k.
               destruct (Hinv_j i) as [_ Hres].
               apply Hres; assumption.
             - (* k <> j *)
               assert (Hneq_k: k <> j) by congruence.
               destruct (Hinv_rest i k Hneq_k) as [Hres1 Hres2].
               destruct (classic (processed_j k)) as [Hp | Hnp].
               + rewrite <- Hstable.
                 * apply Hres1; auto.
                 * right; reflexivity.
               + apply Hres2; assumption.
           }
           { (* k -> j *)
             destruct (Hinv_j k) as [Hres1 Hres2].
             destruct (classic (processed_i k)) as [Hp | Hnp].
             + rewrite <- Hstable.
               * apply Hres1; auto.
               * left; reflexivity.
             + apply Hres2; assumption.
           }
           { (* i -> j (old) *)
             destruct (Hinv_j i) as [_ Hres].
             apply Hres; assumption.
           }
        -- (* u <> i *)
           simpl. rewrite t_update_neq; [|congruence].
           assert (Hpi: processed_i u).
           { destruct Hin_i as [Hpi | Heq]; [assumption | congruence]. }
           destruct (Hinv_j u) as [Hres _].
           apply Hres; assumption.
      * intros Hnot_in.
        destruct (eq_dec (u, u) (i, i)) as [Heq | Hneq].
        -- assert (u = i) by congruence. subst u. exfalso. apply Hnot_in. right. reflexivity.
        -- simpl. rewrite t_update_neq; [|congruence].
           destruct (Hinv_j u) as [_ Hres].
           apply Hres. intro Hp. apply Hnot_in. left. assumption.
    + (* 其他列保持不变 *)
      intros u v Hneq.
      simpl. rewrite t_update_neq.
      * apply Hinv_rest; auto.
      * intro Hc. injection Hc as _ Hc_v. symmetry in Hc_v. contradiction.
Qed.

(**
  引理3.1：无效顶点的路径集合等价性
  证明：对于无效的起点u，从u到v的路径集合在done和done∪{k}下是等价的
  这是因为无效顶点不能作为任何非空路径的起点
*)
Lemma invalid_vertex_path_equiv:
  forall (done: V -> Prop) (k u v: V) (w: option Z),
    ~ vvalid g u ->
    min_weight_distance_in_vset g u v (done ∪ [k]) w <->
    min_weight_distance_in_vset g u v done w.
Proof.
  intros done k u v w Hnvu.
  unfold min_weight_distance_in_vset.
  apply min_value_of_subset_with_default_congr; auto.
  intros p. split; intros [Hp Hthrough]; split; auto.
  - (* done ∪ [k] -> done *)
    destruct Hp as [Hp_valid [Hhead Htail_p]].
    intros x Hsplit.
    (* u不有效意味着没有从u出发的非空路径 *)
    assert (His_empty: is_empty_path p).
    {
      destruct (is_empty_path_dec p Hp_valid) as [He|Hne]; auto.
      exfalso.
      (* 如果p非空，则head p有效 *)
      pose proof (valid_path_head_valid p Hp_valid Hne) as Hvalid.
      rewrite Hhead in Hvalid. contradiction.
    }
    (* 空路径没有中间节点，矛盾 *)
    destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hconcat Htail_p1]]]]]]].
    rewrite <- Hconcat in His_empty.
    assert (Hvalid_concat: path_valid g (concat_path p1 p2)).
    { rewrite <- Hconcat in Hp_valid. exact Hp_valid. }
    rewrite (is_empty_path_iff_edges_nil g _ Hvalid_concat) in His_empty.
    rewrite concat_path_edge in His_empty.
    apply app_eq_nil in His_empty.
    destruct His_empty as [He1 He2].
    rewrite <- (is_empty_path_iff_edges_nil g p1 Hp1) in He1.
    contradiction.
  - (* done -> done ∪ [k] *)
    intros x Hsplit. apply Hthrough in Hsplit.
    sets_unfold. left. auto.
Qed.

(**
  引理3.2：Floyd_j内层循环的初始化条件
  证明：在开始处理列j时（processed_i为空），内层循环不变量成立
*)
Lemma Floyd_j_init:
  forall (done: V -> Prop) (k: V) (processed_j: V -> Prop) (j: V) (s': St),
    (forall u v,
      (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
      (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v)))) ->
    ~ processed_j j ->
    (forall u,
       (∅ u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s'.(dist) (u, j))) /\
       (~ ∅ u -> min_weight_distance_in_vset g u j done (s'.(dist) (u, j)))) /\
    (forall u v, v <> j ->
       (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
       (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v)))).
Proof.
  intros done k processed_j j s' Hinv' Hnotin_j.
  split.
  - (* 关于列j：空集情况 *)
    intros u. split.
    + (* 空集中没有元素 *)
      intros Hf; exfalso; apply Hf.
    + (* 不在空集中，使用原有不变量 *)
      intros _.
      pose proof (Hinv' u j) as Hinv_inst.
      destruct Hinv_inst as [_ Hres]. 
      apply Hres. assumption.
  - (* 关于其他列：保持不变 *)
    intros u v Hneq. apply Hinv'.
Qed.

(**
  引理3.3：Floyd_j内层循环的终止条件
  证明：当所有行i都处理完毕后，列j的所有距离都已更新
*)
Lemma Floyd_j_final:
  forall (done: V -> Prop) (k: V) (processed_j: V -> Prop) (j: V) (s': St),
    (forall u,
       (vvalid g u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s'.(dist) (u, j))) /\
       (~ vvalid g u -> min_weight_distance_in_vset g u j done (s'.(dist) (u, j)))) ->
    (forall u v, v <> j ->
       (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
       (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v)))) ->
    forall u v,
      ((processed_j ∪ [j]) v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
      (~ (processed_j ∪ [j]) v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v))).
Proof.
  intros done k processed_j j s' Hinv_j Hinv_rest u v.
  destruct (eq_dec (v, v) (j, j)) as [Heq_v | Hneq_v].
  - (* v = j: 刚处理完的列 *)
    assert (v = j) by congruence. subst v.
    split.
    + (* (processed_j ∪ [j]) j总是成立 *)
      intros _.
      destruct (classic (vvalid g u)) as [Hvu | Hnvu].
      * (* u有效：使用Hinv_j *)
        destruct (Hinv_j u) as [Hres _].
        apply Hres. assumption.
      * (* u无效：使用路径等价性 *)
        destruct (Hinv_j u) as [_ Hres].
        specialize (Hres Hnvu).
        rewrite (invalid_vertex_path_equiv done k u j (s'.(dist) (u, j)) Hnvu).
        exact Hres.
    + (* ~ (processed_j ∪ [j]) j是矛盾 *)
      intros Hnot_in.
      exfalso. apply Hnot_in. sets_unfold. right. reflexivity.
  - (* v <> j: 其他列保持不变 *)
    assert (Hv_neq_j: v <> j).
    { intro Hcontra. apply Hneq_v. subst. reflexivity. }
    split.
    + (* v在(processed_j ∪ [j])中 *)
      intros Hin_union.
      sets_unfold in Hin_union.
      destruct Hin_union as [Hpv | Heq_vj].
      * (* v在processed_j中：使用Hinv_rest *)
        destruct (Hinv_rest u v Hv_neq_j) as [Hres _].
        apply Hres. assumption.
      * (* v = j：矛盾 *)
        subst v. contradiction.
    + (* v不在(processed_j ∪ [j])中 *)
      intros Hnot_in.
      assert (Hnpv: ~ processed_j v).
      { intro H. apply Hnot_in. sets_unfold. left. assumption. }
      destruct (Hinv_rest u v Hv_neq_j) as [_ Hres].
      apply Hres. assumption.
Qed.

(**
  引理3.4：Floyd_j内层循环不变量的Proper性质
  证明：内层循环不变量在等价集合上良定义
*)
Lemma Floyd_j_invariant_Proper:
  forall (done: V -> Prop) (k: V) (processed_j: V -> Prop) (j: V),
    Proper (Sets.equiv ==> eq ==> iff)
      (fun (processed_i: V -> Prop) (s': St) =>
        (forall u,
           (processed_i u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s'.(dist) (u, j))) /\
           (~ processed_i u -> min_weight_distance_in_vset g u j done (s'.(dist) (u, j)))) /\
        (forall u v, v <> j ->
           (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
           (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v))))).
Proof.
  intros done k processed_j j.
  intros s1 s2 Hs st1 st2 Hst.
  subst st2.
  split; intros [H1 H2]; split.
  - (* 左到右：第一部分 *)
    intros u. specialize (H1 u). destruct H1 as [H1a H1b].
    assert (Hiff: s1 u <-> s2 u) by (apply Hs).
    destruct Hiff as [Hs12 Hs21].
    split; intros Hin_prop.
    + apply H1a. apply Hs21. assumption.
    + apply H1b. intro H. apply Hin_prop. apply Hs12. assumption.
  - (* 左到右：第二部分 *)
    assumption.
  - (* 右到左：第一部分 *)
    intros u. specialize (H1 u). destruct H1 as [H1a H1b].
    assert (Hiff: s1 u <-> s2 u) by (apply Hs).
    destruct Hiff as [Hs12 Hs21].
    split; intros Hin_prop.
    + apply H1a. apply Hs12. assumption.
    + apply H1b. intro H. apply Hin_prop. apply Hs21. assumption.
  - (* 右到左：第二部分 *)
    assumption.
Qed.

(**
  引理3：中层循环（Floyd_j）的正确性
  证明对于固定的k和j，遍历所有i进行松弛操作后维护循环不变量
  
  证明结构：
  1. 使用Hoare_forset框架处理内层循环
  2. 初始化：应用Floyd_j_init证明空集时不变量成立
  3. 终止：应用Floyd_j_final证明所有行处理完后得到正确后置条件
  4. Proper：应用Floyd_j_invariant_Proper证明良定义性
  5. 循环体：应用update_dist_correct处理每个距离更新
*)
Lemma Floyd_j_correct:
  forall (done: V -> Prop) (k: V) (processed_j: V -> Prop) (j: V),
    (forall v : V, processed_j v -> vvalid g v) ->
    vvalid g j ->
    ~ processed_j j ->
    Hoare
      (fun s' =>
        forall u v,
          (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
          (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v))))
      (Floyd_j k j)
      (fun _ s' =>
        forall u v,
          ((processed_j ∪ [j]) v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
          (~ (processed_j ∪ [j]) v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v)))).
Proof.
  intros done k processed_j j Hsubset_j Hin_j Hnotin_j.
  unfold Floyd_j.
  eapply Hoare_conseq.
  3: apply (Hoare_forset (fun processed_i s' =>
      (forall u,
         (processed_i u -> min_weight_distance_in_vset g u j (done ∪ [k]) (s'.(dist) (u, j))) /\
         (~ processed_i u -> min_weight_distance_in_vset g u j done (s'.(dist) (u, j)))) /\
      (forall u v, v <> j ->
         (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s'.(dist) (u, v))) /\
         (~ processed_j v -> min_weight_distance_in_vset g u v done (s'.(dist) (u, v))))
  )).
  - (* 初始化：应用Floyd_j_init *)
    intros s' Hinv'.
    apply (Floyd_j_init done k processed_j j s' Hinv' Hnotin_j).
  - (* 终止条件：应用Floyd_j_final *)
    intros b s' Hinv.
    destruct Hinv as [Hinv_j Hinv_rest].
    apply (Floyd_j_final done k processed_j j s' Hinv_j Hinv_rest).
  - (* Proper性质：应用Floyd_j_invariant_Proper *)
    apply (Floyd_j_invariant_Proper done k processed_j j).
  - (* 内层循环步骤：应用update_dist_correct *)
    intros processed_i i Hsubset_i Hvalid_i Hnotin_i.
    apply (update_dist_correct done k j processed_j processed_i i 
           Hsubset_j Hin_j Hnotin_j Hsubset_i Hvalid_i Hnotin_i).
Qed.

(**
  引理4：外层循环（Floyd_k）的正确性
  证明对于固定的k，遍历所有顶点对(i,j)进行松弛后维护循环不变量
*)
Lemma Floyd_k_correct:
  forall (done: V -> Prop) (k: V),
    (forall v : V, done v -> vvalid g v) ->
    vvalid g k ->
    ~ done k ->
    Hoare
      (Floyd_loop_invariant done)
      (Floyd_k k)
      (fun _ => Floyd_loop_invariant (done ∪ [k])).
Proof.
  intros done k Hsubset Hin Hnotin.
  unfold Floyd_k.
  eapply Hoare_conseq.
  3: apply (Hoare_forset (fun processed_j s =>
      forall u v,
        (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
        (~ processed_j v -> min_weight_distance_in_vset g u v done (s.(dist) (u, v)))
  )).
  - (* 初始化 *)
    intros s Hinv u v.
    split.
    + intros Hfalse. exfalso. apply Hfalse.
    + intros _. apply Hinv.
  - (* 终止条件：所有j处理完后，循环不变量得到维护 *)
    intros b s Hinv.
    unfold Floyd_loop_invariant.
    intros u v.
    destruct (classic (vvalid g v)) as [Hv | Hnv].
    + destruct (Hinv u v) as [Hres _].
      apply Hres. assumption.
    + destruct (Hinv u v) as [_ Hres].
      specialize (Hres Hnv).
      (* 对于无效的v，路径必为空，所以中间节点集合无关 *)
      assert (Hunchanged: min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v)) <-> min_weight_distance_in_vset g u v done (s.(dist) (u, v))).
      {
        unfold min_weight_distance_in_vset.
        apply min_value_of_subset_with_default_congr; auto.
        intros p.
        split; intros [Hp Hthrough]; split; auto.
        - (* done U [k] -> done *)
          destruct Hp as [Hp_valid [Hhead Htail_p]].
          intros x Hsplit.
          assert (His_empty: is_empty_path p).
          {
            destruct (is_empty_path_dec p Hp_valid) as [He|Hne]; auto.
            exfalso.
            pose proof (valid_path_tail_valid p Hp_valid Hne) as Hvalid.
            rewrite Htail_p in Hvalid. contradiction.
          }
          destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hconcat Htail_p1]]]]]]].
          rewrite <- Hconcat in His_empty.
          assert (Hvalid_concat: path_valid g (concat_path p1 p2)).
          { rewrite <- Hconcat in Hp_valid. exact Hp_valid. }
          rewrite (is_empty_path_iff_edges_nil g _ Hvalid_concat) in His_empty.
          rewrite concat_path_edge in His_empty.
          apply app_eq_nil in His_empty.
          destruct His_empty as [He1 He2].
          rewrite <- (is_empty_path_iff_edges_nil g p1 Hp1) in He1.
          contradiction.
        - (* done -> done U [k] *)
          intros x Hsplit. apply Hthrough in Hsplit.
          unfold Sets.union, Sets.lift_union; simpl.
          left. auto.
      }
      rewrite Hunchanged.
      apply Hres.
  - (* Proper性质 *)
    intros s1 s2 Hs st1 st2 Hst.
    rewrite <- Hst.
    assert (Heqv: forall x, s1 x <-> s2 x) by apply Hs.
    split; intros Hinv u v; specialize (Hinv u v); destruct Hinv as [Hyes Hno].
    + split.
      * intros Hv. apply Hyes. rewrite Heqv. exact Hv.
      * intros Hnv. apply Hno. rewrite Heqv. exact Hnv.
    + split.
      * intros Hv. apply Hyes. rewrite <- Heqv. exact Hv.
      * intros Hnv. apply Hno. rewrite <- Heqv. exact Hnv.
  - (* 中层循环步骤 *)
    intros processed_j j Hsubset_j Hin_j Hnotin_j.
    apply (Floyd_j_correct done k processed_j j Hsubset_j Hin_j Hnotin_j).
Qed.

(**
  ===== 主定理：Floyd算法的正确性 =====
  
  定理陈述：
  如果初始状态满足空集上的循环不变量（即初始化正确），
  则Floyd算法执行后，dist数组正确记录了所有顶点对之间的最短距离。
  
  证明思路：
  1. 使用Hoare_forset框架证明最外层循环
  2. 初始化：空集上的循环不变量由初始状态保证
  3. 循环体：使用Floyd_k_correct证明每次添加新中间节点k后不变量维护
  4. 终止：当done包含所有有效顶点时，得到完整的最短路径距离
*)
Theorem Floyd_correct:
  Hoare initialized_state
        Floyd
        (fun _ s => distance_correct s).
Proof.
  unfold Floyd. 
  eapply Hoare_conseq.
  3: apply (Hoare_forset Floyd_loop_invariant).
  - (* 初始化条件：空集上的循环不变量 *)
    intros s H. exact H.
  - (* 终止条件：从完整的循环不变量推导出正确性 *)
    intros b s0 Hinv.
    split.
    + (* 健全性：如果dist记录了距离w，则w确实是最短距离 *)
      intros u v w Hw.
      specialize (Hinv u v).
      rewrite Hw in Hinv.
      (* 当中间节点集合是全体有效节点时，等价于无限制的最短路径 *)
      assert (Hequiv: min_weight_distance_in_vset g u v (fun v => vvalid g v) w <-> min_weight_distance g u v w).
      {
        unfold min_weight_distance_in_vset, min_weight_distance.
        assert (Hpaths: (fun p => is_path_through_vset g p u v (fun v => vvalid g v)) == (fun p => is_path g p u v)).
        {
          intros p. unfold is_path_through_vset.
          split.
          * intros [Hp Ht]. exact Hp.
          * intros Hp. split.
            -- exact Hp.
            -- intros x Hsplit.
               destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hconcat Htail]]]]]]].
               subst x.
               apply (valid_path_tail_valid p1 Hp1 Hne1).
        }
        rewrite Hpaths. reflexivity.
      }
      apply Hequiv. exact Hinv.
    + (* 完备性：如果w是最短距离，则dist正确记录 *)
      intros u v w Hmin.
      specialize (Hinv u v).
      
      assert (Hequiv: min_weight_distance_in_vset g u v (fun v => vvalid g v) (s0.(dist) (u, v)) <-> min_weight_distance g u v (s0.(dist) (u, v))).
      {
         unfold min_weight_distance_in_vset, min_weight_distance.
         assert (Hpaths: (fun p => is_path_through_vset g p u v (fun v => vvalid g v)) == (fun p => is_path g p u v)).
         {
           intros p. unfold is_path_through_vset.
           split.
           * intros [Hp Ht]. exact Hp.
           * intros Hp. split.
             -- exact Hp.
             -- intros x Hsplit.
                destruct Hsplit as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hconcat Htail]]]]]]].
                subst x.
                apply (valid_path_tail_valid p1 Hp1 Hne1).
         }
         rewrite Hpaths. reflexivity.
      }
      apply Hequiv in Hinv.
      (* 最小值的唯一性保证相等 *)
      eapply (min_default_unique Z_op_le).
      * exact Hinv.
      * exact Hmin.
  - (* Proper性质：循环不变量在等价集合上良定义 *)
    apply Floyd_loop_invariant_Proper.
  - (* 循环体：对每个中间节点k应用Floyd_k *)
    intros done k Hsubset Hin Hnotin.
    apply (Floyd_k_correct done k Hsubset Hin Hnotin).
Qed.

(** ===== 辅助引理：数学运算 ===== *)

(**
  整数列表求和的分配律
  证明：sum(l1 ++ l2) = sum(l1) + sum(l2)
*)
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
    f_equal. lia.
Qed.

(**
  ===== 定理2：最短路径的最后一条边 =====
  
  如果从源点s到顶点u的最短距离等于"从s到v的最短距离加上边e的权重"，
  并且边e连接v到u，那么存在一条从s到u的最短路径，其最后一条边正是e。
  
  这个定理对于重构最短路径非常重要。
*)
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
  (* 分析Hdist_v的结构 *)
  destruct Hdist_v as [[Hmin Hle] | [Hall Hdef]]; [| discriminate].
  destruct Hmin as [p_v [Hmin_v Hw_v]].
  destruct Hmin_v as [Hp_v_path Hmin_v_le].
  (* 构造从s到u的路径：p_u = p_v ++ (v->u) *)
  pose (p_u := concat_path p_v (single_path v u e)).
  (* 证明p_u是有效路径 *)
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
  (* 证明p_u是从s到u的路径 *)
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
      (* 证明p_u的权重等于w_su *)
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
        simpl. f_equal. lia.
      }
      rewrite Hpw.
      (* 利用最小性 *)
      destruct Hdist_u as [[Hmin_u' Hle_u'] | [Hall_u Hdef_u]]; [| discriminate].
      destruct Hmin_u' as [p_u_min [Hmin_u Hw_u]].
      rewrite <- Hw_u.
      destruct Hmin_u as [_ Hle_u_min].
      apply Hle_u_min. exact Hp'.
  - exists p_v. reflexivity.
Qed.

End Floyd.