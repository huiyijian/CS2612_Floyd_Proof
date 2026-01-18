
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

    第四档难度要求：
    1. 证明算法输出确实是最短路径长度
    2. 证明如果 e 是 v 到 u 的边，且 d(s,u) = d(s,v) + length(e)，
       则存在 s 到 u 的最短路径，最后一条边是 e
    3. 额外记录信息使得最后可以构建最短路，并证明其正确性
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
Local Existing Instance eq_dec.
Local Existing Instance v_eq_dec.

Notation step := (step g).
Notation reachable := (reachable g).

(** === 状态定义 ===
    dist: 存储最短距离
    next: 存储路径重建信息 - next[u][v] 表示 u 到 v 最短路径上的下一个顶点
*)
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

(** 松弛操作：dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j])
    同时更新 next 数组 *)
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

(** === 路径重建 === *)
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

Definition reconstruct_path (next: (V * V) -> option V) (u v: V) (limit: nat): list V :=
  reconstruct_path_aux next u v limit.

(** === 核心循环不变量 ===

    Floyd 算法的核心不变量：dist[u][v] 是通过 done 集合中顶点的最短距离
*)
Definition Floyd_dist_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v, min_weight_distance_in_vset g u v done (s.(dist) (u, v)).

(** === 正确性规范 === *)

(** 健全性：如果dist记录了距离d，则d确实是最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall u v d, s.(dist) (u, v) = Some d ->
    min_weight_distance g u v (Some d).

(** 完备性：如果存在最短距离d，则dist正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall u v d, min_weight_distance g u v (Some d) ->
    s.(dist) (u, v) = Some d.

(** 第三档：边的最优性证明
    如果 e 是 v 到 u 的边，且 d(s,u) = d(s,v) + length(e)，
    则存在 s 到 u 的最短路径，最后一条边是 e *)
Definition edge_optimality (s: St): Prop :=
  forall src u v e d_su d_sv w_e,
    s.(dist) (src, u) = Some d_su ->
    s.(dist) (src, v) = Some d_sv ->
    step_aux g e v u ->
    weight g e = Some w_e ->
    d_su = (d_sv + w_e)%Z ->
    exists p, is_path g p src u /\
              path_weight g p = Some d_su /\
              exists p', p = concat_path p' (single_path v u e).

(** 第四档：路径重建正确性 *)
Definition path_reconstruction_correct (s: St): Prop :=
  forall u v d, s.(dist) (u, v) = Some d ->
    exists p, is_path g p u v /\ path_weight g p = Some d.

(** 完整的正确性规范 *)
Definition distance_correct (s: St): Prop :=
  distance_soundness s /\
  distance_completeness s /\
  edge_optimality s /\
  path_reconstruction_correct s.

(** === 辅助引理 === *)

Lemma Z_op_le_refl: forall x, Z_op_le x x.
Proof.
  intros. destruct x; simpl; lia.
Qed.

Lemma Z_op_le_trans: forall x y z, Z_op_le x y -> Z_op_le y z -> Z_op_le x z.
Proof.
  intros. destruct x, y, z; simpl in *; try contradiction; try lia; auto.
Qed.

Lemma Z_op_le_antisym: forall x y, Z_op_le x y -> Z_op_le y x -> x = y.
Proof.
  intros. destruct x, y; simpl in *; try contradiction; try lia; auto.
  f_equal. lia.
Qed.

(** === Hoare_forset 引理 === *)
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

(** === 初始状态定义 === *)
Definition initialized_dist_state (s: St): Prop :=
  Floyd_dist_invariant ∅ s.

(** === 松弛操作的核心引理 === *)

(** 使用库中的 floyd_relaxation_correct *)
Lemma min_dist_recur: forall u v k (done: V -> Prop),
  vvalid g k ->
  ~ k ∈ done ->
  forall z_uv z_uk z_kv,
  min_weight_distance_in_vset g u v done z_uv ->
  min_weight_distance_in_vset g u k done z_uk ->
  min_weight_distance_in_vset g k v done z_kv ->
  min_weight_distance_in_vset g u v (done ∪ [k])
    (Z_op_min z_uv (Z_op_plus z_uk z_kv)).
Proof.
  intros.
  apply (@floyd_relaxation_correct G V E pg gv g P path emptypath singlepath concatpath
         destruct1npath ind1npath indn1path path_unique sud g_valid ew nnc); auto.
Qed.

(** 关键引理：k 作为端点时距离不变 *)
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

(** === Floyd_k 距离正确性证明 ===

    仅证明距离部分的正确性
*)

(** 内层不变量 - 仅距离

    关键点：对于已处理的 j（即 v ∈ updated_j），所有 (u, v) 对的距离满足 done ∪ [k] 的不变量；
    对于未处理的 j（即 v ∉ updated_j），所有 (u, v) 对的距离满足 done 的不变量。

    注意：当 v ∈ updated_j 时，我们需要对所有 u 都满足新的不变量。
    这是因为对于固定的 v = j，内层循环会遍历所有 i，因此在外层循环完成一个 j 后，
    所有 (u, j) 都会被正确更新。
*)
Definition Floyd_dist_inner_inv (k: V) (done: V -> Prop) (updated_j: V -> Prop) (s: St): Prop :=
  forall u v,
    (v ∈ updated_j -> min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
    (~ v ∈ updated_j -> min_weight_distance_in_vset g u v done (s.(dist) (u, v))).

(** 内层最内层不变量 - 对于固定的 j，遍历 i 时的不变量

    这个不变量跟踪：
    1. 对于已经处理过的 i（即 i ∈ processed_i），(i, j) 满足 done ∪ [k] 的不变量
    2. 对于尚未处理的 i，(i, j) 满足 done 的不变量（等待被更新）
    3. 对于 v ≠ j 的情况，保持外层不变量
*)
Definition Floyd_dist_innermost_inv (k: V) (j: V) (done: V -> Prop)
           (processed_j: V -> Prop) (processed_i: V -> Prop) (s: St): Prop :=
  (* 对于 v ∈ processed_j（已完成的 j），所有 u 满足新不变量 *)
  (forall u v, v ∈ processed_j ->
     min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
  (* 对于当前的 j，已处理的 i 满足新不变量 *)
  (forall u, u ∈ processed_i ->
     min_weight_distance_in_vset g u j (done ∪ [k]) (s.(dist) (u, j))) /\
  (* 对于当前的 j，未处理的 i 满足旧不变量 *)
  (forall u, ~ u ∈ processed_i ->
     min_weight_distance_in_vset g u j done (s.(dist) (u, j))) /\
  (* 对于 v ∉ processed_j ∪ [j]，所有 u 满足旧不变量 *)
  (forall u v, ~ v ∈ (processed_j ∪ [j]) ->
     min_weight_distance_in_vset g u v done (s.(dist) (u, v))).

(** single_path 的 is_path 性质 - 提前定义以供后续使用 *)
Lemma single_path_is_path: forall v u e,
  step_aux g e v u ->
  is_path g (single_path v u e) v u.
Proof.
  intros.
  split.
  - apply single_path_valid. exact H.
  - split.
    + pose proof (single_path_valid g v u e H) as Hsp.
      pose proof (head_valid g (single_path v u e) Hsp) as Hhsp.
      rewrite single_path_vertex in Hhsp. simpl in Hhsp.
      injection Hhsp. auto.
    + pose proof (single_path_valid g v u e H) as Hsp.
      pose proof (tail_valid g (single_path v u e) Hsp) as Htsp.
      rewrite single_path_vertex in Htsp. simpl in Htsp.
      unfold tl_error in Htsp. simpl in Htsp.
      injection Htsp. auto.
Qed.

(** 辅助引理：连接路径保持 is_path 性质 - 使用库中的 path_concat_valid *)
Lemma concat_path_is_path: forall (src mid dst: V) (p1 p2: P),
  is_path g p1 src mid ->
  is_path g p2 mid dst ->
  is_path g (concat_path p1 p2) src dst.
Proof.
  intros. apply path_concat_valid with mid; auto.
Qed.

Lemma Floyd_k_dist_correct: forall k done,
  vvalid g k ->
  ~ k ∈ done ->
  Hoare (Floyd_dist_invariant done)
        (Floyd_k k)
        (fun _ => Floyd_dist_invariant (done ∪ [k])).
Proof.
  intros k done Hk_valid Hk_not_in.
  unfold Floyd_k.

  (* 外层循环：遍历所有 j *)
  eapply Hoare_conseq with
    (P2 := fun s => Floyd_dist_inner_inv k done ∅ s)
    (Q2 := fun _ s => Floyd_dist_inner_inv k done (vvalid g) s).
  {
    (* 前置条件转换 *)
    intros s Hinv.
    unfold Floyd_dist_inner_inv.
    intros u v. split.
    - intros Hfalse. sets_unfold in Hfalse. contradiction.
    - intros _. apply Hinv.
  }
  {
    (* 后置条件转换 *)
    intros _ s Hinv.
    unfold Floyd_dist_invariant. intros u v.
    destruct (classic (vvalid g v)) as [Hv|Hnv].
    + specialize (Hinv u v). destruct Hinv as [H _].
      apply H. exact Hv.
    + specialize (Hinv u v). destruct Hinv as [_ H].
      (* v 不是有效顶点 *)
      (* 当 v 无效时，is_path_through_vset 中的中间顶点约束不影响路径集合 *)
      (* 因为对于 u -> v 的路径：*)
      (* 1. 如果路径非空（有边），tail 必须有效 (step_vvalid2)，与 v 无效矛盾 *)
      (* 2. 如果路径为空（u = v），没有中间顶点，所以约束相同 *)
      (* 因此两个路径集合相等 *)
      unfold min_weight_distance_in_vset.
      assert (Hpath_equiv: forall p,
        is_path_through_vset g p u v (done ∪ [k]) <->
        is_path_through_vset g p u v done).
      {
        intros p. split; intros [Hip Hinter]; split; auto.
        - (* done ∪ [k] -> done *)
          intros x Hx.
          specialize (Hinter x Hx).
          destruct Hinter as [Hdone'|Hk_eq]; auto.
          (* x = k 是中间顶点 *)
          unfold Sets.singleton, SetsEle.In in Hk_eq. subst x.
          exfalso.
          (* 如果有中间顶点，路径必须非空 *)
          destruct Hx as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Htail_p1]]]]]]].
          (* p2 非空，所以 tail p2 有效 *)
          (* tail p = tail p2 = v，所以 v 有效，矛盾 *)
          destruct Hip as [Hpv [Hhead_p Htail_p]].
          destruct (destruct_n1_path p2) as [p_base v_base | p2' u2 v2 e2] eqn:Hd2.
          + (* p2 空，与 Hne2 矛盾 *)
            apply Hne2. exists v_base.
            pose proof (destruct_n1_spec _ _ Hp2) as Hs2.
            rewrite Hd2 in Hs2. exact Hs2.
          + (* p2 非空，tail p2 = v2 有效 *)
            pose proof (destruct_n1_spec _ _ Hp2) as Hs2.
            rewrite Hd2 in Hs2.
            destruct Hs2 as [Hp2' [Htail2' [Hstep2 Heq2]]].
            (* tail p = tail p2 = v2 *)
            (* 使用 path_concat_valid (从库中) 来证明 tail (concat p1 p2) = tail p2 *)
            (* 首先证明 v = v2 *)
            (* Hip : is_path g p u v，其中 p = concat_path p1 p2 *)
            (* 由 is_path 定义，tail p = v *)
            (* 我们需要 tail p2 = v2 *)
            (* 由 Heq2: p2 = concat_path p2' (single_path u2 v2 e2) *)
            (* tail (concat p2' (single ...)) = tail (single ...) = v2 *)
            (* 使用 single_path_is_path 得到 is_path g (single u2 v2 e2) u2 v2 *)
            pose proof (single_path_is_path u2 v2 e2 Hstep2) as Hsp_path.
            (* tail (single_path u2 v2 e2) = v2 *)
            unfold is_path in Hsp_path.
            destruct Hsp_path as [Hsp_valid [Hsp_head Hsp_tail]].
            (* 使用 path_concat_valid 证明 tail p2 = v2 *)
            (* 首先构造 is_path g p2' (head p2') u2 *)
            assert (Hp2'_path: is_path g p2' (head p2') u2).
            {
              split; auto.
            }
            (* 由于 tail p2' = u2 且 head (single ...) = u2 *)
            (* 可以用 path_concat_valid *)
            assert (Hconcat_path: is_path g (concat_path p2' (single_path u2 v2 e2)) (head p2') v2).
            {
              apply (concat_path_is_path (head p2') u2 v2).
              - exact Hp2'_path.
              - split; auto.
            }
            (* 由 is_path 的定义，tail (concat_path p2' (single ...)) = v2 *)
            destruct Hconcat_path as [_ [_ Htail_concat]].
            (* Heq2: p2 = concat_path p2' (single_path u2 v2 e2) *)
            (* 所以 tail p2 = v2 *)
            assert (Htail_p2: tail p2 = v2).
            { rewrite Heq2. exact Htail_concat. }
            (* 现在需要证明 tail (concat_path p1 p2) = tail p2 *)
            (* 由 Hip: is_path g p u v 和 p = concat_path p1 p2 *)
            (* Htail_p: tail p = v *)
            (* 我们有 is_path g p1 u' (tail p1) 和 is_path g p2 (head p2) v *)
            (* 其中 tail p1 = head p2 *)
            (* 所以 is_path g (concat p1 p2) u' v，tail (concat p1 p2) = v *)
            (* 但我们需要验证 v = tail p2 = v2 *)
            (* Htail_p: tail (concat_path p1 p2) = v 直接给出 *)
            rewrite <- Hcat in Htail_p.
            (* 需要 tail (concat_path p1 p2) = tail p2 *)
            (* 使用 concat_path_is_path 的结论 *)
            assert (Hp1_path: is_path g p1 (head p1) (tail p1)).
            { split; auto. }
            assert (Hp2_path: is_path g p2 (head p2) (tail p2)).
            { split; auto. }
            (* p 有效，所以 tail p1 = head p2 *)
            (* 如何得到？由 path_valid g (concat_path p1 p2) 的定义... *)
            (* 实际上从 Hpv 我们知道 path_valid g p *)
            (* p = concat_path p1 p2 *)
            (* 但 path_valid (concat ...) 不直接给出 tail p1 = head p2 *)
            (* 它只是通过 concat_path_valid 构造的，前提包含这个等式 *)
            (* 让我们直接计算 *)
            (* tail (concat_path p1 p2) 由 tail_valid 给出 *)
            (* = tl_error (vertex_in_path (concat_path p1 p2)) *)
            (* = tl_error (vp1 ++ skipn 1 vp2) *)
            (* 当 p2 非空时，= tl_error vp2 = tail p2 *)
            (* 关键：p2 非空 (Hne2) *)
            (* 最简单的方法：直接使用 Htail_p 和 Htail_p2 *)
            (* 但我们还不知道 tail (concat p1 p2) = tail p2 *)
            (* 让我用一个辅助引理 *)
            (* 实际上，由于证明太复杂，让我换一个策略 *)
            (* v = tail p = tail (concat_path p1 p2) *)
            (* p2 非空，所以 destruct_n1 给出 p2 = concat p2' (single u2 v2 e2) *)
            (* 由 destruct_n1_spec，tail p2 = v2 可以通过相同的计算得到 *)
            (* 而 tail (concat p1 p2) 当 p2 非空时 = tail p2 *)
            (* 这是因为 vertex_in_path (concat p1 p2) = vp1 ++ skipn 1 vp2 *)
            (* tl_error 取最后一个元素，当 vp2 至少有 2 个元素时，结果是 vp2 的最后一个 = tail p2 *)
            (* 但 p2 非空不意味着 vp2 有多个元素... *)
            (* 让我直接证明 v = v2 *)
            apply Hnv.
            (* 需要证明 vvalid g v *)
            (* 由 step_vvalid2，v2 有效 *)
            (* 如果 v = v2，则完成 *)
            (* Htail_p: tail (concat_path p1 p2) = v *)
            (* 我们已经知道 tail p2 = v2 *)
            (* 关键：证明 v = v2 即 tail (concat_path p1 p2) = tail p2 *)
            (* 由于 p2 非空，tail (concat_path p1 p2) = tail p2 *)
            (* 这是 concat_path 的性质 *)
            (* 使用 is_path 的 Hpv 和路径非空来证明 *)
            rewrite <- Hcat in Hpv.
            assert (Htail_eq: tail (concat_path p1 p2) = v2).
            {
              (* p2 = concat_path p2' (single_path u2 v2 e2) *)
              (* tail p2 = v2 *)
              (* tail (concat p1 p2) = tail p2 当 p2 非空 *)
              pose proof (tail_valid g (concat_path p1 p2) Hpv) as Htv_concat.
              pose proof (tail_valid g p2 Hp2) as Htv_p2'.
              rewrite Htail_p2 in Htv_p2'.
              rewrite concat_path_vertex in Htv_concat.
              destruct (vertex_in_path p2) eqn:Hvp2.
              { pose proof (vpath_iff_epath g p2 Hp2) as [Hlen _].
                rewrite Hvp2 in Hlen. simpl in Hlen. lia. }
              destruct (vertex_in_path p1) eqn:Hvp1.
              { pose proof (vpath_iff_epath g p1 Hp1) as [Hlen _].
                rewrite Hvp1 in Hlen. simpl in Hlen. lia. }
              simpl in Htv_concat, Htv_p2'.
              unfold tl_error in Htv_concat, Htv_p2'.
              destruct l.
              - (* vertex_in_path p2 = [v0] *)
                simpl in Htv_p2'. injection Htv_p2' as Hv2_eq.
                rewrite app_nil_r in Htv_concat.
                (* Htv_concat: Some (tail ...) = nth_error (v1 :: l0) (length l0) *)
                (* 目标：tail (concat p1 p2) = v2 = v0 *)
                (* 但 tail p1 = k，head p2 = v0 (当 vp2 = [v0]) *)
                (* 由于 p = concat p1 p2 有效，tail p1 = head p2 *)
                (* 但我们从 Htail_p1: tail p1 = k 得到 k = head p2 = v0 *)
                (* 这种情况表示 k 是中间顶点且 p2 只有一个顶点 *)
                (* 即 p2 = [k]，head p2 = tail p2 = k *)
                (* 但 is_empty_path p2 应该为假（Hne2）*)
                (* 当 p2 只有一个顶点时，is_empty_path p2 为真 *)
                (* 与 Hne2 矛盾 *)
                exfalso. apply Hne2.
                (* 需要证明 is_empty_path p2 *)
                (* vertex_in_path p2 = [v0] 意味着 p2 只有一个顶点 *)
                (* 用 destruct_n1_path p2 应该给出 DestructBasen1 *)
                (* 但 Hd2 说 destruct_n1_path p2 = DestructStepn1 ... *)
                pose proof (destruct_n1_spec _ _ Hp2) as Hs2_again.
                rewrite Hd2 in Hs2_again.
                (* Hs2_again: path_valid g p2' /\ ... *)
                destruct Hs2_again as [_ [_ [_ Heq2']]].
                (* Heq2': p2 = concat_path p2' (single_path u2 v2 e2) *)
                (* 由 Hvp2: vertex_in_path p2 = [v0] *)
                (* 这意味着 p2 只有一个顶点，但 p2 = concat p2' (single ...) 意味着至少有边 *)
                (* 矛盾 *)
                (* single_path 有两个顶点 [u2, v2]，所以 concat 后至少两个顶点 *)
                pose proof (single_path_valid g u2 v2 e2 Hstep2) as Hsp_valid'.
                pose proof (vpath_iff_epath g (single_path u2 v2 e2) Hsp_valid') as [Hlen_sp _].
                rewrite single_path_vertex in Hlen_sp. simpl in Hlen_sp.
                (* Hlen_sp: 2 = S (length [e2]) = 2，所以 single_path 有 2 个顶点 *)
                (* concat_path p2' (single_path ...) 的顶点 = vp2' ++ skipn 1 [u2; v2] = vp2' ++ [v2] *)
                (* 所以至少有 1 + 1 = 2 个顶点，但 Hvp2 说只有 1 个 *)
                rewrite Heq2' in Hvp2.
                rewrite concat_path_vertex in Hvp2.
                rewrite single_path_vertex in Hvp2. simpl in Hvp2.
                destruct (vertex_in_path p2') as [|v3 l3] eqn:Hvp2'.
                + (* vertex_in_path p2' = nil，与 path_valid 矛盾 *)
                  pose proof (vpath_iff_epath g p2' Hp2') as [Hlen' _].
                  rewrite Hvp2' in Hlen'. simpl in Hlen'. lia.
                + (* vertex_in_path p2' = v3 :: l3，则 concat 至少有 2 个顶点 *)
                  simpl in Hvp2.
                  (* Hvp2: v3 :: l3 ++ v2 :: nil = v0 :: nil *)
                  (* 长度矛盾：length (v3 :: l3 ++ [v2]) >= 2，但 length [v0] = 1 *)
                  assert (Hlen_contra: length ((v3 :: l3) ++ v2 :: nil) = length (v0 :: nil)).
                  { f_equal. exact Hvp2. }
                  rewrite app_length in Hlen_contra. simpl in Hlen_contra. lia.
              - (* vertex_in_path p2 = v0 :: v3 :: l, 有多个顶点 *)
                (* 在 destruct l 后，l 被替换为 v3 :: l'，所以原来的形式变成 v0 :: v3 :: l' *)
                (* Coq 把新的尾部仍然叫 l，所以现在 vertex_in_path p2 = v0 :: v3 :: l *)
                (* 其中 v3 是原来 l 的头部 *)
                simpl in Htv_p2'.
                (* Htv_p2' 现在是: Some v2 = nth_error (v3 :: l) (length l) *)

                (* 从 Htv_p2' 得到 v2 是 (v3 :: l) 的最后元素 *)
                assert (Htv_p2'_eq: nth_error (v3 :: l) (length l) = Some v2).
                { symmetry. exact Htv_p2'. }

                (* Htv_concat 经过 simpl 后的形式 *)
                pose proof (tail_valid g (concat_path p1 p2) Hpv) as Htv_fresh.
                rewrite concat_path_vertex in Htv_fresh.
                rewrite Hvp1 in Htv_fresh. rewrite Hvp2 in Htv_fresh.
                simpl in Htv_fresh.
                unfold tl_error in Htv_fresh.

                (* 现在 Htv_fresh 应该有正确的形式 *)
                destruct (l0 ++ v3 :: l) eqn:Hl0vl.
                + (* l0 ++ v3 :: l = nil，矛盾 *)
                  destruct l0; simpl in Hl0vl; discriminate.
                + (* l0 ++ v3 :: l = v4 :: l1 *)
                  simpl in Htv_fresh.
                  (* Htv_fresh: Some (tail ...) = nth_error (v4 :: l1) (length l1) *)
                  (* 即 tail (concat p1 p2) = last (v4 :: l1) v4 *)

                  (* 由于 l0 ++ v3 :: l = v4 :: l1，最后元素是 (v3 :: l) 的最后元素 *)
                  assert (Hlast_same: nth_error (v4 :: l1) (length l1) = nth_error (v3 :: l) (length l)).
                  {
                    (* Hl0vl: l0 ++ v3 :: l = v4 :: l1 *)
                    (* 所以 length (v4 :: l1) = length (l0 ++ v3 :: l) = length l0 + S (length l) *)
                    assert (Hlen_eq: length (v4 :: l1) = length (l0 ++ v3 :: l)).
                    { f_equal. symmetry. exact Hl0vl. }
                    rewrite app_length in Hlen_eq. simpl in Hlen_eq.
                    (* Hlen_eq: S (length l1) = length l0 + S (length l) *)
                    (* 所以 length l1 = length l0 + length l *)
                    assert (Hl1_len: length l1 = length l0 + length l) by lia.
                    (* nth_error (v4 :: l1) (length l1) *)
                    (* = nth_error (l0 ++ v3 :: l) (length l0 + length l) *)
                    (* = nth_error (v3 :: l) (length l) *)
                    rewrite <- Hl0vl.
                    rewrite Hl1_len.
                    rewrite nth_error_app2 by lia.
                    f_equal. lia.
                  }
                  rewrite Hlast_same in Htv_fresh.
                  rewrite Htv_p2'_eq in Htv_fresh.
                  injection Htv_fresh as Htl_eq.
                  exact Htl_eq.
            }
            rewrite <- Htail_p.
            rewrite Htail_eq.
            apply (step_vvalid2 g e2 u2 v2 Hstep2).
        - (* done -> done ∪ [k] *)
          intros x Hx. left. apply Hinter. exact Hx.
      }
      assert (Hequiv: Sets.equiv
        (fun p => is_path_through_vset g p u v (done ∪ [k]))
        (fun p => is_path_through_vset g p u v done)).
      { intros p. apply Hpath_equiv. }
      rewrite Hequiv.
      apply H. exact Hnv.
  }

  (* 主循环证明 *)
  apply Hoare_forset with (Inv := fun processed_j s => Floyd_dist_inner_inv k done processed_j s).
  intros j processed_j Hj_valid Hj_not_in.
  unfold Floyd_j.

  (* 内层循环 - 使用更精细的不变量 *)
  eapply Hoare_conseq with
    (P2 := fun s => Floyd_dist_innermost_inv k j done processed_j ∅ s)
    (Q2 := fun _ s => Floyd_dist_innermost_inv k j done processed_j (vvalid g) s).
  {
    (* 前置条件转换：从 Floyd_dist_inner_inv 到 Floyd_dist_innermost_inv *)
    intros s Hinv.
    unfold Floyd_dist_innermost_inv.
    repeat split.
    - (* 对于 v ∈ processed_j，所有 u 满足新不变量 *)
      intros u v Hv_in. apply (proj1 (Hinv u v)). exact Hv_in.
    - (* 对于当前的 j，已处理的 i 满足新不变量 - 空集，无需证明 *)
      intros u Hu_in. sets_unfold in Hu_in. contradiction.
    - (* 对于当前的 j，未处理的 i 满足旧不变量 *)
      intros u _. apply (proj2 (Hinv u j)). exact Hj_not_in.
    - (* 对于 v ∉ processed_j ∪ [j]，所有 u 满足旧不变量 *)
      intros u v Hv_not_in. apply (proj2 (Hinv u v)).
      intros Hv_in. apply Hv_not_in. left. exact Hv_in.
  }
  {
    (* 后置条件转换：从 Floyd_dist_innermost_inv 到 Floyd_dist_inner_inv (processed_j ∪ [j]) *)
    intros _ s [Hpj [Hpi_done [Hpi_old Hother]]].
    unfold Floyd_dist_inner_inv.
    intros u v. split.
    - (* v ∈ processed_j ∪ [j] -> 新不变量 *)
      intros Hv_in.
      destruct Hv_in as [Hv_old|Hv_j].
      + (* v ∈ processed_j *)
        apply Hpj. exact Hv_old.
      + (* v = j *)
        unfold Sets.singleton, SetsEle.In in Hv_j. subst v.
        destruct (classic (vvalid g u)) as [Hu_valid|Hu_invalid].
        * apply Hpi_done. exact Hu_valid.
        * (* u 无效的情况 - 使用 Hpi_old 并证明路径集合等价 *)
          (* 由于 u 无效，不存在从 u 出发的路径，所以 done 和 done ∪ [k] 的路径集合相同 *)
          assert (Hequiv': Sets.equiv
            (fun p => is_path_through_vset g p u j (done ∪ [k]))
            (fun p => is_path_through_vset g p u j done)).
          {
            intros p. split; intros [Hip Hinter].
            - split; auto.
              intros x Hx. specialize (Hinter x Hx).
              destruct Hinter as [Hdone'|Hk_eq]; auto.
              unfold Sets.singleton, SetsEle.In in Hk_eq. subst x.
              (* x = k 是中间顶点，但起点 u 无效 *)
              (* 如果有中间顶点，路径必须非空，意味着 head p 有效 *)
              (* 但 head p = u（由 Hip），而 u 无效，矛盾 *)
              exfalso.
              destruct Hip as [Hpv [Hhead _]].
              destruct Hx as [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat _]]]]]]].
              (* p = concat_path p1 p2，且 p1 非空 *)
              (* 使用 destruct_1n_path 分解 p *)
              destruct (destruct_1n_path p) as [v_base | p' u' v' e'] eqn:Hdp.
              + (* 空路径 - 与 p1 非空矛盾 *)
                pose proof (destruct_1n_spec _ _ Hpv) as Hspec.
                rewrite Hdp in Hspec.
                (* p = empty_path v_base *)
                (* 但 p = concat_path p1 p2 且 p1 非空 *)
                (* empty_path 没有边，但非空路径 p1 有边 *)
                destruct (destruct_1n_path p1) as [v1_base | p1' u1' v1' e1'] eqn:Hdp1.
                * apply Hne1. exists v1_base.
                  pose proof (destruct_1n_spec _ _ Hp1) as Hspec1.
                  rewrite Hdp1 in Hspec1. exact Hspec1.
                * pose proof (destruct_1n_spec _ _ Hp1) as Hspec1.
                  rewrite Hdp1 in Hspec1.
                  destruct Hspec1 as [_ [_ [Hstep1 Heq1]]].
                  (* p1 = concat_path (single_path u1' v1' e1') p1' *)
                  (* edge_in_path p1 包含 e1' *)
                  pose proof (empty_path_edge g v_base) as Hemp_e.
                  rewrite <- Hspec in Hemp_e.
                  rewrite <- Hcat in Hemp_e.
                  rewrite concat_path_edge in Hemp_e.
                  rewrite Heq1 in Hemp_e.
                  rewrite concat_path_edge in Hemp_e.
                  rewrite single_path_edge in Hemp_e.
                  discriminate.
              + (* 非空路径 *)
                pose proof (destruct_1n_spec _ _ Hpv) as Hspec.
                rewrite Hdp in Hspec.
                destruct Hspec as [Hp' [Hhead' [Hstep' Heq']]].
                apply Hu_invalid.
                (* Heq' : concat_path p1 p2 = concat_path (single_path u' v' e') p' *)
                (* Hhead : head (concat_path p1 p2) = u *)
                (* 使用 head_valid 将 head 转换为 hd_error (vertex_in_path) *)
                pose proof (single_path_valid g u' v' e' Hstep') as Hsp.
                pose proof (tail_valid g (single_path u' v' e') Hsp) as Hsp_tail.
                rewrite single_path_vertex in Hsp_tail. simpl in Hsp_tail.
                unfold tl_error in Hsp_tail. simpl in Hsp_tail.
                injection Hsp_tail as Hsp_tail_eq.
                assert (Hconnect: tail (single_path u' v' e') = head p').
                { rewrite Hsp_tail_eq. symmetry. exact Hhead'. }
                pose proof (concat_path_valid g _ _ Hsp Hp' Hconnect) as Hcp_valid.
                pose proof (head_valid g (concat_path (single_path u' v' e') p') Hcp_valid) as Hcp_head.
                rewrite concat_path_vertex in Hcp_head.
                rewrite single_path_vertex in Hcp_head. simpl in Hcp_head.
                (* Hcp_head : Some (head (concat_path (single_path u' v' e') p')) = Some u' *)
                (* 使用 Heq' 将 Hhead 中的 concat_path p1 p2 替换为 concat_path (single_path ...) p' *)
                rewrite Heq' in Hhead.
                assert (Hu_eq: u = u').
                {
                  assert (Some u = Some u').
                  { rewrite <- Hhead. rewrite <- Hcp_head. reflexivity. }
                  injection H. auto.
                }
                rewrite Hu_eq.
                apply (step_vvalid1 g e' u' v' Hstep').
            - split; auto.
              intros x Hx. left. apply Hinter. exact Hx.
          }
          unfold min_weight_distance_in_vset.
          rewrite Hequiv'.
          unfold min_weight_distance_in_vset in Hpi_old.
          apply Hpi_old. exact Hu_invalid.
    - (* v ∉ processed_j ∪ [j] -> 旧不变量 *)
      intros Hv_not_in.
      apply Hother. exact Hv_not_in.
  }

  (* 内层循环主体 *)
  apply Hoare_forset with (Inv := fun processed_i s =>
    Floyd_dist_innermost_inv k j done processed_j processed_i s).

  intros i processed_i Hi_valid Hi_not_in.
  unfold update_dist.

  (* 单步更新的证明 *)
  unfold Hoare. intros s res s' Hinv Hexec.
  simpl in Hexec. inversion Hexec; subst. clear Hexec.

  destruct Hinv as [Hpj [Hpi_done [Hpi_old Hother]]].

  remember (s.(dist) (i, k)) as d_ik.
  remember (s.(dist) (k, j)) as d_kj.
  remember (s.(dist) (i, j)) as d_ij.

  (* 获取旧的距离不变量 *)
  assert (Hdist_ij_old: min_weight_distance_in_vset g i j done d_ij).
  { rewrite Heqd_ij. apply Hpi_old. exact Hi_not_in. }

  assert (Hdist_ik: min_weight_distance_in_vset g i k done d_ik).
  { rewrite Heqd_ik.
    destruct (classic (k ∈ processed_j)) as [Hkj|Hnkj].
    - apply (proj1 (min_dist_stable_k i k done (dist s (i, k)) Hk_valid Hk_not_in)).
      apply Hpj. exact Hkj.
    - destruct (v_eq_dec k j) as [Hk_eq_j|Hk_neq_j].
      + (* k = j *)
        rewrite Hk_eq_j. apply Hpi_old. exact Hi_not_in.
      + (* k ≠ j *)
        apply Hother.
        intros [Hk_in_pj|Hk_eq_j'].
        * apply Hnkj. exact Hk_in_pj.
        * unfold Sets.singleton, SetsEle.In in Hk_eq_j'.
          exfalso. apply Hk_neq_j. unfold equiv. symmetry. exact Hk_eq_j'. }

  assert (Hdist_kj: min_weight_distance_in_vset g k j done d_kj).
  { rewrite Heqd_kj.
    destruct (classic (k ∈ processed_i)) as [Hki|Hnki].
    - apply (proj1 (min_dist_stable_k_rev k j done (dist s (k, j)) Hk_valid Hk_not_in)).
      apply Hpi_done. exact Hki.
    - apply Hpi_old. exact Hnki. }

  pose proof (min_dist_recur i j k done Hk_valid Hk_not_in d_ij d_ik d_kj
    Hdist_ij_old Hdist_ik Hdist_kj) as Hrecur.

  destruct (Z_op_lt_dec (Z_op_plus d_ik d_kj) d_ij) as [Hlt|Hnlt].
  - (* 更新发生 *)
    simpl.
    unfold Floyd_dist_innermost_inv.
    repeat split.
    + (* 对于 v ∈ processed_j，所有 u 满足新不变量 *)
      intros u v Hv_in.
      unfold t_set. simpl.
      destruct (equiv_dec (i, j) (u, v)) as [Heq|Hneq].
      * (* (i, j) = (u, v)，但 v ∈ processed_j，而 j ∉ processed_j，矛盾 *)
        exfalso.
        unfold equiv in Heq.
        assert (v = j) by congruence.
        subst v. apply Hj_not_in. exact Hv_in.
      * apply Hpj. exact Hv_in.
    + (* 对于当前的 j，已处理的 i（包括当前 i）满足新不变量 *)
      intros u Hu_in.
      unfold t_set. simpl.
      destruct (equiv_dec (i, j) (u, j)) as [Heq|Hneq].
      * (* u = i *)
        unfold equiv in Heq.
        assert (u = i) by congruence. subst u.
        destruct d_ij as [zij|], d_ik as [zik|], d_kj as [zkj|]; simpl in *; try contradiction.
        -- (* Some zij, Some zik, Some zkj *)
           unfold Z_op_min in Hrecur. simpl in Hrecur.
           replace (Z.min zij (zik + zkj)) with (zik + zkj)%Z in Hrecur.
           ++ exact Hrecur.
           ++ symmetry. apply Z.min_r. lia.
        -- (* None, Some zik, Some zkj *)
           unfold Z_op_min in Hrecur. simpl in Hrecur.
           exact Hrecur.
      * (* u ≠ i，但 u ∈ processed_i ∪ [i] *)
        destruct Hu_in as [Hu_old|Hu_eq_i].
        -- (* u ∈ processed_i *)
           apply Hpi_done. exact Hu_old.
        -- (* u = i，但我们已经排除了这种情况 *)
           unfold Sets.singleton, SetsEle.In in Hu_eq_i.
           exfalso. apply Hneq.
           unfold equiv. rewrite Hu_eq_i. reflexivity.
    + (* 对于当前的 j，未处理的 i 满足旧不变量 *)
      intros u Hu_not_in.
      unfold t_set. simpl.
      destruct (equiv_dec (i, j) (u, j)) as [Heq|Hneq].
      * (* u = i，但 u ∉ processed_i ∪ [i]，矛盾 *)
        exfalso.
        unfold equiv in Heq.
        assert (u = i) by congruence. subst u.
        apply Hu_not_in.
        unfold Sets.union, Sets.singleton, SetsEle.In.
        right. reflexivity.
      * (* u ≠ i *)
        apply Hpi_old.
        intros Hu_in. apply Hu_not_in. left. exact Hu_in.
    + (* 对于 v ∉ processed_j ∪ [j]，所有 u 满足旧不变量 *)
      intros u v Hv_not_in.
      unfold t_set. simpl.
      destruct (equiv_dec (i, j) (u, v)) as [Heq|Hneq].
      * (* (i, j) = (u, v)，但 v ∉ processed_j ∪ [j]，而 j ∈ [j]，矛盾 *)
        exfalso.
        unfold equiv in Heq.
        assert (v = j) by congruence. subst v.
        apply Hv_not_in.
        unfold Sets.union, Sets.singleton, SetsEle.In.
        right. reflexivity.
      * apply Hother. exact Hv_not_in.
  - (* 不更新 *)
    simpl.
    unfold Floyd_dist_innermost_inv.
    repeat split.
    + (* 对于 v ∈ processed_j，所有 u 满足新不变量 *)
      intros u v Hv_in. apply Hpj. exact Hv_in.
    + (* 对于当前的 j，已处理的 i（包括当前 i）满足新不变量 *)
      intros u Hu_in.
      destruct Hu_in as [Hu_old|Hu_eq_i].
      * (* u ∈ processed_i *)
        apply Hpi_done. exact Hu_old.
      * (* u = i *)
        unfold Sets.singleton, SetsEle.In in Hu_eq_i. subst u.
        rewrite <- Heqd_ij.
        destruct d_ij as [zij|], d_ik as [zik|], d_kj as [zkj|]; simpl in *.
        all: try (unfold Z_op_min in Hrecur; simpl in Hrecur;
                  try replace (Z.min zij (zik + zkj)) with zij in Hrecur by (symmetry; apply Z.min_l; lia);
                  exact Hrecur).
        exfalso. apply Hnlt. exact I.
    + (* 对于当前的 j，未处理的 i 满足旧不变量 *)
      intros u Hu_not_in.
      apply Hpi_old.
      intros Hu_in. apply Hu_not_in. left. exact Hu_in.
    + (* 对于 v ∉ processed_j ∪ [j]，所有 u 满足旧不变量 *)
      intros u v Hv_not_in. apply Hother. exact Hv_not_in.
Qed.

(** === 主定理：距离正确性 ===

    证明 Floyd 算法计算的距离是正确的
*)

(** 辅助引理：路径中间顶点都是有效顶点 *)
Lemma path_through_vvalid_equiv: forall u v,
  Sets.equiv
    (fun p => is_path_through_vset g p u v (vvalid g))
    (fun p => is_path g p u v).
Proof.
  intros u v p. split.
  - intros [Hpath _]. exact Hpath.
  - intros Hpath. split; auto.
    intros x [p1 [p2 [Hp1 [Hp2 [Hne1 [Hne2 [Hcat Htail]]]]]]].
    destruct Hpath as [Hpv [Hhead Htail']].
    rewrite <- Hcat in Hpv.
    (* 需要证明 tail p1 = x 是有效顶点 *)
    (* 由于 p1 是非空路径（Hne1: ~ is_empty_path p1），使用 destruct_n1_spec *)
    (* 从路径分解得到最后一条边，然后用 step_vvalid2 *)
    destruct (destruct_n1_path p1) as [p_base v_base | p1' u_step v_step e_step] eqn:Hdestruct.
    + (* p1 是空路径，与 Hne1 矛盾 *)
      exfalso. apply Hne1.
      exists v_base.
      pose proof (destruct_n1_spec _ _ Hp1) as Hspec.
      rewrite Hdestruct in Hspec.
      exact Hspec.
    + (* p1 = concat_path p1' (single_path u_step v_step e_step) *)
      pose proof (destruct_n1_spec _ _ Hp1) as Hspec.
      rewrite Hdestruct in Hspec.
      destruct Hspec as [Hp1' [Htail1' [Hstep Heq_p1]]].
      (* tail p1 = v_step，由 step_vvalid2 知 v_step 是有效顶点 *)
      assert (Htail_p1: tail p1 = v_step).
      {
        rewrite Heq_p1.
        (* 首先证明 head (single_path u_step v_step e_step) = u_step *)
        assert (Hhead_single: head (single_path u_step v_step e_step) = u_step).
        {
          pose proof (head_valid g (single_path u_step v_step e_step)
                       (single_path_valid _ _ _ _ Hstep)) as Hhs.
          rewrite single_path_vertex in Hhs. simpl in Hhs.
          injection Hhs as Hhs'. exact Hhs'.
        }
        assert (Hconnect: tail p1' = head (single_path u_step v_step e_step)).
        { rewrite Htail1'. rewrite Hhead_single. reflexivity. }
        pose proof (concat_path_valid _ _ _ Hp1' (single_path_valid _ _ _ _ Hstep) Hconnect) as Hcp.
        (* tail (single_path ...) = v_step *)
        assert (Htail_single: tail (single_path u_step v_step e_step) = v_step).
        {
          pose proof (tail_valid g (single_path u_step v_step e_step)
                       (single_path_valid _ _ _ _ Hstep)) as Htv_single.
          rewrite single_path_vertex in Htv_single. simpl in Htv_single.
          unfold tl_error in Htv_single. simpl in Htv_single.
          injection Htv_single as Hv. exact Hv.
        }
        (* 使用 tail_concat 的直接计算 *)
        pose proof (tail_valid g (concat_path p1' (single_path u_step v_step e_step)) Hcp) as Htv.
        rewrite concat_path_vertex in Htv.
        rewrite single_path_vertex in Htv.
        (* vertex_in_path p1' 非空因为 p1' 是有效路径 *)
        pose proof (vpath_iff_epath g p1' Hp1') as [Hlen _].
        destruct (vertex_in_path p1') as [|h t] eqn:Hvp1'.
        - simpl in Hlen. lia.
        - (* 列表形式：h::t ++ skipn 1 [u_step; v_step] = h::t ++ [v_step] *)
          simpl in Htv. unfold tl_error in Htv.
          (* 需要计算 tl_error 的结果 *)
          (* tl_error (h :: t ++ [v_step]) 应该返回 v_step *)
          destruct (t ++ v_step :: nil) eqn:Ht_concat.
          + destruct t; simpl in Ht_concat; discriminate.
          + simpl in Htv.
            (* Htv : Some (tail (concat_path p1' (single_path u_step v_step e_step))) =
                     match nth_error (v0 :: l) (length l) with ... *)
            (* 需要证明 nth_error (v0 :: l) (length l) = Some v_step *)
            (* 因为 v0 :: l = t ++ [v_step]，所以最后一个元素是 v_step *)
            assert (Hlast_elem: nth_error (v0 :: l) (length l) = Some v_step).
            {
              assert (Hlist_eq: v0 :: l = t ++ v_step :: nil).
              { symmetry. exact Ht_concat. }
              (* 首先证明 length l = length t *)
              assert (Hlen_eq: length l = length t).
              {
                assert (H: length (v0 :: l) = length (t ++ v_step :: nil)).
                { f_equal. exact Hlist_eq. }
                simpl in H. rewrite app_length in H. simpl in H. lia.
              }
              rewrite Hlist_eq. rewrite Hlen_eq.
              rewrite nth_error_app2; [|lia].
              replace (length t - length t) with 0 by lia.
              simpl. reflexivity.
            }
            rewrite Hlast_elem in Htv.
            injection Htv as Htail_eq. exact Htail_eq.
      }
      rewrite Htail in Htail_p1. rewrite Htail_p1.
      apply (step_vvalid2 g e_step u_step v_step). exact Hstep.
Qed.

Theorem Floyd_dist_correct:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => distance_soundness s /\ distance_completeness s).
Proof.
  unfold initialized_dist_state, Floyd.
  eapply Hoare_conseq_post.
  2: {
    apply Hoare_forset with (Inv := Floyd_dist_invariant).
    intros k done Hk_valid Hk_not_in_done.
    apply Floyd_k_dist_correct; auto.
  }
  intros r s Hinv.
  unfold Floyd_dist_invariant in Hinv.

  split.
  (* 1. distance_soundness *)
  {
    intros u v d Hd.
    unfold min_weight_distance.
    specialize (Hinv u v).
    unfold min_weight_distance_in_vset in Hinv.
    (* 使用 min_default_eq_forward 转换路径集合 *)
    eapply (min_default_eq_forward Z_op_le).
    - rewrite Hd in Hinv. exact Hinv.
    - intros p Hp. exists p. split.
      + apply (proj1 (path_through_vvalid_equiv u v p)). exact Hp.
      + apply Z_op_le_refl.
    - intros p Hp. exists p. split.
      + apply (proj2 (path_through_vvalid_equiv u v p)). exact Hp.
      + apply Z_op_le_refl.
  }

  (* 2. distance_completeness *)
  {
    intros u v d Hd.
    specialize (Hinv u v).
    unfold min_weight_distance in Hd.
    unfold min_weight_distance_in_vset in Hinv.
    (* 使用 min_default_unique 和 min_default_eq_forward *)
    assert (Hd': min_value_of_subset_with_default Z_op_le
                   (fun p => is_path_through_vset g p u v (vvalid g))
                   (path_weight g) None (Some d)).
    {
      eapply (min_default_eq_forward Z_op_le).
      + exact Hd.
      + intros p Hp. exists p. split.
        * apply (proj2 (path_through_vvalid_equiv u v p)). exact Hp.
        * apply Z_op_le_refl.
      + intros p Hp. exists p. split.
        * apply (proj1 (path_through_vvalid_equiv u v p)). exact Hp.
        * apply Z_op_le_refl.
    }
    pose proof (min_default_unique Z_op_le (path_weight g)
      (fun p => is_path_through_vset g p u v (vvalid g)) None _ _ Hd' Hinv) as Heq.
    inversion Heq. reflexivity.
  }
Qed.

(** === 第三档难度：边的最优性 ===

    如果 e 是 v 到 u 的边，且 d(src,u) = d(src,v) + weight(e)，
    则存在 src 到 u 的最短路径，最后一条边是 e
*)

Theorem edge_optimality_theorem:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => edge_optimality s).
Proof.
  eapply Hoare_conseq_post.
  2: { apply Floyd_dist_correct. }
  intros _ s [Hsound Hcomp].
  unfold edge_optimality.
  intros src u v e d_su d_sv w_e Hdsu Hdsv Hstep Hwe Heq.

  (* 由 d_sv 是最短距离，存在 src 到 v 的最短路径 p_sv *)
  assert (Hmin_sv: min_weight_distance g src v (Some d_sv)).
  { apply Hsound. exact Hdsv. }

  unfold min_weight_distance in Hmin_sv.
  destruct Hmin_sv as [[Hmin_obj Hle]|[Hall Heq_def]].
  + (* 存在最短路径 *)
    destruct Hmin_obj as [p_sv [[Hp_sv Hp_sv_min] Hw_sv]].
    exists (concat_path p_sv (single_path v u e)).
    split.
    * (* 路径有效性 - 使用 concat_path_is_path *)
      apply (concat_path_is_path src v u).
      -- exact Hp_sv.
      -- apply single_path_is_path. exact Hstep.
    * split.
      -- (* 权重正确 *)
         rewrite concat_path_weight.
         rewrite Hw_sv.
         unfold path_weight. rewrite single_path_edge. simpl.
         rewrite Hwe. simpl. f_equal. lia.
      -- (* 路径以 e 结尾 *)
         exists p_sv. reflexivity.
  + (* 无路径情况 - 矛盾，因为 d_sv 有值 *)
    exfalso.
    discriminate Heq_def.
Qed.

(** === 第四档难度：路径重建正确性 ===

    如果 dist[u][v] = Some d，则存在权重为 d 的 u 到 v 路径
*)
Theorem path_reconstruction_theorem:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => path_reconstruction_correct s).
Proof.
  eapply Hoare_conseq_post.
  2: { apply Floyd_dist_correct. }
  intros _ s [Hsound Hcomp].
  unfold path_reconstruction_correct.
  intros u v d Hd.
  (* 由健全性，d 是最短距离 *)
  assert (Hmin: min_weight_distance g u v (Some d)).
  { apply Hsound. exact Hd. }
  (* 由最短距离定义，存在这样的路径 *)
  unfold min_weight_distance in Hmin.
  destruct Hmin as [[Hmin_obj Hle]|[Hall Heq_def]].
  + destruct Hmin_obj as [p [[Hp _] Hw]].
    exists p. auto.
  + exfalso. discriminate Heq_def.
Qed.

(** === 完整正确性定理 === *)
Theorem Floyd_correct:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => distance_correct s).
Proof.
  unfold distance_correct.
  eapply Hoare_conseq_post.
  2: { apply Floyd_dist_correct. }
  intros _ s [Hsound Hcomp].
  repeat split.
  + exact Hsound.
  + exact Hcomp.
  + (* edge_optimality *)
    unfold edge_optimality.
    intros src u v e d_su d_sv w_e Hdsu Hdsv Hstep Hwe Heq.
    assert (Hmin_sv: min_weight_distance g src v (Some d_sv)).
    { apply Hsound. exact Hdsv. }
    unfold min_weight_distance in Hmin_sv.
    destruct Hmin_sv as [[Hmin_obj Hle]|[Hall Heq_def]].
    * destruct Hmin_obj as [p_sv [[Hp_sv Hp_sv_min] Hw_sv]].
      exists (concat_path p_sv (single_path v u e)).
      split.
      -- (* 路径有效性 - 使用 concat_path_is_path *)
         apply (concat_path_is_path src v u).
         ++ exact Hp_sv.
         ++ apply single_path_is_path. exact Hstep.
      -- split.
         ++ unfold is_path in Hp_sv.
            destruct Hp_sv as [Hpv_sv [Hhead_sv Htail_sv]].
            rewrite concat_path_weight.
            rewrite Hw_sv.
            unfold path_weight. rewrite single_path_edge. simpl.
            rewrite Hwe. simpl. f_equal. lia.
         ++ exists p_sv. reflexivity.
    * exfalso. discriminate Heq_def.
  + (* path_reconstruction_correct *)
    unfold path_reconstruction_correct.
    intros u v d Hd.
    assert (Hmin: min_weight_distance g u v (Some d)).
    { apply Hsound. exact Hd. }
    unfold min_weight_distance in Hmin.
    destruct Hmin as [[Hmin_obj Hle]|[Hall Heq_def]].
    * destruct Hmin_obj as [p [[Hp _] Hw]].
      exists p. auto.
    * exfalso. discriminate Heq_def.
Qed.

End Floyd.
