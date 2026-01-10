Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

(** 
  Dijkstra 算法证明所需的辅助引理库
  
  本文件提供 Dijkstra 算法正确性证明所需的所有引理，
  使用抽象的类型类定义，与 eweight.v 保持一致。
*)

Section dijkstra.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).


(** ===== 初始化相关引理 ===== *)

(** 
  初始状态的最短距离性质
  
  对于源点 src：
  - dist[src] = g_zero，且这是真正的最短距离（空路径）
  
  对于其他顶点 v ≠ src：
  - dist[v] = W_inf，表示通过空集不可达
*)
Lemma init_dist_from_source: forall (src: V),
  min_weight_distance g src src (Some 0).
Admitted.

Lemma init_dist_to_others: forall (src v: V),
  v <> src ->
  min_weight_distance_in_vset g src v ∅ None.
Admitted.


(** ===== 路径分解引理 ===== *)

(**
  最短路径的前缀也是最短路径
  
  如果 p 是从 u 到 v 的最短路径，且 p 经过顶点 w，
  那么从 u 到 w 的那段也是最短路径。
  
  证明：反证法，如果存在更短的从 u 到 w 的路径，
  替换后可以得到更短的从 u 到 v 的路径，矛盾。
*)
Lemma shortest_path_prefix_shortest: 
  forall (u v w: V) (p p_prefix: P),
    min_weight_path g u v p ->
    (* p_prefix 是 p 的前缀，终点是 w *)
    is_path g p_prefix u w ->
    In w (vertex_in_path p) ->
    (* 则 p_prefix 是最短路径 *)
    min_weight_path g u w p_prefix.
Admitted.

(**
  带顶点集合约束的路径前缀性质
  
  类似上面的引理，但考虑中间节点的约束。
*)
Lemma shortest_path_in_vset_prefix: 
  forall (u v w: V) (p p_prefix: P) (vset: V -> Prop),
    min_weight_path_in_vset g u v vset p ->
    is_path_through_vset g p_prefix u w vset ->
    In w (vertex_in_path p) ->
    min_weight_path_in_vset g u w vset p_prefix.
Admitted.


(** ===== 松弛操作相关引理 ===== *)

(**
  Dijkstra 松弛操作的正确性
  
  假设：
  - dist[u] 已经是从 src 到 u 的最短距离
  - dist[v] 是从 src 到 v、仅通过 visited 的最短距离
  - 存在边 e: u -> v，权重为 w_e
  
  则：松弛后 dist[v] = min(dist[v], dist[u] + w_e) 是
      从 src 到 v、仅通过 visited ∪ {u} 的最短距离
  
  证明思路：
  1. 下界：任何通过 visited ∪ {u} 的路径权重 ≥ min(dist[v], dist[u] + w_e)
     - 不经过 u：权重 ≥ dist[v]
     - 经过 u：最短的是 src ~> u -> v，权重 ≥ dist[u] + w_e
  2. 可达：存在路径达到这个下界
*)
Lemma dijkstra_relax_correct:
  forall (src u v: V) (visited: V -> Prop) (e: E) 
         (dist_u dist_v w_e: option Z),
    (* 前提条件 *)
    u ∈ visited ->  (* u 已经被访问 *)
    step_aux g e u v ->  (* 存在边 u -> v *)
    weight g e = w_e ->
    (* dist[u] 是最终的最短距离 *)
    min_weight_distance g src u dist_u ->
    (* dist[v] 是通过 visited 的最短距离 *)
    min_weight_distance_in_vset g src v visited dist_v ->
    (* 结论：松弛后是通过 visited ∪ {u} 的最短距离 *)
    min_weight_distance_in_vset g src v (visited ∪ [u]) 
      (Z_op_min dist_v (Z_op_plus dist_u w_e)).
Admitted.


(** ===== 贪心选择的正确性引理 ===== *)

(**
  贪心选择引理（Dijkstra 算法的核心）
  
  假设：
  - 所有已访问顶点的 dist 值都是最终的最短距离
  - 所有未访问顶点的 dist 值是仅通过已访问顶点的最短距离
  - 选择 dist 值最小的未访问顶点 u
  
  则：dist[u] 已经是从 src 到 u 的真正最短距离
  
  证明（反证法）：
  假设存在更短的路径 P: src ~> u，权重 < dist[u]。
  
  考虑 P 上第一个离开 visited 集合的顶点 v：
  - v 的前驱 w 在 visited 中
  - 根据循环不变量，dist[w] = 真正的最短距离到 w
  - 经过 w 到达 v 的路径权重 ≥ dist[w] + weight(w, v)
  - 根据循环不变量，dist[v] ≤ dist[w] + weight(w, v)
    （因为 dist[v] 是通过 visited 的最短距离，包括经过 w 的路径）
  
  所以：dist[v] ≤ weight(P 的前缀到 v) < weight(P) < dist[u]
  
  但这与"选择了 u"矛盾，因为我们应该选择 dist 值最小的顶点 v。
  
  关键：这个证明依赖于边权重非负！
*)
Lemma greedy_choice_correct:
  forall (src u: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 前提：循环不变量成立 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* u 是未访问顶点中 dist 值最小的 *)
    ~ u ∈ visited ->
    dist u <> None ->
    (forall v, ~ v ∈ visited -> dist v <> None -> Z_op_le (dist u) (dist v)) ->
    (* 结论：dist[u] 是最终的最短距离 *)
    min_weight_distance g src u (dist u).
Proof.
  intros src u visited dist H_visited_correct H_unvisited_optimal 
         H_u_unvisited H_u_finite H_u_minimal.
  (* 
    证明提示：
    1. 使用反证法：假设存在更短的路径 P
    2. 分析 P 上第一个离开 visited 的顶点
    3. 使用非负权重性质
    4. 推导矛盾
    
    需要的辅助引理：
    - 路径分解：可以在任意顶点分解路径
    - 权重单调性：部分路径权重 ≤ 完整路径权重（非负权重）
    - 最短距离的下界性质
  *)
Admitted.


(** ===== 非负权重的性质引理 ===== *)

(**
  路径延长不会减少权重（非负权重的关键性质）
  
  如果 p1 是 p2 的前缀，则 weight(p1) ≤ weight(p2)
*)
Lemma path_extension_weight_monotone:
  forall (u v w: V) (p_short p_long: P),
    is_path g p_short u v ->
    is_path g p_long u w ->
    In v (vertex_in_path p_long) ->
    (* p_short 相当于 p_long 的前缀 *)
    Z_op_le (path_weight g p_short) (path_weight g p_long).
Admitted.


(** ===== 最短距离的基本性质引理 ===== *)

(**
  三角不等式
  
  从 u 到 w 的最短距离 ≤ 从 u 到 v 的最短距离 + 从 v 到 w 的最短距离
*)
Lemma triangle_inequality:
  forall (u v w: V) (d_uw d_uv d_vw: option Z),
    min_weight_distance g u w d_uw ->
    min_weight_distance g u v d_uv ->
    min_weight_distance g v w d_vw ->
    Z_op_le d_uw (Z_op_plus d_uv d_vw).
Admitted.

(**
  带边的三角不等式
  
  如果存在边 e: u -> v，则 dist[v] ≤ dist[u] + weight(e)
*)
Lemma triangle_inequality_with_edge:
  forall (src u v: V) (e: E) (d_u d_v: option Z),
    step_aux g e u v ->
    min_weight_distance g src u d_u ->
    min_weight_distance g src v d_v ->
    Z_op_le d_v (Z_op_plus d_u (weight g e)).
Admitted.


(** ===== 可达性和有限性的关系 ===== *)

(**
  如果 dist[v] 不是无穷大，则 v 从 src 可达
*)
Lemma finite_dist_implies_reachable:
  forall (src v: V) (vset: V -> Prop) (d: option Z),
    min_weight_distance_in_vset g src v vset d ->
    d <> None ->
    exists p, is_path_through_vset g p src v vset.
Admitted.

(**
  如果 v 从 src 不可达（通过 vset），则 dist[v] = W_inf
*)
Lemma unreachable_implies_inf:
  forall (src v: V) (vset: V -> Prop),
    (forall p, ~ is_path_through_vset g p src v vset) ->
    min_weight_distance_in_vset g src v vset None.
Admitted.


(** ===== 终止性相关引理 ===== *)

(**
  终止条件下的正确性
  
  当算法终止时（所有可达顶点都已访问），
  循环不变量蕴含完整的正确性。
*)
Lemma termination_implies_soundness:
  forall (src: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 循环不变量 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* 终止条件：所有有限距离的顶点都已访问 *)
    (forall v, dist v <> None -> v ∈ visited) ->
    (* 结论：健全性成立 *)
    forall v w, dist v = w -> min_weight_distance g src v w.
Admitted.

Lemma termination_implies_completeness:
  forall (src: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 循环不变量 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* 终止条件 *)
    (forall v, dist v <> None -> v ∈ visited) ->
    (* 结论：完备性成立 *)
    forall v w, min_weight_distance g src v w -> dist v = w.
Admitted.


(** ===== 辅助引理：集合和路径的关系 ===== *)

(**
  路径集合的单调性
*)
Lemma path_set_monotone:
  forall (u v: V) (vset1 vset2: V -> Prop) (p: P),
    is_path_through_vset g p u v vset1 ->
    vset1 ⊆ vset2 ->
    is_path_through_vset g p u v vset2.
Admitted.

(**
  最短距离的单调性
*)
Lemma min_distance_vset_monotone:
  forall (u v: V) (vset1 vset2: V -> Prop) (d1 d2: option Z),
    min_weight_distance_in_vset g u v vset1 d1 ->
    min_weight_distance_in_vset g u v vset2 d2 ->
    vset1 ⊆ vset2 ->
    Z_op_le d2 d1.
Admitted.

End dijkstra.

