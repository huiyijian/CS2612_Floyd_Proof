Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Dijkstra.

(** Dijkstra算法用于计算单源最短路径。
    核心思想是贪心地选择当前距离最小的未访问顶点，然后松弛其邻居。
    
    算法流程：
    1. 初始化：源点距离为0，其他顶点距离为无穷大（W_inf）
    2. 循环：选择距离最小的未访问顶点u，标记为已访问
    3. 对u的每个邻居v，尝试通过u松弛：dist[v] = min(dist[v], dist[u] + weight(u,v))
    4. 重复直到所有可达顶点都被访问
    
    循环不变量核心思想：
    - 已访问顶点的dist值是最终的最短距离
    - 未访问顶点的dist值是"只能通过已访问顶点作为中间节点"的最短距离
    - 每次选择的顶点u，其dist[u]已经是真正的最短距离（贪心选择的正确性）
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G)
        {eq_dec: EqDec V eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(** 状态记录：已访问顶点集合 + 距离数组 *)
Record St: Type := mkSt {
  visited: V -> Prop;  (** 已访问的顶点集合 *)
  dist: V -> option Z;        (** 当前记录的距离，W_inf表示不可达 *)
}.

Context (src: V)  (** 源点 *)
        (valid_src: vvalid g src).

Instance: Settable St := settable! mkSt <visited; dist>.

(** 初始状态：源点距离为 g_zero，其他顶点距离为 W_inf *)
Definition initSt: St := {|
  visited := ∅;
  dist := fun v => if eq_dec v src then Some 0 else None;
|}.

(** 将顶点u标记为已访问 *)
Definition visit (u: V): program St unit :=
  update' (fun s => s <| visited ::= fun vs => vs ∪ [u] |>).

(** 松弛操作：对于边 e: u -> v，尝试更新 dist[v] = min(dist[v], dist[u] + weight(e)) *)
Definition relax_edge (u: V) (e: E): program St unit :=
  assume (fun s => exists v, step_aux g e u v);;
  v <- get (fun s v => step_aux g e u v);;
  update' (fun s => s <| dist ::= fun dist0 =>
    v !-> (le_min Z_op_le (dist0 v) (Z_op_plus (dist0 u) (weight g e))); dist0 |>).

(** 处理顶点u：标记为已访问，然后松弛所有出边 *)
Definition process_vertex (u: V): program St unit :=
  visit u;;
  forset (fun e => exists v, step_aux g e u v) 
    (relax_edge u).

(** 未访问且距离有限的顶点 *)
Definition unvisited (s: St) (u: V): Prop :=
  vvalid g u /\ ~ u ∈ s.(visited).

(** 选择距离最小的未访问可达顶点 *)
Definition select_min_vertex: program St V :=
  get (fun s u => min_object_of_subset Z_op_le (fun v => unvisited s v) (s.(dist)) u).

(** Dijkstra主算法：重复选择和处理顶点，直到没有未访问的可达顶点 *)
Definition Dijkstra: program St unit :=
  repeat_break (fun _ =>
    choice
      (u <- select_min_vertex;; 
       process_vertex u;;
       ret (by_continue tt))
      (ret (by_break tt))
  ) tt.


(** ===== 循环不变量定义 ===== 
    
    Dijkstra 算法的循环不变量刻画了算法执行过程中状态的关键性质。
    核心思想：将顶点分为已访问和未访问两类，分别维护不同的性质。
*)

(** 
  不变量 1: 已访问顶点的距离是最终的最短距离
  
  含义：对于任何已访问的顶点 v，dist[v] 已经是从源点到 v 的真正最短距离。
  
  形式化：v ∈ visited -> dist[v] = min_weight_distance(src, v)
  
  这是 Dijkstra 算法核心性质：一旦顶点被访问（确定），其距离就不会再改变。
*)
Definition visited_dist_final (s: St): Prop :=
  forall v, v ∈ s.(visited) -> 
    min_weight_distance g src v (s.(dist) v).

(** 
  不变量 2: 未访问顶点的距离是"仅通过已访问顶点"的最短距离
  
  含义：对于未访问的顶点 v，dist[v] 是所有"中间节点都在 visited 中"的路径的最短权重。
  
  形式化：v ∉ visited -> dist[v] = min_weight_distance_in_vset(src, v, visited)
  
  注意：
  - 如果 dist[v] = W_inf，表示通过 visited 无法到达 v
  - 一旦有新顶点 u 加入 visited，通过 u 可能发现更短的路径到达其他未访问顶点
*)
Definition unvisited_dist_optimal (s: St): Prop :=
  forall v, ~ v ∈ s.(visited) ->
    min_weight_distance_in_vset g src v (s.(visited)) (s.(dist) v).

(** 
  不变量 3: 源点性质
  
  含义：源点的距离始终为 g_zero（零元素）
  
  这是初始条件，也是算法的基础。
*)
Definition source_dist_zero (s: St): Prop :=
  s.(dist) src = Some 0.

(** 
  不变量 4: 有效性约束
  
  含义：只有图中的有效顶点才会被访问，且只有有效顶点的距离才可能不是 W_inf
  
  这是健全性的基础。
*)
Definition validity_constraint (s: St): Prop :=
  forall v, v ∈ s.(visited) -> vvalid g v.

(** 完整的循环不变量 *)
Definition loop_invariant (s: St): Prop :=
  visited_dist_final s /\
  unvisited_dist_optimal s /\
  source_dist_zero s /\
  validity_constraint s.


(** ===== 贪心选择的正确性 ===== 
    
    Dijkstra 算法的关键是贪心选择：每次选择 dist 值最小的未访问顶点 u，
    可以保证 dist[u] 已经是真正的最短距离。
    
    为什么？（反证法）
    假设存在更短的路径 P: src ~> u，其权重 < dist[u]。
    考虑 P 上第一个离开 visited 集合的顶点 v：
    - v 的前驱在 visited 中，所以 dist[v] ≤ weight(P 的前缀到 v)
    - 因为权重非负，weight(P 的前缀到 v) < weight(P) < dist[u]
    - 所以 dist[v] < dist[u]
    - 但我们选择了 u 而不是 v，矛盾！（u 应该是最小的）
    
    这个性质保证了贪心策略的正确性。
*)
Definition greedy_choice_correct (s: St) (u: V): Prop :=
  unvisited s u ->
  (forall v, unvisited s v -> Z_op_le (s.(dist) u) (s.(dist) v)) ->
  min_weight_distance g src u (s.(dist) u).


(** ===== 正确性规范 ===== *)

(** 健全性：记录的距离是真实的最短距离 *)
Definition distance_soundness (s: St): Prop :=
  forall v w, s.(dist) v = w -> min_weight_distance g src v w.

(** 完备性：真实的最短距离被正确记录 *)
Definition distance_completeness (s: St): Prop :=
  forall v w, min_weight_distance g src v w -> s.(dist) v = w.

(** 完整正确性：健全性 + 完备性 *)
Definition distance_correct (s: St): Prop :=
  distance_soundness s /\ distance_completeness s.


(** ===== 主定理 ===== 
    
    定理：Dijkstra 算法在初始状态 initSt 上执行，最终得到正确的单源最短路径。
    
    证明路线：
    
    【第一步】证明初始状态满足循环不变量
      需要证明：loop_invariant initSt
      - visited_dist_final: 空集，条件为假，成立
      - unvisited_dist_optimal: 所有顶点都未访问，visited = ∅
        需要证明：对于每个顶点 v
        * 如果 v = src: dist[v] = g_zero，且这是通过空集的最短距离（空路径）
        * 如果 v ≠ src: dist[v] = W_inf，且通过空集无法到达
      - source_dist_zero: 根据 initSt 定义成立
      - validity_constraint: 空集，成立
    
    【第二步】证明循环体保持不变量
      假设 loop_invariant s 成立，选择顶点 u 并处理。
      
      步骤 2.1: 证明 greedy_choice_correct s u
        - 使用反证法
        - 关键：非负权重 + dist[u] 是未访问顶点中最小的
      
      步骤 2.2: 将 u 加入 visited 后
        新状态 s': visited' = visited ∪ {u}
        需要证明：
        a) visited_dist_final s' 成立
           - 对于 v ∈ visited: 沿用 s 的性质
           - 对于 v = u: 使用 greedy_choice_correct
        
        b) unvisited_dist_optimal s' 成立
           - 松弛操作前：dist[v] 是通过 visited 的最短距离
           - 松弛操作后：dist[v] = min(dist[v], dist[u] + weight(u, v))
           - 需要证明这是通过 visited ∪ {u} 的最短距离
           - 使用类似 Floyd 的 relaxation_correct 引理
    
    【第三步】证明终止性
      - 每次循环减少未访问顶点数量
      - 有限图保证算法终止
    
    【第四步】证明终止时的正确性
      终止条件：不存在 unvisited_reachable 的顶点
      即：所有可达顶点都已访问
      
      根据循环不变量：
      - 所有已访问顶点的距离正确（visited_dist_final）
      - 未访问顶点的距离为 W_inf（不可达）
      
      因此：distance_correct 成立
*)

Theorem Dijkstra_correct:
  Hoare (fun s => s = initSt)
        Dijkstra
        (fun _ s => distance_correct s).
Proof.
  unfold Dijkstra.
  (** 
    提示：
    1. 使用 Hoare_repeat_break 规则
    2. 以 loop_invariant 作为循环不变量
    3. 需要证明的关键引理：
       - init_satisfies_invariant: initSt 满足 loop_invariant
       - visit_preserves_invariant: 访问顶点保持不变量
       - relax_preserves_invariant: 松弛操作保持不变量
       - greedy_choice_lemma: 贪心选择的正确性
       - termination_implies_correctness: 终止时不变量蕴含正确性
  *)
Admitted.

End Dijkstra.
