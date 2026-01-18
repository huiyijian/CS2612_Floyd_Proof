# Floyd-Warshall 算法形式化验证文档

## 概述

本文档描述了 Floyd-Warshall 算法在 Coq 证明助手中的完整形式化验证实现。该实现完成了**第四档难度**的所有证明要求，所有证明均使用 `Qed` 完成，无任何 `Admitted`。

## 文件结构

- **主文件**: `GraphAlg/algorithms/Floyd/Floyd.v`
- **依赖库**:
  - `SetsClass` - 集合论基础
  - `GraphLib` - 图论基础库（`graph_basic`, `reachable_basic`, `path`, `path_basic`, `epath`, `Zweight`）
  - `MonadLib` - 状态单子与 Hoare 逻辑（`StateRelBasic`, `StateRelHoare`, `FixpointLib`）
  - `MaxMinLib` - 最大最小值库
  - `ListLib` - 列表辅助库

## 核心数据结构

### 状态定义 (`St`)

```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;   (* 距离矩阵 *)
  next: (V * V) -> option V;   (* 路径重建信息 *)
}.
```

- `dist (u, v)`: 存储顶点 u 到 v 的最短距离，`None` 表示不可达
- `next (u, v)`: 存储 u 到 v 最短路径上的下一个顶点

### Option Z 上的运算

```coq
Definition Z_op_lt (x y: option Z): Prop    (* 严格小于 *)
Definition Z_op_le (x y: option Z): Prop    (* 小于等于 *)
Definition Z_op_plus: option Z -> option Z -> option Z  (* 加法 *)
Definition Z_op_min: option Z -> option Z -> option Z   (* 取最小 *)
```

语义：`None` 表示无穷大 (∞)，任何有限值都小于无穷大。

## 算法实现

### 松弛操作 (`update_dist`)

```coq
Definition update_dist (i j k: V): program St unit :=
  update' (fun s =>
    let d_ik := s.(dist) (i, k) in
    let d_kj := s.(dist) (k, j) in
    let d_ij := s.(dist) (i, j) in
    let d_new := Z_op_plus d_ik d_kj in
    if Z_op_lt_dec d_new d_ij then
      s <| dist ::= fun d => (i, j) !-> d_new; d |>
        <| next ::= fun n => (i, j) !-> n (i, k); n |>
    else s).
```

核心思想：如果通过中间点 k 的路径更短，则更新距离并记录路径信息。

### 三层循环结构

```coq
Definition Floyd_j (k: V) (j: V): program St unit :=
  forset (fun v => vvalid g v) (fun i => update_dist i j k).

Definition Floyd_k (k: V): program St unit :=
  forset (fun v => vvalid g v) (Floyd_j k).

Definition Floyd: program St unit :=
  forset (fun v => vvalid g v) Floyd_k.
```

## 循环不变量

### 外层循环不变量 (`Floyd_dist_invariant`)

```coq
Definition Floyd_dist_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v, min_weight_distance_in_vset g u v done (s.(dist) (u, v)).
```

**语义**: 对于所有顶点对 (u, v)，`dist[u][v]` 等于只允许通过 `done` 集合中顶点作为中间点的最短路径长度。

### 中层循环不变量 (`Floyd_dist_inner_inv`)

```coq
Definition Floyd_dist_inner_inv (k: V) (done processed_j: V -> Prop) (s: St): Prop :=
  (* 对于已处理的 j，所有 u 满足新不变量 (done ∪ [k]) *)
  (forall u v, v ∈ processed_j ->
    min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
  (* 对于未处理的 v，所有 u 满足旧不变量 (done) *)
  (forall u v, v ∉ processed_j ->
    min_weight_distance_in_vset g u v done (s.(dist) (u, v))).
```

### 最内层循环不变量 (`Floyd_dist_innermost_inv`)

```coq
Definition Floyd_dist_innermost_inv (k j: V) (done processed_j processed_i: V -> Prop) (s: St): Prop :=
  (* 对于 v ∈ processed_j，所有 u 满足新不变量 *)
  (forall u v, v ∈ processed_j ->
    min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
  (* 对于当前的 j，已处理的 i 满足新不变量 *)
  (forall u, u ∈ processed_i ->
    min_weight_distance_in_vset g u j (done ∪ [k]) (s.(dist) (u, j))) /\
  (* 对于当前的 j，未处理的 i 满足旧不变量 *)
  (forall u, u ∉ processed_i ->
    min_weight_distance_in_vset g u j done (s.(dist) (u, j))) /\
  (* 对于 v ∉ processed_j ∪ [j]，所有 u 满足旧不变量 *)
  (forall u v, v ∉ (processed_j ∪ [j]) ->
    min_weight_distance_in_vset g u v done (s.(dist) (u, v))).
```

## 正确性规范

### 1. 距离健全性 (`distance_soundness`)

```coq
Definition distance_soundness (s: St): Prop :=
  forall u v d, s.(dist) (u, v) = Some d ->
    min_weight_distance g u v (Some d).
```

如果算法输出距离 d，则 d 确实是最短距离。

### 2. 距离完备性 (`distance_completeness`)

```coq
Definition distance_completeness (s: St): Prop :=
  forall u v d, min_weight_distance g u v (Some d) ->
    s.(dist) (u, v) = Some d.
```

如果存在最短距离 d，则算法正确输出 d。

### 3. 边最优性 (`edge_optimality`) - 第三档要求

```coq
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
```

如果 e 是 v 到 u 的边，且 d(s,u) = d(s,v) + weight(e)，则存在 s 到 u 的最短路径，其最后一条边是 e。

### 4. 路径重建正确性 (`path_reconstruction_correct`) - 第四档要求

```coq
Definition path_reconstruction_correct (s: St): Prop :=
  forall u v d, s.(dist) (u, v) = Some d ->
    exists p, is_path g p u v /\ path_weight g p = Some d.
```

对于任意记录的距离，都存在对应的有效路径。

## 主要定理

### 定理 1: Floyd 算法距离正确性

```coq
Theorem Floyd_dist_correct:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => distance_soundness s /\ distance_completeness s).
```

**证明策略**:
1. 使用 `Hoare_forset` 引理处理三层 `forset` 循环
2. 对每层循环维护相应的不变量
3. 通过 `min_dist_recur` 引理处理松弛操作的正确性
4. 最终利用 `path_through_vvalid_equiv` 将受限路径集合等价转换为完整路径集合

### 定理 2: 完整正确性

```coq
Theorem Floyd_correct:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => distance_correct s).
```

证明算法满足所有四个正确性属性。

## 关键辅助引理

### 1. 距离递推引理 (`min_dist_recur`)

```coq
Lemma min_dist_recur: forall i j k done,
  vvalid g k -> k ∉ done ->
  forall d_ij d_ik d_kj,
    min_weight_distance_in_vset g i j done d_ij ->
    min_weight_distance_in_vset g i k done d_ik ->
    min_weight_distance_in_vset g k j done d_kj ->
    min_weight_distance_in_vset g i j (done ∪ [k]) (Z_op_min d_ij (Z_op_plus d_ik d_kj)).
```

核心递推关系：添加中间点 k 后的最短距离 = min(原距离, 经过 k 的距离)。

### 2. 距离稳定性引理

```coq
Lemma min_dist_stable_k: forall i j done d,
  vvalid g k -> k ∉ done ->
  min_weight_distance_in_vset g i j done d <->
  min_weight_distance_in_vset g i j (done ∪ [k]) d.
```

当 k 不在当前路径中时，添加 k 到允许集合不改变最短距离。

### 3. 路径有效顶点等价

```coq
Lemma path_through_vvalid_equiv: forall u v,
  Sets.equiv
    (fun p => is_path_through_vset g p u v (vvalid g))
    (fun p => is_path g p u v).
```

允许所有有效顶点作为中间点的路径集合等价于所有路径的集合。

### 4. 路径拼接有效性 (`concat_path_is_path`)

```coq
Lemma concat_path_is_path: forall src mid dst p1 p2,
  is_path g p1 src mid ->
  is_path g p2 mid dst ->
  is_path g (concat_path p1 p2) src dst.
```

## 证明中使用的关键技术

### 1. Hoare 逻辑

使用 `StateRelHoare` 库提供的 Hoare 三元组进行程序验证：

```coq
Definition Hoare (P: St -> Prop) (c: program St A) (Q: A -> St -> Prop): Prop
```

### 2. 路径分解

使用 `Destruct1nPath` 和 `Destructn1Path` 对路径进行归纳分解：

- `destruct_1n_path`: 从头部分解路径
- `destruct_n1_path`: 从尾部分解路径

### 3. 集合论推理

大量使用 `SetsClass` 库进行集合等价和包含关系的证明。

### 4. 经典逻辑

使用 `Classical_Prop` 中的排中律处理某些情况分析。

## 假设条件

1. **无负权环** (`NoNegativeCycle g`): 图中不存在负权环
2. **有效图** (`gvalid g`): 图结构有效
3. **边唯一性** (`StepUniqueDirected`): 两顶点间边的唯一确定性
4. **路径唯一性** (`path_unique`): 相同起点和边序列确定唯一路径

## 编译说明

```bash
cd "GraphAlg_1224 - 副本"
coqc -Q GraphAlg/sets SetsClass \
     -Q GraphAlg/graph_lib GraphLib \
     -Q GraphAlg/monadlib MonadLib \
     -Q GraphAlg/fixedpoints FP \
     -Q GraphAlg/coq-record-update/src RecordUpdate \
     -Q GraphAlg/algorithms Algorithms \
     -Q GraphAlg/MaxMinLib MaxMinLib \
     -Q GraphAlg/ListLib ListLib \
     GraphAlg/algorithms/Floyd/Floyd.v
```

## 已知警告

编译时会出现关于 `app_length` 的弃用警告（Coq 8.20+），建议使用 `length_app` 替代。这不影响证明的正确性。

## 总结

本实现完成了 Floyd-Warshall 算法的完整形式化验证，包括：

1. ✅ 算法输出确实是最短路径长度（健全性 + 完备性）
2. ✅ 边最优性：满足特定条件时存在以该边结尾的最短路径
3. ✅ 路径重建正确性：对于任意记录的距离都存在对应的有效路径
4. ✅ 所有证明完整，无 `Admitted`

证明代码约 1100 行，涵盖了循环不变量的建立与维护、路径分解与拼接、集合等价转换等多种证明技术。
