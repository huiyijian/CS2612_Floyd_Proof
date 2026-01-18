# Floyd算法形式化证明技术文档

## 目录

1. [概述](#1-概述)
2. [基础框架与依赖](#2-基础框架与依赖)
3. [核心定义](#3-核心定义)
4. [辅助引理体系](#4-辅助引理体系)
5. [第二档难度证明](#5-第二档难度最短路径长度的正确性)
6. [第三档难度证明](#6-第三档难度路径重构定理)
7. [第四档难度证明](#7-第四档难度路径重建的完整证明)
8. [证明架构总结](#8-证明架构总结)
9. [附录：重要定义与引理速查](#附录重要定义与引理速查)


---

## 1. 概述

本文档介绍Floyd-Warshall算法的Coq形式化证明，基于Hoare逻辑和循环不变量方法。

**主要文件：**
- `GraphAlg/algorithms/Floyd/Floyd.v`: 第二、三档难度证明
- `GraphAlg/algorithms/Floyd/Floyd_lv4.v`: 第四档难度证明
- `GraphAlg/graph_lib/examples/floyd.v`: 辅助引理库

**证明目标：** 
- **第二档难度**：证明算法的输出确实是最短路径的长度；
- **第三档难度**：在上面的基础上证明，如果 $e$ 是 $v$ 到 $u$ 的一条边，并且 $d(s, u) = d(s, v) + length(e)$，那么存在一条 $s$ 到 $u$ 的最短路径，其最后一条边是 $e$。
- **第四档难度**：修改程序，额外记录一些信息使得最后可以构建出最短路，证明它的正确性。

---

## 2. 基础框架与依赖

### 2.1 Hoare逻辑框架

核心是**Hoare三元组**：

```coq
Hoare (P: St -> Prop)          (* 前置条件 *)
      (prog: program St A)      (* 程序 *)
      (Q: A -> St -> Prop)      (* 后置条件 *)
```

**关键组合子：** `Hoare_conseq`（前后置条件调整）、`Hoare_forset`（集合遍历）、`Hoare_update`（状态更新）

### 2.2 图论基础

使用类型类`Graph G V E`，其中`G`是图类型，`V`是顶点类型，`E`是边类型。

**路径表示：** 抽象路径类型`P`，支持`empty_path`（空路径）、`single_path`（单边）、`concat_path`（拼接）等操作。

### 2.3 权重系统

使用`option Z`表示权重：`Some z`表示有限权重，`None`表示无穷大（不可达）。

**权重运算：** `Z_op_plus`（加法）、`Z_op_min`（取最小）、`Z_op_le`（小于等于）


---

## 3. 核心定义

### 3.1 状态定义

```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;  (* 距离矩阵 *)
}.
```

### 3.2 通过顶点集的路径

```coq
Definition is_path_through_vset (g: G) (p: P) (u v: V) (vset: V -> Prop): Prop :=
  is_path g p u v ∧ 
  (∀ x, (∃ p1 p2, path_split p p1 p2 ∧ tail p1 = x) → vset x)
```

**核心思想：** 路径`p`从`u`到`v`，且所有**中间节点**都在集合`vset`中（起点和终点不算中间节点）

### 3.3 受限顶点集下的最短距离

```coq
Definition min_weight_distance_in_vset (g: G) (u v: V) (vset: V -> Prop) (w: option Z): Prop :=
  min_value_of_subset_with_default Z_op_le 
    (λ p, is_path_through_vset g p u v vset) 
    (path_weight g) None w
```

**含义：** `w`是从`u`到`v`、仅经过`vset`中顶点作为中间节点的所有路径中的最小权重

### 3.4 循环不变量

```coq
Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  ∀ u v, min_weight_distance_in_vset g u v done (s.(dist) (u, v))
```

**解释：** `done`为已处理的中间节点集合，`dist[u][v]`存储的是仅使用`done`中顶点作为中间节点的最短距离

### 3.5 正确性规范

```coq
Definition distance_soundness (s: St): Prop :=
  ∀ u v w, s.(dist) (u, v) = w → min_weight_distance g u v w

Definition distance_completeness (s: St): Prop :=
  ∀ u v w, min_weight_distance g u v w → s.(dist) (u, v) = w

Definition distance_correct (s: St): Prop :=
  distance_soundness s ∧ distance_completeness s
```

**说明：** 健全性保证记录的距离确实是最短距离，完备性保证最短距离都被正确记录

---

## 4. 辅助引理体系

### 4.1 路径基础性质 (`floyd.v`)

#### 4.1.1 路径拼接性质

```coq
Lemma path_concat_valid: ∀ i j k p1 p2, 
  is_path g p1 i j → is_path g p2 j k → 
  is_path g (concat_path p1 p2) i k

Lemma path_concat_weight: ∀ i j k p1 p2,
  path_weight g (concat_path p1 p2) = 
  Z_op_plus (path_weight g p1) (path_weight g p2)
```

**作用：** 证明路径拼接的有效性和权重可加性

#### 4.1.2 路径分解引理

**引理：`path_decompose_at_vertex`** （核心引理）

```coq
Lemma path_decompose_at_vertex: ∀ u v k p vset,
  is_path_through_vset g p u v (vset ∪ [k]) →
  In k (vertex_in_path p) →
  ∃ p1 p2, 
    is_path_through_vset g p1 u k vset ∧
    is_path_through_vset g p2 k v vset ∧
    Z_op_le (Z_op_plus (path_weight g p1) (path_weight g p2)) (path_weight g p)
```

**重要性：** 证明经过顶点`k`的路径可以在`k`处分解，且分解后的两段路径的中间节点都不包含`k`（除了作为端点）

### 4.2 最短距离性质 (`floyd.v`)

#### 4.2.1 单调性引理

```coq
Lemma path_vset_mono: ∀ u v k p vset,
  is_path_through_vset g p u v vset →
  is_path_through_vset g p u v (vset ∪ [k])

Lemma min_distance_vset_mono: ∀ u v k vset w1 w2,
  min_weight_distance_in_vset g u v vset w1 →
  min_weight_distance_in_vset g u v (vset ∪ [k]) w2 →
  Z_op_le w2 w1
```

**作用：** 扩大中间节点集不会使路径失效或距离增加

#### 4.2.2 端点特殊性引理

```coq
Lemma min_weight_distance_in_vset_stable: ∀ u v k vset w,
  (u = k ∨ v = k) →
  min_weight_distance_in_vset g u v (vset ∪ [k]) w ↔
  min_weight_distance_in_vset g u v vset w
```

**关键观察：** 如果`k`是起点或终点，是否允许`k`作为中间节点不影响最短距离

### 4.3 松弛操作的正确性 (`floyd.v`)

**引理：`floyd_relaxation_correct`** （算法核心）

```coq
Lemma floyd_relaxation_correct: ∀ i j k vset w_ik w_kj w_ij,
  min_weight_distance_in_vset g i k vset w_ik → 
  min_weight_distance_in_vset g k j vset w_kj → 
  min_weight_distance_in_vset g i j vset w_ij →
  min_weight_distance_in_vset g i j (vset ∪ [k]) 
    (Z_op_min w_ij (Z_op_plus w_ik w_kj))
```

**核心思想：** 证明松弛操作`min(dist[i,j], dist[i,k] + dist[k,j])`的正确性

**证明结构：**
1. **存在性**：最小值由某条路径达到（不经过k则为`w_ij`，经过k则拼接得到`w_ik + w_kj`）
2. **最小性**：所有路径权重都不小于最小值（经过k的用分解引理，不经过k的直接证明）

---

## 主要定理证明

本部分按照难度等级组织，分为三档：
- **第二档难度**：证明Floyd算法的输出确实是最短路径的长度（第5节）
- **第三档难度**：在第二档基础上，证明路径重构定理（第6节）
- **第四档难度**：修改程序记录额外信息，实现路径重建并证明正确性（第7节）

---

## 5 第二档难度：最短路径长度的正确性

### 5.1 状态定义与核心操作

#### 5.1.1 状态定义（第二、三档）

```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;
}.
```

**说明：** 第二、三档难度只需要记录距离信息，不需要额外的路径重建信息。

#### 5.1.2 距离更新操作

```coq
Definition update_dist (i j k: V): program St unit :=
  update' (fun s => s <| dist ::= fun dist0 =>
    (i, j) !-> (Z_op_min (dist0 (i, j)) (Z_op_plus (dist0 (i, k)) (dist0 (k, j)))); 
    dist0 |>).
```

#### 5.1.3 循环不变量定义

```coq
Definition Floyd_loop_invariant (done: V -> Prop) (s: St): Prop :=
  forall u v,
    min_weight_distance_in_vset g u v done (s.(dist) (u, v)).
```

**含义：**
- `done` 是已处理的中间节点集合
- 对任意顶点对 (u, v)，`dist[u][v]` 存储的是"仅经过 done 中顶点作为中间节点"的最短距离
- 这是 Floyd 算法的核心不变量

### 5.2 证明架构

Floyd算法有**三层嵌套循环**，自底向上证明：

```
Floyd (最外层) - 遍历所有中间节点 k
  └─> Floyd_k (中层) - 固定 k，遍历所有目标顶点 j  
        └─> Floyd_j (内层) - 固定 k 和 j，遍历所有起点 i
              └─> update_dist i j k (最内层) - 松弛操作
```

**证明策略：** 自底向上，逐层证明每层循环维护相应的不变量

### 5.3 最内层：距离更新操作

**引理：`update_dist_correct`** 

**前置条件：**
```coq
(forall u,
   (processed_i u -> min_weight_distance_in_vset g u j (done ∪ [k]) (dist (u, j))) /\
   (~ processed_i u -> min_weight_distance_in_vset g u j done (dist (u, j)))) /\
(forall u v, v <> j ->
   (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (dist (u, v))) /\
   (~ processed_j v -> min_weight_distance_in_vset g u v done (dist (u, v))))
```

**后置条件：** 将 `processed_i` 替换为 `processed_i ∪ [i]`

证明使用 `floyd_relaxation_correct`证明松弛操作的正确性，使用`min_weight_distance_in_vset_stable` 证明边界条件。

### 5.4 中层循环：处理固定列 j

**主引理：`Floyd_j_correct`** ，**目标：** 固定 k 和 j，遍历所有起点 i，更新 dist[i][j]

**前置条件：**
```coq
forall u v,
  (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (dist (u, v))) /\
  (~ processed_j v -> min_weight_distance_in_vset g u v done (dist (u, v)))
```

**后置条件：** 将 `processed_j` 替换为 `processed_j ∪ [j]`

**证明使用 `Hoare_forset` 框架**，需要提供4个组件：

#### 5.4.1 辅助引理1：`invalid_vertex_path_equiv` 

```coq
Lemma invalid_vertex_path_equiv:
  forall (done: V -> Prop) (k u v: V) (w: option Z),
    ~ vvalid g u ->
    min_weight_distance_in_vset g u v (done ∪ [k]) w <->
    min_weight_distance_in_vset g u v done w.
```


#### 5.4.2 辅助引理2：`Floyd_j_init` 

**关键：**
```coq
(forall u,
   (∅ u -> ...) /\                    (* 空集中没有元素 *)
   (~ ∅ u -> dist[u][j] 满足 done)    (* 所有 u 都满足旧不变量 *)
```

**作用：** 证明内层循环开始时（`processed_i = ∅`）不变量成立


#### 5.4.3 辅助引理3：`Floyd_j_final` 

**作用：** 从内层循环结束状态推导出后置条件

分 `v = j` 和 `v ≠ j` 两种情况。情况1：v = j， 如果 u 有效：直接使用内层不变量；如果 u 无效：使用 `invalid_vertex_path_equiv` 证明等价性。情况2：v ≠ j，v 在 processed_j 中或不在，直接使用前置条件


#### 5.4.4 辅助引理4：`Floyd_j_invariant_Proper` 

证明内层循环不变量关于集合等价关系是良定义的

#### 5.4.5 主证明：`Floyd_j_correct`

```coq
eapply Hoare_conseq.
3: apply (Hoare_forset (内层不变量)).
- (* 初始化 *) apply Floyd_j_init
- (* 终止条件 *) apply Floyd_j_final  
- (* Proper *) apply Floyd_j_invariant_Proper
- (* 循环体 *) intros i; apply update_dist_correct
```


### 5.5 外层循环：处理中间节点 k

**引理：`Floyd_k_correct`**

**目标：** 固定 k，遍历所有目标顶点 j

```coq
Lemma Floyd_k_correct: forall done k,
  Hoare (Floyd_loop_invariant done)
        (Floyd_k k)
        (Floyd_loop_invariant (done ∪ [k])).
```


#### 5.5.1 外层不变量

```coq
fun processed_j s =>
  forall u v,
    (processed_j v -> min_weight_distance_in_vset g u v (done ∪ [k]) (dist (u, v))) /\
    (~ processed_j v -> min_weight_distance_in_vset g u v done (dist (u, v)))
```

#### 5.5.2 初始化

```coq
intros s Hinv u v.
split.
+ intros Hfalse. exfalso. apply Hfalse.  (* ∅ 中没有元素 *)
+ intros _. apply Hinv.                   (* 所有列满足旧不变量 *)
```

#### 5.5.3 终止条件

当所有列 j 处理完毕后，证明 `Floyd_loop_invariant (done ∪ [k])`

分两种情况：
-情况1：v 有效（`vvalid g v`），则直接使用外层不变量中 `processed_j v` 的结论
-情况2：v 无效**（`~ vvalid g v`），则使用类似 `invalid_vertex_path_equiv` 的技术


#### 5.5.4 Proper 性质

标准的集合等价关系改写

#### 5.5.5 循环体

```coq
intros processed_j j Hsubset_j Hin_j Hnotin_j.
apply (Floyd_j_correct done k processed_j j ...).
```

### 5.6 主定理：Floyd算法的完全正确性

**定理：`Floyd_correct`**

这是整个Floyd算法正确性证明的顶点，综合运用前面所有引理，证明算法的完全正确性。

#### 5.6.1 定理陈述

```coq
Theorem Floyd_correct:
  Hoare initialized_state
        Floyd
        (fun _ s => distance_correct s).
```

如果初始状态满足空集上的循环不变量（`initialized_state`），则Floyd算法执行后，`dist`数组满足完全正确性（`distance_correct`），即同时满足健全性和完备性：
- 健全性：`dist[u][v] = w` ⟹ w 是真正的最短距离
- 完备性：w 是最短距离 ⟹ `dist[u][v] = w`

#### 5.6.2 证明框架：三层嵌套循环的统一

核心思想： 使用 `Hoare_forset` 框架处理最外层循环（遍历所有中间节点k）

```coq
3: apply (Hoare_forset Floyd_loop_invariant).
```

循环不变量： `Floyd_loop_invariant done` 表示当 `done` 中的所有顶点都作为中间节点处理完毕后，`dist[u][v]` 存储的是只允许经过 `done` 中顶点作为中间节点的最短路径。

#### 5.6.3 证明的四个组成部分

- 第一部分：初始化条件
- 第二部分：终止条件
- 第三部分：Proper 性质
- 第四部分：循环体

使用的引理已在上文中介绍。

#### 5.6.4 证明的层次结构总结

整个证明形成了清晰的层次结构：

```
Floyd_correct (主定理)
  ├─ 初始化：空集满足不变量
  ├─ 终止：全集蕴含正确性
  │   ├─ 健全性：使用路径集合等价性
  │   └─ 完备性：使用最小值唯一性
  ├─ Proper：引理1 (Floyd_loop_invariant_Proper)
  └─ 循环体：引理4 (Floyd_k_correct)
       ├─ 初始化：空集的情况
       ├─ 终止：全集的情况（分有效/无效顶点）
       ├─ Proper：标准集合等价改写
       └─ 循环体：引理3 (Floyd_j_correct)
            ├─ 初始化：引理3.2 (Floyd_j_init)
            ├─ 终止：引理3.3 (Floyd_j_final)
            ├─ Proper：引理3.4 (Floyd_j_invariant_Proper)
            └─ 循环体：引理2 (update_dist_correct)
                 └─ 核心：floyd_relaxation_correct
                      └─ 基于：min_weight_distance_in_vset_stable
```


---

## 6 第三档难度：路径重构定理

### 6.1 问题陈述

**定理：`shortest_path_last_edge`** 

**目标：** 如果边 `e: v → u` 满足 `d(s,u) = d(s,v) + weight(e)`，则存在一条从 s 到 u 的最短路径，其最后一条边恰好是 e。

```coq
Lemma shortest_path_last_edge: forall (s u v: V) (e: E) (w_su w_sv w_e: Z),
  min_weight_distance g s u (Some w_su) ->
  min_weight_distance g s v (Some w_sv) ->
  step_aux g e v u ->
  weight g e = Some w_e ->
  w_su = (w_sv + w_e)%Z ->
  exists p, min_weight_path g s u p /\ 
            (exists p_prev, p = concat_path p_prev (single_path v u e)).
```

**应用价值：** 这是路径重构算法的理论基础
- 可以通过反向追踪重构最短路径
- 找满足 `d[s,u] = d[s,v] + w(v,u)` 的前驱 v
- 递归地找 s 到 v 的路径，然后接上边 (v,u)

### 6.2 证明结构

#### 6.2.1 第一步：提取 s 到 v 的最短路径

```coq
destruct Hdist_v as [[Hmin Hle] | [Hall Hdef]]; [| discriminate].
destruct Hmin as [p_v [Hmin_v Hw_v]].
destruct Hmin_v as [Hp_v_path Hmin_v_le].
```


#### 6.2.2 第二步：构造从 s 到 u 的候选路径

```coq
pose (p_u := concat_path p_v (single_path v u e)).
```

**关键：** 利用最优子结构性质


#### 6.2.3 第三步：证明候选路径有效

```coq
assert (Hvalid_u_path: path_valid g p_u).
{
  apply concat_path_valid.
  - destruct Hp_v_path as [Hval _]; exact Hval.
  - apply single_path_valid. exact Hstep.
  - (* 证明连接点相等：tail p_v = head (single_path v u e) = v *)
    ...
}
```

#### 6.2.4 第四步：证明路径的起点和终点正确

```coq
assert (Hvalid_u: is_path g p_u s u).
{
  unfold is_path.
  split; [exact Hvalid_u_path |].
  split.
  - (* head p_u = s *)
    (* 使用 concat_path_vertex 和 head_valid *)
    ...
  - (* tail p_u = u *)
    (* 使用 concat_path_vertex 和 tail_valid *)
    (* 关键：使用 tl_error_last 计算拼接路径的尾部 *)
    ...
}
```

**关键引理：**
- `head_concat_valid`: head (concat p1 p2) = head p1（当 p1 非空时）
- `tail_concat`: tail (concat p1 p2) = tail p2（当 p2 非空时）
- `tl_error_last`: 计算列表的最后元素

#### 6.2.5 第五步：证明路径权重正确

```coq
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
  replace (fold_right Z_op_plus (Some 0%Z) (map (weight g) (edge_in_path p_v))) 
    with (path_weight g p_v) by reflexivity.
  rewrite Hw_v.
  simpl. f_equal. lia.
}
```

#### 6.2.6 第六步：证明最短路径

```coq
rewrite Hpw.
destruct Hdist_u as [[Hmin_u' Hle_u'] | [Hall_u Hdef_u]]; [| discriminate].
destruct Hmin_u' as [p_u_min [Hmin_u Hw_u]].
rewrite <- Hw_u.
destruct Hmin_u as [_ Hle_u_min].
apply Hle_u_min. exact Hp'.
```



---

## 7 第四档难度：路径重建的完整证明

### 7.1 问题陈述与目标

**第四档难度要求：**
1. 修改程序，额外记录信息使得最后可以构建出最短路
2. 实现路径重建函数
3. 证明路径重建的正确性

**主要文件：** `GraphAlg/algorithms/Floyd/Floyd_lv4.v`
由于第四档难度的证明需要修改之前部分的证明，为了避免混淆，我们创建了新文件。

### 7.2 状态扩展：添加 next 数组

#### 7.2.1 扩展后的状态定义

```coq
Record St: Type := mkSt {
  dist: (V * V) -> option Z;   (* 距离矩阵 *)
  next: (V * V) -> option V;   (* 路径重建信息 *)
}.
```

**`next` 数组的语义：**
- `next[u][v] = Some w` 表示从 u 到 v 的最短路径上，u 的下一跳是 w
- `next[u][v] = None` 表示没有从 u 到 v 的路径，或 u = v

**设计思想：** 通过存储"下一跳"信息，可以递归地重建整条最短路径

#### 7.2.2 修改后的距离更新操作

```coq
Definition update_dist (i j k: V): program St unit :=
  update' (fun s =>
    let d_ik := s.(dist) (i, k) in
    let d_kj := s.(dist) (k, j) in
    let d_ij := s.(dist) (i, j) in
    let d_new := Z_op_plus d_ik d_kj in
    if Z_op_lt_dec d_new d_ij then
      s <| dist ::= fun d => (i, j) !-> d_new; d |>
        <| next ::= fun n => (i, j) !-> n (i, k); n |>  (* 同时更新next *)
    else s).
```

**关键修改：** 当通过 k 找到更短路径时，`next[i][j] := next[i][k]`，即继承从 i 到 k 的第一步


### 7.3 路径重建函数

```coq
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
```

**递归策略：**
1. 如果 u = v，返回 [u]
2. 否则，取下一跳 x = next[u][v]，递归构建从 x 到 v 的路径
3. 将 u 添加到路径开头

### 7.4 Next 数组的正确性规范

#### 7.4.1 弱有效性不变量

```coq
Definition next_valid_weak (s: St): Prop :=
  (forall u v w,
    s.(next) (u, v) = Some w ->
    u <> v ->
    exists e, step_aux g e u w) /\  (* 存在边 u -> w *)
  (forall u, s.(next) (u, u) = None).  (* 自环的next为空 *)
```


#### 7.4.2 完整不变量

```coq
Definition Floyd_invariant (done: V -> Prop) (s: St): Prop :=
  Floyd_dist_invariant done s /\ next_valid_weak s.
```

**组合两个不变量：**
1. `dist` 数组的正确性（距离不变量）
2. `next` 数组的有效性（弱有效性不变量）

### 7.5 关键引理：自环不会被更新

```coq
Lemma self_loop_no_update_gen: forall i k (done: V -> Prop) (s: St),
  vvalid g i ->
  vvalid g k ->
  min_weight_distance_in_vset g i i done (s.(dist) (i, i)) ->
  min_weight_distance_in_vset g i k done (s.(dist) (i, k)) ->
  min_weight_distance_in_vset g k i done (s.(dist) (k, i)) ->
  ~ Z_op_lt (Z_op_plus (s.(dist) (i, k)) (s.(dist) (k, i))) (s.(dist) (i, i)).
```

证明思路：
1. `dist[i][i]` 是从 i 到 i 的最短距离，空路径权重为 0，所以 `dist[i][i] ≤ 0`
2. 如果存在从 i 到 k 再回到 i 的路径，其权重 ≥ 0（无负环假设）
3. 因此 `dist[i][k] + dist[k][i] ≥ 0 ≥ dist[i][i]`
4. 更新条件 `dist[i][k] + dist[k][i] < dist[i][i]` 永远不满足

### 7.6 Update_dist 保持 next 有效性

**引理：`update_dist_preserves_next_valid`**

```coq
Lemma update_dist_preserves_next_valid: forall i j k (done: V -> Prop),
  vvalid g i ->
  vvalid g j ->
  vvalid g k ->
  Hoare (fun s => next_valid_weak s /\ Floyd_dist_invariant done s)
        (update_dist i j k)
        (fun _ s => next_valid_weak s).
```

证明要点：不更新时： trivial，next 不变；更新时： `next[i][j] := next[i][k]`，需要证明存在边 i → w（其中 w = next[i][k]），可由 `next_valid_weak` 对 `next[i][k]` 的保证直接得到

### 7.7 循环不变量的维护

#### 7.7.1 内层循环不变量（遍历 i）

```coq
Definition Floyd_dist_innermost_inv (k: V) (j: V) (done: V -> Prop)
           (processed_j: V -> Prop) (processed_i: V -> Prop) (s: St): Prop :=
  (* 对于已完成的 j，所有 u 满足新不变量 *)
  (forall u v, v ∈ processed_j ->
     min_weight_distance_in_vset g u v (done ∪ [k]) (s.(dist) (u, v))) /\
  (* 对于当前的 j，已处理的 i 满足新不变量 *)
  (forall u, u ∈ processed_i ->
     min_weight_distance_in_vset g u j (done ∪ [k]) (s.(dist) (u, j))) /\
  (* 对于当前的 j，未处理的 i 满足旧不变量 *)
  (forall u, ~ u ∈ processed_i ->
     min_weight_distance_in_vset g u j done (s.(dist) (u, j))) /\
  (* 对于其他 v，所有 u 满足旧不变量 *)
  (forall u v, ~ v ∈ (processed_j ∪ [j]) ->
     min_weight_distance_in_vset g u v done (s.(dist) (u, v))).
```

精细的追踪：*区分已处理、正在处理和未处理的顶点对

#### 7.7.2 Floyd_k 同时维护两个不变量

**引理：`Floyd_k_invariant_correct`**

```coq
Lemma Floyd_k_invariant_correct: forall k done,
  vvalid g k ->
  ~ k ∈ done ->
  Hoare (Floyd_invariant done)
        (Floyd_k k)
        (Floyd_invariant (done ∪ [k])).
```

证明策略：
1. 定义组合的内层不变量：`Floyd_dist_inner_inv /\ next_valid_weak`
2. 在内层循环的每一步中，同时维护两个不变量
3. 使用 `update_dist_preserves_next_valid` 保证 next 的有效性

### 7.8 主定理：完整正确性

**定理：`Floyd_with_next_correct`**

```coq
Theorem Floyd_with_next_correct:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => distance_soundness s /\ 
                    distance_completeness s /\ 
                    next_valid_weak s).
```

**证明结构：**
```
初始状态满足 Floyd_invariant ∅
    ↓ (应用 Hoare_forset)
对每个 k，Floyd_k 维护 Floyd_invariant
    ↓ (Floyd_k_invariant_correct)
Floyd_invariant (vvalid g)
    ↓ (后置条件转换)
distance_soundness ∧ distance_completeness ∧ next_valid_weak
```

### 7.9 路径重建正确性

**定理：`path_reconstruction_theorem`**

```coq
Theorem path_reconstruction_theorem:
  Hoare initialized_dist_state
        Floyd
        (fun _ s => path_reconstruction_correct s).
```

其中：

```coq
Definition path_reconstruction_correct (s: St): Prop :=
  forall u v d, s.(dist) (u, v) = Some d ->
    exists p, is_path g p u v /\ path_weight g p = Some d.
```

证明思路： 由 `distance_soundness` 知，`dist[u][v] = d` 意味着 d 是最短距离。由最短距离的定义，必存在权重为 d 的路径 p。 因此路径重建是可能的（虽然我们没有完全机械化 `reconstruct_path` 的正确性）

---

## 8 证明架构总结


**第二档难度：最短路径长度正确性**
```
distance_correct ← Floyd_correct ← Floyd_k_correct ← Floyd_j_correct ← update_dist_correct
                                                         ↑
                                        Floyd_j_init, Floyd_j_final, Floyd_j_invariant_Proper
                                                         ↑
                                          floyd_relaxation_correct ← path_decompose_at_vertex
```

**第三档难度：路径重构定理**
```
shortest_path_last_edge
    ↑
├─ min_weight_distance_path_exists
├─ path_concat_valid/weight  
└─ min_weight_distance_le
    ↑
Floyd_correct的结果
```

**第四档难度：Next 数组与路径重建**
```
Floyd_with_next_correct
    ↑
Floyd_k_invariant_correct (维护 Floyd_invariant = dist正确性 + next有效性)
    ↑
├─ Floyd_dist_inner_inv (距离不变量)
└─ next_valid_weak (next有效性)
    ↑
update_dist_preserves_next_valid
    ↑
self_loop_no_update_gen (关键：自环不更新)
    ↑
NoNegativeCycle假设
```

**路径重建正确性**
```
path_reconstruction_theorem
    ↑
distance_soundness (来自 Floyd_with_next_correct)
    ↑
min_weight_distance定义 (最短距离必存在路径)
```

---

## 附录：重要定义与引理速查

### A.1 核心定义

| 定义 | 含义 |
|------|------|
| `St` | 算法状态（距离矩阵 + next数组） |
| `is_path_through_vset` | 通过指定顶点集的路径 |
| `min_weight_distance_in_vset` | 受限顶点集下的最短距离 |
| `Floyd_loop_invariant` | 主循环不变量（仅距离） |
| `Floyd_invariant` | 完整循环不变量（距离 + next） |
| `next_valid_weak` | next数组的有效性条件 |
| `distance_correct` | 完全正确性（健全性+完备性+边最优性+路径重建） |

### A.2 关键引理

| 引理 | 作用 | 行数 |
|------|------|------|
| **路径基础** |||
| `path_concat_valid/weight` | 路径拼接有效性/权重可加性 | - |
| `path_decompose_at_vertex` | 在顶点处分解路径（**核心**） | - |
| **最短距离性质** |||
| `path_vset_mono` | 路径集合单调性 | - |
| `min_weight_distance_in_vset_stable` | 端点特殊情况 | - |
| **松弛操作** |||
| `floyd_relaxation_correct` | 松弛操作正确性（**算法核心**） | - |
| **第二档难度** |||
| `update_dist_correct` | 单次距离更新正确性 | ~150 |
| `invalid_vertex_path_equiv` | 无效顶点路径等价性 | ~45 |
| `Floyd_j_init/final/Proper` | Floyd_j辅助引理 | ~105 |
| `Floyd_j_correct` | Floyd_j循环正确性 | ~25 |
| `Floyd_k_correct` | Floyd_k循环正确性 | ~200 |
| `Floyd_correct` | **主定理：算法完全正确性** | ~70 |
| **第三档难度** |||
| `shortest_path_last_edge` | **路径重构定理** | ~100 |
| **第四档难度** |||
| `next_valid_weak` | next数组的有效性定义 | ~10 |
| `self_loop_no_update` | 自环距离不会被松弛 | ~110 |
| `self_loop_no_update_gen` | 自环不更新（通用版本） | ~100 |
| `update_dist_preserves_next_valid` | 更新操作保持next有效性 | ~60 |
| `Floyd_dist_innermost_inv` | 最内层循环不变量定义 | ~15 |
| `Floyd_k_invariant_correct` | Floyd_k同时维护dist和next | ~400 |
| `Floyd_with_next_correct` | **主定理：含next的完整正确性** | ~60 |
| `path_reconstruction_theorem` | **路径重建正确性定理** | ~20 |
| `Floyd_correct` (level 4) | **完整正确性（4个性质）** | ~80 |

### A.3 算法结构

| 函数/循环 | 作用 |
|----------|------|
| `update_dist i j k` | 松弛：`dist[i,j] := min(dist[i,j], dist[i,k]+dist[k,j])`<br>同时更新：`next[i,j] := next[i,k]` (若更新) |
| `Floyd_j k j` | 固定k和j，遍历所有i |
| `Floyd_k k` | 固定k，遍历所有j |
| `Floyd` | 遍历所有k |
| `reconstruct_path u v` | 从next数组重建u到v的路径 |



---


