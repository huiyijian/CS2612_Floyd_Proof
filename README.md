# Floyd算法形式化证明技术文档

## 目录

1. [概述](#1-概述)
2. [基础框架与依赖](#2-基础框架与依赖)
3. [核心定义](#3-核心定义)
4. [辅助引理体系](#4-辅助引理体系)
5. [第二档难度证明](#5-第二档难度最短路径长度的正确性)
6. [第三档难度证明](#6-第三档难度路径重构定理)
7. [证明架构总结](#7-证明架构总结)
8. [附录：重要定义与引理速查](#附录重要定义与引理速查)


---

## 1. 概述

本文档介绍Floyd-Warshall算法的Coq形式化证明，基于Hoare逻辑和循环不变量方法。

**主要文件：**
- `GraphAlg/algorithms/Floyd/Floyd.v`: 主证明文件
- `GraphAlg/graph_lib/examples/floyd.v`: 辅助引理库

**证明目标：** 
- 第二档难度：证明算法的输出确实是最短路径的长度；
- 第三档难度：在上面的基础上证明，如
果 $e$ 是 $v$ 到 $u$ 的一条边，并且 $d(s, u) = d(s, v) + length(e)$，那么存在一条 $s$ 到 $u$ 的最短路
径，其最后一条边是 $e$。
- 第四档难度：修改程序，额外记录一些信息使得最后可以构建出最短
路，证明它的正确性。

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

本部分按照难度等级组织，分为两档：
- **第二档难度**：证明Floyd算法的输出确实是最短路径的长度（第5.A节）
- **第三档难度**：在第二档基础上，证明路径重构定理（第5.B节）

---

## 5 第二档难度：最短路径长度的正确性

### 5.1 证明架构

Floyd算法有**三层嵌套循环**，自底向上证明：

```
Floyd (最外层) - 遍历 k
  └─> Floyd_k - 遍历 j  
        └─> Floyd_j - 遍历 i
              └─> update_dist i j k
```

### 5.2 最内层：距离更新操作

**引理：`update_dist_correct`** 

**程序：** `dist[i,j] := min(dist[i,j], dist[i,k] + dist[k,j])`

**证明要点：**
1. 使用`floyd_relaxation_correct`证明更新后的`dist[i,j]`正确
2. 使用`min_weight_distance_in_vset_stable`处理`i = k`或`j = k`的边界情况
3. 通过`t_update_neq`保证其他列保持不变

### 5.3 中层循环：处理固定列j

原始引理约130行，拆分为4个辅助引理：

**辅助引理1：`invalid_vertex_path_equiv`** 
- **核心思想：** 无效顶点不能作为非空路径起点，中间节点集扩大不影响距离

**辅助引理2：`Floyd_j_init`** 
- **作用：** 证明`processed_i = ∅`时内层循环不变量成立

**辅助引理3：`Floyd_j_final`** 
- **作用：** 从所有行处理完的不变量推导出后置条件
- **关键：** 分`v = j`和`v ≠ j`两种情况处理

**辅助引理4：`Floyd_j_invariant_Proper`** 
- **作用：** 证明内层循环不变量的良定义性（使用`Hoare_forset`的必要条件）

**主引理：`Floyd_j_correct`**

```coq
Lemma Floyd_j_correct: ∀ done k processed_j j,
  Hoare (前置：∀ u v, processed_j v → dist[u,v]正确(done∪{k}))
        (Floyd_j k j)
        (后置：∀ u v, (processed_j∪{j}) v → dist[u,v]正确(done∪{k}))
```

**证明：** 应用`Hoare_forset`，分别使用上述4个辅助引理

### 5.4 外层循环：处理中间节点k

**引理：`Floyd_k_correct`** 

```coq
Lemma Floyd_k_correct: ∀ done k,
  Hoare (Floyd_loop_invariant done)
        (Floyd_k k)
        (Floyd_loop_invariant (done ∪ [k]))
```

**证明：** 类似`Floyd_j_correct`，对所有列j使用`Hoare_forset`，每列调用`Floyd_j_correct`

### 5.5 主定理：Floyd算法的完全正确性

**定理：`Floyd_correct`** 

```coq
Theorem Floyd_correct:
  Hoare initialized_state Floyd (λ _ s, distance_correct s)
```

其中`distance_correct s`包含健全性和完备性

**证明结构：**
1. **初始化：** 空集上的循环不变量由初始状态保证
2. **终止条件：** 当`done`包含所有有效顶点时，受限距离等价于无限制距离
3. **Proper性质：** 应用`Floyd_loop_invariant_Proper`
4. **循环体：** 对每个k调用`Floyd_k_correct`

---

## 6 第三档难度：路径重构定理

### 6.1 问题陈述

**定理目标：** 如果边`e: v → u`满足`d(s,u) = d(s,v) + weight(e)`，则存在一条从s到u的最短路径，其最后一条边恰好是e。

```coq
Lemma shortest_path_last_edge: ∀ s u v e w_su w_sv w_e,
  min_weight_distance g s u (Some w_su) →
  min_weight_distance g s v (Some w_sv) →
  step_aux g e v u →
  weight g e = Some w_e →
  w_su = (w_sv + w_e)%Z →
  ∃ p, min_weight_path g s u p ∧ 
       (∃ p_prev, p = concat_path p_prev (single_path v u e))
```

这是路径重构算法的理论基础。可以通过反向追踪重构路径：找满足`d[s,u] = d[s,v] + w(v,u)`的前驱v，递归地找s到v的路径，然后接上边(v,u)。

### 6.2 关键引理依赖

1. **`min_weight_distance_path_exists`：** 从距离存在性得到路径存在性
2. **`path_concat_valid`：** 两条首尾相连的路径可以拼接
3. **`path_concat_weight`：** 拼接路径的权重等于权重之和
4. **`min_weight_distance_le`：** 最短距离是所有路径权重的下界

### 6.3 证明策略

**核心思想：** 使用最短路径的最优子结构性质

**证明步骤：**
1. 获取s到v的最短路径`p_sv`
2. 构造新路径：`p = concat_path p_sv (single_path v u e)`
3. 证明新路径有效且权重为`w_su`
4. 证明这是最短路径（权重等于已知的最短距离）



---

## 7 证明架构总结

### 7.1 证明层次结构

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

---

## 附录：重要定义与引理速查

### A.1 核心定义

| 定义 | 含义 |
|------|------|
| `St` | 算法状态（距离矩阵） |
| `is_path_through_vset` | 通过指定顶点集的路径 |
| `min_weight_distance_in_vset` | 受限顶点集下的最短距离 |
| `Floyd_loop_invariant` | 主循环不变量 |
| `distance_correct` | 完全正确性（健全性+完备性） |

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

### A.3 算法结构

| 函数/循环 | 作用 |
|----------|------|
| `update_dist i j k` | 松弛：`dist[i,j] := min(dist[i,j], dist[i,k]+dist[k,j])` |
| `Floyd_j k j` | 固定k和j，遍历所有i |
| `Floyd_k k` | 固定k，遍历所有j |
| `Floyd` | 遍历所有k |



---


