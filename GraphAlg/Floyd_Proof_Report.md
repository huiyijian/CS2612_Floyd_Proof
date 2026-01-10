# Floyd 算法证明扩展报告

## 1. 简介
本报告详细阐述了 Floyd-Warshall 算法形式化验证中一个关键引理的证明过程。具体而言，我们证明了：如果一条边 $e: v \to u$ 满足“松弛条件”（即 $d(s,u) = d(s,v) + w(e)$），那么存在一条从 $s$ 到 $u$ 的最短路径，且该路径的最后一条边是 $e$。

## 2. 形式化陈述
引理 `shortest_path_last_edge` 在 Coq 中的定义如下：

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

## 3. 证明策略

证明采用构造法。已知存在一条从 $s$ 到 $v$ 的最短路径（记为 $p_v$），我们通过将边 $e$ 拼接到 $p_v$ 的末尾来构造一条新路径 $p_u$。

### 3.1 路径构造
我们将 $p_u$ 定义为 $p_v$ 与由边 $e$ 构成的单边路径的连接：
$$ p_u = p_v \circ [v \xrightarrow{e} u] $$
Coq 代码：`pose (p_u := concat_path p_v (single_path v u e))`.

### 3.2 有效性证明
我们必须证明 $p_u$ 是从 $s$ 到 $u$ 的有效路径。这需要满足：
1.  **连通性**：$p_v$ 的尾节点必须与单边路径的头节点（即 $v$）匹配。这由 $p_v$ 结束于 $v$ 保证。
2.  **单步有效性**：单边路径 $[v \xrightarrow{e} u]$ 是有效的，因为 $e$ 是从 $v$ 到 $u$ 的合法边（`step_aux g e v u`）。
3.  **端点匹配**：$p_u$ 必须起始于 $s$ 并终止于 $u$。
    *   起点：与 $p_v$ 相同（$s$）。
    *   终点：与单边路径相同（$u$）。

### 3.3 权重计算
我们需要证明 $weight(p_u) = d(s,u)$。
利用辅助引理 `Zlist_sum_app`，我们证明了连接路径的权重等于各部分权重之和：
$$ weight(p_u) = weight(p_v) + weight(e) $$
代入已知值：
$$ weight(p_u) = w_{sv} + w_e $$
根据假设条件 $w_{su} = w_{sv} + w_e$，我们可以得出：
$$ weight(p_u) = w_{su} $$

### 3.4 最优性证明
最后，我们需要证明 $p_u$ 确实是一条*最短*路径。
*   我们已经证明了 $weight(p_u) = d(s,u)$。
*   根据 `min_weight_distance` 的定义，$d(s,u)$ 是从 $s$ 到 $u$ 的任意路径权重的下界。
*   由于 $p_u$ 达到了这个下界，因此它是一条最短路径。

## 4. 主要挑战与解决方案

### 4.1 权重可加性 (`Zlist_sum_app`)
`path_weight` 函数使用 `fold_right` 对 `option Z` 列表求和。Coq 无法自动简化列表连接上的 `fold_right` 操作。
**解决方案**：我们证明了一个自定义引理 `Zlist_sum_app`：
`forall l1 l2, Zlist_sum (l1 ++ l2) = Z_op_plus (Zlist_sum l1) (Zlist_sum l2)`。
这需要对 `l1` 进行归纳，并仔细处理 `option Z` 的算术运算（`Z_op_plus`）。

### 4.2 路径端点有效性
证明 `tail p_u = u` 需要展开 `concat_path` 和 `single_path` 的定义。
**问题**：Coq 处理连接列表的 `tl_error`（取尾元素）比较繁琐。
**解决方案**：我们利用库引理 `tl_error_last`（或类似逻辑）来证明 `l ++ [x]` 的尾元素确实是 `Some x`。

### 4.3 重写中的子项匹配
在交互式证明过程中，遇到了如 "Found no subterm matching..." 的错误。
**解决方案**：在重写之前，显式地 `unfold` 定义（如 `p_u`, `path_weight`）并使用 `simpl` 暴露子项。对于 `vertex_in_path` 的匹配问题，我们使用了 `remember` 和 `destruct` 来让 Coq 明确列表的结构，从而成功完成匹配。

## 5. 结论
该证明成功展示了“松弛条件”蕴含了扩展最短路径的存在性。这是证明 Floyd-Warshall 等动态规划算法正确性的关键步骤，验证了最优子结构性质在图算法中的应用。
