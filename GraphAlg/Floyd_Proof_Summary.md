# Floyd 算法形式化证明进展总结

**日期**: 2026-01-17
**分支**: `level_4`

## 1. 当前状态
- **代码分支**：已创建新分支 `level_4` 并提交了当前所有修改。
- **编译状态**：`Floyd.v` 文件目前无法通过编译，报错位置在第 1284 行 (`min_dist_invalid_u` 引理)。
- **核心文件**：`algorithms/Floyd/Floyd.v`。

## 2. 已完成的工作
1.  **类型修复**：修正了 `min_value_empty` 引理的类型签名，添加了 `TotalOrder` 约束。
2.  **不变量扩展**：实现了 `Floyd_invariant_general_ext` 引理，用于解决 Hoare 逻辑中的前置条件/后置条件统一问题。
3.  **逻辑简化**：尝试简化 `Floyd_k_correct` 证明中 `v = j` 分支的逻辑，利用 `Floyd_invariant_general_ext` 规避了部分复杂的路径构造。

## 3. 待补充完善的证明（协作指南）

### 3.1 修复 `min_dist_invalid_u` (优先)
- **位置**: `Floyd.v` 第 1284 行左右。
- **问题**：`contradiction` 策略失败。
- **原因**：虽然 `head_valid` 应该能推导出 `vvalid g u`，从而与假设 `~ vvalid g u` 矛盾，但当前上下文中可能存在命题不匹配（例如 `path_valid` 的定义细节）。
- **任务**：检查 `head_valid` 的确切输出，手动展开并应用反证法。建议检查 `Hvalid` 的类型和内容。

### 3.2 完成 `Floyd_k_correct` 的循环不变量证明
- **位置**: `Floyd.v` 第 1324 行起，特别是第 1530 行附近。
- **问题**：主循环证明尚未完成。
- **任务**：完善 `update_dist` 后状态的正确性证明。需要确保 `d_ij`, `d_ik`, `d_kj` 的值正确传递给递归引理 `min_dist_recur`。需要构造旧状态（`done` 集合）下的最短路径假设。

### 3.3 完成 `Hzero` 引理
- **任务**：证明对于任意顶点 `v`，`min_weight_distance_in_vset g v v S (Some 0)` 成立。
- **难点**：需要处理空路径的情况，证明自环距离为 0。

### 3.4 `min_weight_distance_in_vset` 的空路径处理
- **任务**：确保最短路径定义能正确涵盖长度为 0 的路径（即 `u=v` 时距离为 0），这是 `Hzero` 成立的前提。
