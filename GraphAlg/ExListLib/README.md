# ExListLib - 扩展列表库

本库在`ListLib`基础上提供扩展功能，包括整数索引列表操作、排列操作、前后缀匹配、排序算法等高级列表处理工具。

## 文件结构

```
ExListLib/
├── ZList.v         # 整数索引列表操作
├── Nperm.v         # 自然数排列
├── Presuffix.v     # 前后缀与部分匹配
├── Sorting.v       # 排序算法
└── InvertalList.v  # 区间列表
```

## 模块说明

### ZList.v - 整数索引列表操作

提供基于整数（`Z`类型）索引的列表操作，更符合算法实现的习惯。

#### 主要定义

**整数序列：**
- `Zseq start len`: 生成从`start`开始，长度为`len`的整数序列
  - 示例：`Zseq 3 4 = [3; 4; 5; 6]`

**整数索引访问：**
- `Znth n l a0`: 用整数`n`索引列表`l`，默认值`a0`
  - 定义：`nth (Z.to_nat n) l a0`

**整数索引更新：**
- `replace_nth n a l`: 替换列表第`n`个位置为`a`
- `replace_Znth n a l`: 用整数索引替换元素
  - 定义：`replace_nth (Z.to_nat n) a l`

**整数范围子列表：**
- `Zsublist lo hi l`: 提取区间`[lo, hi)`的子列表
  - 定义：`skipn (Z.to_nat lo) (firstn (Z.to_nat hi) l)`

**长度操作：**
- `Zlength l`: 列表长度（返回`Z`类型）
  - 来自标准库，等价于`Z.of_nat (length l)`

**求和：**
- `sum l`: 整数列表求和

#### 核心引理

**Zseq性质：**
- `Zseq_length`: 长度性质
- `Zseq_nth`: 第n个元素等于`start + n`
- `Zseq_app`: 序列拼接
- `Zseq_firstn`/`Zseq_skipn`: 与firstn/skipn的交互

**Znth性质：**
- `Znth0_cons`: 列表头部访问
- `Znth_cons`: cons后访问
- `app_Znth1`/`app_Znth2`: 拼接列表的访问
- `Znth_indep`: 索引在范围内时，默认值无关
- `Znth_Zsublist`: 子列表的索引访问

**replace_Znth性质：**
- `replace_Znth_cons`: 对cons列表的替换
- `replace_Znth_app_l`/`replace_Znth_app_r`: 拼接列表的替换
- `replace_Znth_Znth`: 替换为原值则不变
- `replace_Znth_nothing`: 超出范围的替换无效

**Zsublist性质：**
- `Zsublist_single`: 单元素子列表
- `Zsublist_split`: 子列表分割
- `Zsublist_split_app_l`/`Zsublist_split_app_r`: 拼接列表的子列表
- `Zlength_Zsublist`: 子列表长度
- `Zsublist_self`: 完整列表
- `Zsublist_nil`: 空子列表
- `Zsublist_Zsublist`: 嵌套子列表

**Zlength性质：**
- `Zlength_nonneg`: 长度非负
- `Zlength_app`: 拼接列表的长度
- `Zlength_cons`: cons列表的长度

**sum性质：**
- `sum_app`: 拼接列表的求和
- `sum_bound`: 有界元素的求和上界
- `sum_bound_lt`: 严格有界元素的求和上界

**列表相等：**
- `list_eq_ext`: 列表相等的充要条件（长度相等且逐元素相等）

### Nperm.v - 自然数排列

提供排列（permutation）的定义和操作，用于列表元素的重排。

#### 主要定义

**排列定义：**
- `nperm s`: `s`是`[0, 1, ..., length s - 1]`的一个排列
  - 定义：`Permutation (seq 0 (length s)) s`

**应用排列：**
- `apply_perm s l d`: 按排列`s`重排列表`l`
  - 定义：`map (fun n => nth n l d) s`

**恒等排列：**
- `identity_perm n`: 恒等排列`[0, 1, ..., n-1]`
  - 定义：`seq 0 n`

**逆排列：**
- `find_index l n`: 在列表`l`中查找`n`的位置
- `inverse_nperm s`: 排列`s`的逆排列

**特殊排列：**
- `swap_seq n1 n2`: 交换两段的排列
- `swap_seq2 n1 n2 n3`: 交换两个元素的排列

#### 核心引理

**基本性质：**
- `nperm_NoDup`: 排列无重复元素
- `nperm_range`: 排列中的元素都在有效范围内
- `identity_perm_is_is_nperm`: 恒等排列确实是排列
- `identity_perm_refl`: 恒等排列不改变列表

**查找与逆排列：**
- `find_index_nth`: 查找第n个元素的位置返回n
- `nth_find_index`: 查找元素在其位置处确实是该元素
- `inverse_nperm_nperm`: 逆排列也是排列

**应用排列性质：**
- `length_apply_perm`: 应用排列不改变长度
- `map_apply_perm`: map与apply_perm可交换
- `apply_perm_inverse_l`/`apply_perm_inverse_r`: 排列与逆排列互逆
- `apply_perm_is_permutation`: 应用排列得到原列表的排列

**Forall2保持：**
- `Forall2_nperm_congr`: `Forall2`在排列下保持
- `Forall2_nperm_congr_iff`: `Forall2`在排列下的等价性

**特殊排列：**
- `swap_seq2_is_nperm`: swap_seq2是有效排列
- `swap_nperm_apply_perm`: 交换两个元素的效果
- `swap_seq_is_nperm`: swap_seq是有效排列
- `swap_seq_apply_perm`: 交换两段的效果

### Presuffix.v - 前后缀与部分匹配

提供前后缀（既是前缀又是后缀）和部分匹配的定义，主要用于字符串匹配算法（如KMP）。

#### 主要定义

**前后缀：**
- `presuffix l1 l2`: `l1`既是`l2`的前缀又是后缀
- `proper_presuffix l1 l2`: `l1`是`l2`的真前后缀（长度严格小于）

**部分匹配：**
- `partial_match_res patn text res`: `res`是模式串`patn`的前缀且是文本串`text`的后缀
- `partial_bound_res patn text bound`: `bound`对所有部分匹配结果的长度给出上界

**最大前后缀：**
- `presuffix_bound l1 l2`: `l1`包含`l2`的所有真前后缀
- `max_proper_presuffix l1 l2`: `l1`是`l2`的最大真前后缀

#### 核心引理

**基本性质：**
- `prefix_snoc`: 追加元素后的前缀关系
- `sublist_snor`: 追加元素后的子列表关系
- `is_suffix_snoc_snoc_iff`: 后缀追加元素的等价条件

**长度关系：**
- `prefix_length`/`suffix_length`/`presuffix_length`: 前缀/后缀/前后缀的长度约束

**等价刻画：**
- `prefix_iff`: 前缀的逐点等价定义
- `suffix_iff`: 后缀的逐点等价定义
- `is_prefix_snoc_iff`: 追加元素后的前缀等价条件

**传递性：**
- `prefix_trans`/`suffix_trans`/`presuffix_trans`: 前缀/后缀/前后缀的传递性

**全序性：**
- `prefix_total_order`: 同一列表的前缀构成全序
- `suffix_total_order`: 同一列表的后缀构成全序
- `partial_match_total_order`: 部分匹配结果的全序性

**部分匹配：**
- `partial_match_iff`: 部分匹配的等价刻画
- `partial_match_snoc_iff`: 追加字符后的部分匹配条件
- `partial_match_nil`: 空串是部分匹配结果
- `presuffix_partial_match`: 前后缀保持部分匹配

**与位置定义的关系：**
- `prefix_iff_sublist`/`suffix_iff_sublist`: 与子列表的关系
- `prefix_app_iff`/`suffix_app_iff`: 与列表拼接的关系
- `prefix_sublist_iff`/`suffix_sublist_cons_iff`: 与子列表操作的关系

**特殊情况：**
- `nil_prefix`/`nil_suffix`/`nil_presuffix`: 空列表性质
- `presuffix_nil_iff`: 前后缀为空的等价条件

### Sorting.v - 排序算法

实现插入排序算法及其正确性证明。

#### 主要定义

**插入排序：**
- `insert i l`: 将元素`i`插入有序列表`l`
- `sort l`: 对列表`l`排序

#### 核心引理

- `insert_perm`: 插入操作保持排列关系
- `sort_perm`: 排序结果是原列表的排列

### InvertalList.v - 区间列表

定义并研究元素间隔满足特定条件的列表，主要用于散列表分析。

#### 主要定义

**区间列表：**
- `interval_list pace lo hi l`: 列表`l`中元素取值范围`[lo, hi]`，相邻元素间隔至少为`pace`

**递增列表：**
- `Zincreasing l`: 列表`l`单调递增

**整数排序：**
- `Zinsert i l`: 将整数`i`插入有序整数列表
- `Zsort l`: 整数列表排序

#### 核心引理

**interval_list性质：**
- `interval_list_bounded_lt`: 区间列表元素有界
- `interval_list_NoDup`: 区间列表无重复
- `interval_perm_keep`: 排列保持区间列表性质
- `interval_list_compress`: 收缩区间保持性质
- `interval_list_range`: 区间列表的长度上界

**排序相关：**
- `Zinsert_In`: 插入后的成员关系
- `Zsort_Zincreasing`: 排序结果单调递增
- `Zinsert_perm`/`Zsort_perm`: 排序保持排列关系

**递增列表与区间列表：**
- `increasing_interval_list_range`: 递增区间列表的范围约束

## 使用示例

```coq
Require Import ExListLib.ZList.
Require Import ExListLib.Nperm.

(* 整数索引访问 *)
Example Znth_example:
  Znth 2 [10; 20; 30; 40] 0 = 30.
Proof. reflexivity. Qed.

(* 整数子列表 *)
Example Zsublist_example:
  Zsublist 1 3 [10; 20; 30; 40] = [20; 30].
Proof. reflexivity. Qed.

(* 应用排列 *)
Example apply_perm_example:
  apply_perm [2; 0; 1] [10; 20; 30] 0 = [30; 10; 20].
Proof. reflexivity. Qed.
```

## 依赖关系

- **标准库**: `Coq.Lists.List`, `Coq.ZArith.ZArith`, `Coq.Sorting.Permutation`
- **项目依赖**: `ListLib` (Core, Positional, Basics)

## 常用引理索引

### 整数索引列表（ZList）
- 访问：`Znth`, `app_Znth1`, `app_Znth2`
- 更新：`replace_Znth`, `replace_Znth_app_l`
- 子列表：`Zsublist`, `Zsublist_split`, `Znth_Zsublist`
- 长度：`Zlength`, `Zlength_app`
- 相等：`list_eq_ext`

### 排列（Nperm）
- 定义：`nperm`, `identity_perm`
- 应用：`apply_perm`, `apply_perm_inverse_l`
- 逆排列：`inverse_nperm`, `find_index`
- 性质：`nperm_NoDup`, `apply_perm_is_permutation`

### 前后缀（Presuffix）
- 定义：`presuffix`, `partial_match_res`
- 传递性：`prefix_trans`, `suffix_trans`
- 等价刻画：`prefix_iff`, `suffix_iff`
- 全序性：`prefix_total_order`, `partial_match_total_order`

### 排序（Sorting）
- 排序：`sort`, `insert`
- 正确性：`sort_perm`, `insert_perm`

### 区间列表（InvertalList）
- 定义：`interval_list`, `Zincreasing`
- 性质：`interval_list_NoDup`, `interval_list_range`
- 排序：`Zsort`, `Zsort_perm`, `Zsort_Zincreasing`

---

*该库是CS2205图论算法验证项目的扩展组件，可以不使用；提供高级列表处理功能*

