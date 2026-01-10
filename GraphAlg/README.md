# 图论算法形式化验证大作业

这是课程的大作业说明，旨在让学生使用Coq定理证明器完成四个经典图论算法的正确性证明。

## 项目概述

本作业要求学生证明以下四个经典图论算法的正确性：

| 算法 | 描述 | 证明目标 |
|------|------|----------|
| **Dijkstra** | 单源最短路径算法 | 证明算法终止时，`dist`数组正确记录从源点到所有可达顶点的最短距离 |
| **Floyd** | 全源最短路径算法 | 证明算法终止时，`dist`矩阵正确记录任意两点间的最短距离 |
| **Prim** | 最小生成树算法 | 证明算法终止时，`mst_edges`构成原图的最小生成树 |
| **Kruskal** | 最小生成树算法 | 证明算法终止时，`mst_edges`构成原图的最小生成树 |

## 项目结构

```
.
├── algorithms/           # 算法证明目标（学生需完成的部分）
│   ├── Dijkstra/         # Dijkstra算法
│   ├── Floyd/            # Floyd算法  
│   ├── Prim/             # Prim算法
│   ├── Kruskal/          # Kruskal算法
│   └── makefile
│
├── monadlib/             # Monad程序库
│   ├── StateRelMonad/    # 状态关系Monad（主要使用）
│   ├── SetMonad/         # 集合Monad
│   └── MonadErr/         # 带错误处理的Monad
│
├── graph_lib/            # 图论基础库
│   ├── graph_basic.v     # 图的基本定义
│   ├── reachable/        # 可达性相关定义与性质
│   ├── directed/         # 有向图相关
│   ├── undirected/       # 无向图相关
│   ├── subgraph/         # 子图相关
│   └── examples/         # 算法相关的辅助定义
│
├── ListLib/              # 列表操作库
│
├── extremumlib/          # 最值库
│   ├── MaxMin.v          # 最大最小值定义
│   ├── Nat/              # 自然数最值
│   └── Z/                # 整数最值
│
├── coq-record-update/    # 记录更新语法糖库
├── sets/                 # 集合论库
└── fixedpoints/          # 不动点理论库
```

## 核心库介绍

### MonadLib - Monad程序库

提供基于状态关系Monad的程序语义框架，用于自然地描述和验证算法。

**主要操作符：**
- `ret a` - 返回值a，不改变状态
- `x <- m;; f x` - 顺序组合（bind）
- `assume P` / `assume!! P` - 条件假设
- `choice m1 m2` - 非确定性选择
- `while cond body` - 循环结构
- `list_iter l f` - 列表迭代
- `update'` - 状态更新

**Hoare逻辑：**
```coq
Hoare P c Q  (* 前条件P，程序c，后条件Q *)
```

**常用策略：**
- `hoare_bind H` - 使用H作为中间断言
- `hoare_step` - 单步推进
- `hoare_auto` - 自动推进

### GraphLib - 图论库

提供图的基本定义和可达性相关性质。

**主要定义：**
- `vvalid g v` - 顶点有效性
- `evalid g e` - 边有效性
- `step g u v` - 单步可达
- `reachable g u v` - 可达关系
- `min_weight_distance weight g u v n` - 最短距离

### ListLib - 列表库

提供列表操作的常用性质，如`In`、`nth`、`length`等操作的引理。

### ExtremumLib - 最值库

提供最值相关定义和性质。

**主要定义：**
- `min_object_of_subset` - 子集中的最小元素

### coq-record-update - 记录更新库

提供简洁的状态更新语法：
```coq
s <| field ::= fun x => new_value |>
```

## 证明目标详解

### Dijkstra算法

需要证明算法的**正确性**，包含四个子目标：

1. **distance_reachable_soundness**: 若`dist v = Some n`，则`n`是从源点到`v`的最短距离
2. **distance_reachable_completeness**: 若存在最短距离`n`，则`dist v = Some n`
3. **distance_unreachable_soundness**: 若`v`不可达，则`dist v = None`
4. **distance_unreachable_completeness**: 若`dist v = None`，则`v`不可达

### Floyd算法

类似Dijkstra，但针对所有顶点对：

1. **distance_reachable_soundness/completeness**: 任意两点间最短距离的正确性
2. **distance_unreachable_soundness/completeness**: 不可达情况的正确性

### Prim算法 & Kruskal算法

需要证明算法产生的边集`mst_edges`满足`is_mst`条件（即构成最小生成树）。

## 环境要求

- **Coq 8.20.1**
- 依赖库已包含在项目中

## 编译说明

直接在根目录下
```bash
make depend
make
```

## 作业提交要求

1. 将`algorithms/`目录下各算法文件中的`Admitted.`替换为完整证明
2. 确保所有文件能够通过`coqc`编译
3. 按照课程要求格式提交

## 提示

1. 仔细阅读各库的源代码，理解提供的定义和引理
2. 善用`Search`命令查找可用的引理
3. 使用`Print`查看定义的展开形式
4. 循环不变式是证明的关键，需要仔细设计

---

