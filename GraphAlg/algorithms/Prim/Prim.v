Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic path path_basic vpath Zweight.
From GraphLib.undirected Require Import tree.
From MaxMinLib Require Import MaxMin Interface. 
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Prim.

(** Prim算法用于计算无向连通图的最小生成树。
    核心思想是贪心地选择连接"树内顶点"和"树外顶点"的最小权重边。
    
    算法流程：
    1. 初始化：选择一个起始顶点S，将其加入树中
    2. 循环：在所有"切边"（一端在树内，一端在树外）中选择权重最小的边
    3. 将该边和对应的树外顶点加入生成树
    4. 重复直到所有可达顶点都在树中
    
    循环不变量提示：
    - in_tree 包含的顶点通过 mst_edges 构成一棵树
    - mst_edges 是当前 in_tree 上的最小生成树的边集
    - 每次选择的切边满足"安全边"性质
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G)
        {eq_dec: EqDec (V * V) eq}
        {eq_dec_E: EqDec E eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Record St: Type := mkSt_s {
  in_tree: V -> Prop;      (** 当前在生成树中的顶点集合 *)
  mst_edges: list E; (** 当前生成树的边集 *)
}.

Context (src: V)
        (validsrc: vvalid g src).

(** 初始状态：只有源点S在树中，边集为空 *)
Definition initSt: St := {|
  in_tree := [src];
  mst_edges := nil;
|}.

Instance: Settable St := settable! mkSt_s <in_tree; mst_edges>.

(** 切边定义：一端在树内，一端在树外的边 *)
Definition is_cut_edge (s: St) (e: E): Prop :=
  exists u v, step_aux g e u v /\
  (u ∈ s.(in_tree) /\ ~ v ∈ s.(in_tree)).

(** 从所有切边中选择权重最小的边 *)
Definition get_min_cut_edge (f: St -> E -> Prop): program St E :=
  get (fun s e => min_object_of_subset Z_op_le (fun e => is_cut_edge s e) (weight g) e).

Definition add_to_mst_vertex (v: V): program St unit :=
  update' (fun s => s <| in_tree ::= fun t => t ∪ [v] |>).

Definition add_to_mst_edge (e: E): program St unit :=
  update' (fun s => s <| mst_edges ::= fun es => e :: es |>).

(** Prim主算法：循环直到没有切边（所有可达顶点都在树中） *)
Definition Prim: program St unit :=
  while (fun s => exists e, is_cut_edge s e) 
    ( e <- get_min_cut_edge is_cut_edge ;;  (* 选择最小权重的切边 *)
      v <- get (fun s v => exists u, step_aux g e u v /\ u ∈ s.(in_tree) /\ ~ v ∈ s.(in_tree));; (* 获取切边的另一个端点 *)
      add_to_mst_vertex v;;                      (* 将新顶点加入树 *)
      add_to_mst_edge e                   (* 将边加入边集 *)
    ).


(** ===== 辅助定义 ===== *)

(** 边集的总权重 *)
Definition total_weight (s: St): option Z :=
  fold_right (fun e l => Z_op_plus (weight g e) l) (Some 0) s.(mst_edges).


(** ===== 生成树和最小生成树定义 ===== *)

Parameter is_spanning_tree: St -> Prop.

Definition is_mst (s: St): Prop :=
  min_object_of_subset Z_op_le is_spanning_tree total_weight s.

Theorem Prim_correct: 
  Hoare (fun s => s = initSt)
        Prim
        (fun _ s => is_mst s).
Admitted.

End Prim.

