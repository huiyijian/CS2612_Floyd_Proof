Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted path path_basic vpath Zweight.
From GraphLib.undirected Require Import tree.
From MaxMinLib Require Import MaxMin Interface. 
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.

Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope Z.

Section Kruskal.

(** Kruskal算法用于计算无向连通图的最小生成树。
    核心思想是按边权重从小到大排序，贪心地选择不会形成环的边。
    
    算法流程：
    1. 初始化：边集为空，每个顶点自成一个连通分量
    2. 循环：在所有未处理的边中，选择权重最小且不会形成环的边
    3. 将该边加入生成树
    4. 重复直到边数达到 |V|-1 或没有可选边
    
    循环不变量提示：
    - mst_edges 构成一个森林（无环）
    - mst_edges 的权重之和不超过任何其他可行方案
    - 选择的边满足"安全边"性质
*)

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G)
        {eq_dec: EqDec E eq}
        {eq_dec_E: EqDec E eq}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Record St: Type := mkSt {
  mst_edges: list E;  (** 当前选中的边集 *)
}.

(** 初始状态：边集为空 *)
Definition initSt: St := {| mst_edges := nil |}.

Instance: Settable St := settable! mkSt <mst_edges>.

(** 将边e加入生成树边集 *)
Definition add_edge_to_mst (e: E): program St unit :=
  update' (fun s => s <| mst_edges ::= fun es => e :: es |>).


Definition forms_cycle (s: St) (e: E): Prop :=
  forall u v, step_aux g e u v -> 
    reachable_in_eset g (fun e => In e s.(mst_edges)) u v.

(** 从所有有效且不形成环的边中选择权重最小的 *)
Definition get_min_edge (f: St -> E -> Prop): program St E :=
  get (fun s e => min_object_of_subset Z_op_le (fun e => f s e) (weight g) e).

(** 可选边：有效边且不形成环 *)
Definition selectable_edge (s: St) (e: E): Prop :=
  evalid g e /\ ~ forms_cycle s e.

(** Kruskal主算法：循环直到没有可选边 *)
Definition Kruskal: program St unit :=
  while (fun s => exists e, selectable_edge s e)
    (e <- get_min_edge selectable_edge;;  (* 选择最小权重的可选边 *)
      add_edge_to_mst e                    (* 将边加入边集 *)
    ).


(** ===== 更多辅助定义 ===== *)

(** ===== 辅助定义 ===== *)

(** 边集的总权重 *)
Definition total_weight (s: St): option Z :=
  fold_right (fun e l => Z_op_plus (weight g e) l) (Some 0) s.(mst_edges).


(** ===== 生成树和最小生成树定义 ===== *)

Parameter is_spanning_tree: St -> Prop.

Definition is_mst (s: St): Prop :=
  min_object_of_subset Z_op_le is_spanning_tree total_weight s.
  
Theorem Kruskal_correct: 
  Hoare (fun s => s = initSt)
        Kruskal
        (fun _ s => is_mst s).
Admitted.

End Kruskal.