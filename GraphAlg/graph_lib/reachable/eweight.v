Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import GraphLib path vpath path_basic.
From MaxMinLib Require Import MaxMin. 

Class CommMonoid 
    {W: Type} 
    (plus: W -> W -> W) := {
    g_zero: W;

    g_plus: forall a b, plus a b = plus b a;
    g_plus_assoc: forall a b c, plus (plus a b) c = plus a (plus b c);
    g_plus_id: forall a, plus a g_zero = a;
}.

(* 带无穷大的全序关系 *)
Class InfWeight 
    {W: Type} 
    (W_le: W -> W -> Prop)
    (W_plus: W -> W -> W)
    {W_le_totalorder: TotalOrder W_le}
    {W_plus_group: CommMonoid W_plus}
    := 
{
    W_inf: W;

    W_le_inf: forall a, W_le a W_inf;
    W_plus_inf: forall a, W_plus a W_inf = W_inf;
}.


Class EdgeWeight 
    (G E: Type) 
    (W: Type) := {
  weight: G -> E -> W;
}.


Section WEIGHTED. 


Context {G V E: Type} 
        {W: Type}
        {W_le: W -> W -> Prop}
        {W_le_totalorder: TotalOrder W_le}
        {W_plus: W -> W -> W}
        {W_plus_comm_monoid: CommMonoid W_plus}
        {infweight: InfWeight W_le W_plus}
        {P: Type}
        {pg: Graph G V E} 
        {gv: GValid G}
        {ew: EdgeWeight G E W}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}.

Parameter Wlist_sum: list W -> W.

(* 路径的权重和函数 *)
Definition path_weight (g: G) (p: P): W :=
    Wlist_sum (map (weight g) (edge_in_path p)).

(* p是一条从u到v的最短路径 *)
Definition min_weight_path (g: G) (u: V) (v: V) (p: P): Prop :=
    min_object_of_subset W_le (fun p => is_path g p u v) (path_weight g) p.
    
(* z是从u到v的最短距离*)
Definition min_weight_distance (g: G) (u: V) (v: V) (z: W): Prop :=
    min_value_of_subset_with_default W_le (fun p => is_path g p u v) (path_weight g) W_inf z.

(* p是一条从u到v只经过vset的顶点的最短路径 *)
Definition min_weight_path_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (p: P): Prop :=
    min_object_of_subset W_le (fun p => is_path_through_vset g p u v vset) (path_weight g) p.

(* z是从u到v只经过vset的顶点的最短距离 *)
Definition min_weight_distance_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (z: W): Prop :=
    min_value_of_subset_with_default W_le (fun p => is_path_through_vset g p u v vset) (path_weight g) W_inf z.


End WEIGHTED.
