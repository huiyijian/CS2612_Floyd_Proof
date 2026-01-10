Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import GraphLib path vpath path_basic.
From MaxMinLib Require Import MaxMin Interface. 

Local Open Scope Z.

Class EdgeWeight 
    (G E: Type):= {
  weight: G -> E -> option Z;
}.


Section WEIGHTED. 


Context {G V E: Type} 
        {P: Type}
        {pg: Graph G V E} 
        {gv: GValid G}
        {ew: EdgeWeight G E}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}.

Definition Zlist_sum: list (option Z) -> option Z :=
    fold_right Z_op_plus (Some 0).

(* 路径的权重和函数 *)
Definition path_weight (g: G) (p: P): option Z :=
    Zlist_sum (map (weight g) (edge_in_path p)).

(* p是一条从u到v的最短路径 *)
Definition min_weight_path (g: G) (u: V) (v: V) (p: P): Prop :=
    min_object_of_subset Z_op_le (fun p => is_path g p u v) (path_weight g) p.
    
(* z是从u到v的最短距离*)
Definition min_weight_distance (g: G) (u: V) (v: V) (z: option Z): Prop :=
    min_value_of_subset_with_default Z_op_le (fun p => is_path g p u v) (path_weight g) None z.

(* p是一条从u到v只经过vset的顶点的最短路径 *)
Definition min_weight_path_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (p: P): Prop :=
    min_object_of_subset Z_op_le (fun p => is_path_through_vset g p u v vset) (path_weight g) p.

(* z是从u到v只经过vset的顶点的最短距离 *)
Definition min_weight_distance_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (z: option Z): Prop :=
    min_value_of_subset_with_default Z_op_le (fun p => is_path_through_vset g p u v vset) (path_weight g) None z.


End WEIGHTED.
