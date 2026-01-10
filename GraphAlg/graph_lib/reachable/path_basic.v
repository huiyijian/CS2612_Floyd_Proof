
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Arith.
From GraphLib Require Import graph_basic reachable_basic Syntax path.

Import ListNotations.
Import SetsNotation.

Local Open Scope sets.
Local Open Scope list.

Section path.
  
Context {G V E: Type}
        {P: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}. 

Definition is_path (g: G) (p: P) (u v: V): Prop :=
  path_valid g p /\ head p = u /\ tail p = v.

Definition is_empty_path (p: P): Prop :=
  exists v, p = empty_path v.

Definition is_path_through_vset (g: G) (p: P) (u v: V) (vset: V -> Prop): Prop :=
  is_path g p u v /\ 
    forall x, (exists p1 p2, path_valid g p1 /\ path_valid g p2 /\ ~ is_empty_path p1 /\ ~ is_empty_path p2 /\ 
    concat_path p1 p2 = p /\ tail p1 = x) -> x ∈ vset.

Lemma through_empty_vset: forall g u v e,
  step_aux g e u v <->
  is_path_through_vset g (single_path u v e) u v ∅.
Proof.
Admitted.

End path.