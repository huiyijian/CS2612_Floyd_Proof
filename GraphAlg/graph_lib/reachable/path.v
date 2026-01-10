Require Import SetsClass.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Arith.Arith.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic reachable_basic Syntax.

Import ListNotations.

Record vpath_iff_epath_prop 
    {G V E: Type} 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (pv: list V) 
    (pe: list E): Prop := {
    vpath_iff_epath_length: length pv = length pe + 1;
    vpath_iff_epath_step: 
        forall g n u v e, 0 <= n < length pe -> 
            nth_error pe n = Some e ->
            nth_error pv n = Some u ->
            nth_error pv (S n) = Some v ->
            step_aux g e u v;
}.

Class Path 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) := {
    path_valid: 
        G -> P -> Prop; 
    vertex_in_path: 
        P -> list V;
    head: 
        P -> V;
    head_valid: 
        forall g p, path_valid g p -> 
            Some (head p) = hd_error (vertex_in_path p);
    tail: 
        P -> V;
    tail_valid: 
        forall g p, path_valid g p -> 
            Some (tail p) = tl_error (vertex_in_path p);
    edge_in_path: 
        P -> list E;
    vpath_iff_epath: 
        forall g p, path_valid g p -> 
            vpath_iff_epath_prop (vertex_in_path p) (edge_in_path p);
}.

Class EmptyPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    empty_path: V -> P;
    empty_path_valid: forall g v, path_valid g (empty_path v);
    empty_path_vertex: forall v, vertex_in_path (empty_path v) = [v];
}.

Class SinglePath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    single_path: V -> V -> E -> P;
    single_path_valid: forall g u v e, step_aux g e u v -> path_valid g (single_path u v e);
    single_path_vertex: forall u v e, vertex_in_path (single_path u v e) = [u; v];
    single_path_edge: forall u v e, edge_in_path (single_path u v e) = [e];
}.

Class ConcatPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) := {
    concat_path: P -> P -> P;

    concat_path_valid: forall g a1 a2, 
    path_valid g a1 -> path_valid g a2 -> 
    tail a1 = head a2 -> 
    path_valid g (concat_path a1 a2);

    concat_path_vertex: forall a1 a2, vertex_in_path (concat_path a1 a2) = vertex_in_path a1 ++ (skipn 1 (vertex_in_path a2));

    concat_path_edge: forall a1 a2, edge_in_path (concat_path a1 a2) = edge_in_path a1 ++ edge_in_path a2;
}.

Inductive path_destruct_1n {P E V: Type} :=
| DestructBase1n (v: V)               
| DestructStep1n (p: P) (u v: V) (e: E). 

Class Destruct1nPath 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p):= {
    destruct_1n_path: P -> path_destruct_1n;
    destruct_1n_spec: forall g p, path_valid g p ->
        match destruct_1n_path p with
        | DestructBase1n v => 
            p = empty_path v
        | DestructStep1n p' u v e =>
              path_valid g p' /\
              head p' = v /\
              step_aux g e u v /\
              p = concat_path (single_path u v e) p'
        end;
}.

Inductive path_destruct_n1 {P E V: Type} :=
| DestructBasen1 (p: P) (v: V)
| DestructStepn1 (p: P) (u v: V) (e: E).

Class Destructn1Path 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    destruct_n1_path: P -> path_destruct_n1;
    destruct_n1_spec: forall g p, path_valid g p ->
        match destruct_n1_path p with
        | DestructBasen1 p' v =>
            p = empty_path v
        | DestructStepn1 p' u v e =>
            path_valid g p' /\
            tail p' = u /\
            step_aux g e u v /\
            p = concat_path p' (single_path u v e)
        end;
}.
Print list_ind.
Print list_rec.
(* Type -> Prop ? *)
Class PathInd1n 
    (G V E: Type) 
    `{pg: Graph G V E} 
    `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    path_ind1n: forall g (X: P -> Type) 
    (H1: forall v, X (empty_path v)) 
    (H2: forall u v e a2, 
    step_aux g e u v -> 
    path_valid g a2 ->
    head a2 = v ->
    X a2 -> 
    X (concat_path (single_path u v e) a2)), 
    forall a, path_valid g a -> X a;
}.

Class PathIndn1 (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} 
    (P: Type) 
    (p: Path G V E P) 
    (ep: EmptyPath G V E P p) 
    (sp: SinglePath G V E P p) 
    (cp: ConcatPath G V E P p) := {
    path_indn1: forall g (X: P -> Type) 
    (H1: forall v, X (empty_path v)) 
    (H2: forall u v e a1, step_aux g e u v -> 
    path_valid g a1 ->
    tail a1 = u ->
    X a1 -> 
    X (concat_path a1 (single_path u v e))), 
    forall a, path_valid g a -> X a;
}.
