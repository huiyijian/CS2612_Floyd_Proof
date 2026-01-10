Require Import Coq.Lists.List.
Section graph_basic.

Class Graph (G V E: Type) := {
  vvalid : G -> V -> Prop;
  evalid : G -> E -> Prop;
  step_aux : G -> E -> V -> V -> Prop;
}.

Class GValid (G: Type) :=
  gvalid : G -> Prop.

Class StepValid (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_vvalid1: forall g e x y, step_aux g e x y -> vvalid g x ;
  step_vvalid2: forall g e x y, step_aux g e x y -> vvalid g y ;
  step_evalid: forall g e x y, step_aux g e x y -> evalid g e ;
}.

Class NoEmptyEdge (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_empty_edge: forall g e, gvalid g -> evalid g e -> exists x y, step_aux g e x y ;
}.

Class UndirectedGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G}:= {
  step_sym: forall g e x y, step_aux g e x y -> step_aux g e y x;
}.

Class StepUniqueDirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  step_aux_unique: forall g e x1 y1 x2 y2, gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  x1 = x2 /\ y1 = y2;
}.

Class StepUniqueUndirected (G V E: Type) `{pg: Graph G V E} `{gv: GValid G}:= {
  step_aux_unique_undirected: forall g e x1 y1 x2 y2, gvalid g -> step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1);
}.

Class SimpleGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  no_multiple_edge: forall g e1 e2 x y, gvalid g -> step_aux g e1 x y -> step_aux g e2 x y -> e1 = e2;
  no_self_loop: forall g e x, gvalid g -> ~ step_aux g e x x;
}.

Class FiniteGraph (G V E: Type) `{pg: Graph G V E} `{gv: GValid G} := {
  listV: G -> list V;
  finite_vertices: forall g, gvalid g -> forall v, vvalid g v -> In v (listV g);
}.

End graph_basic.

