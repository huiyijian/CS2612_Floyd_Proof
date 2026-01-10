Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
Local Open Scope list.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.

(** * 树的基本定义 *)

Class Tree 
    (G V E: Type) 
    {pg: Graph G V E} 
    {gv: GValid G} 
    (A: Type) 
    {path: Path G V E A}:=
{
  tree_connected: forall g, gvalid g -> connected g;
  tree_no_curcuit: forall g, gvalid g -> ~ have_simple_circuit g;
}.


Section TREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {A: Type}
        {path: Path G V E A}
        {emptypath: EmptyPath G V E A path}
        {singlepath: SinglePath G V E A path}
        {concatpath: ConcatPath G V E A path}
        {tree: @Tree G V E pg gv A path}
        {g: G}
        {gvalid: gvalid g}.

Lemma tree_have_path: 
  forall u v,
  vvalid g u ->
  vvalid g v ->
  exists p, valid_epath g u p v.
Proof.
  intros.
  pose proof (tree_connected g gvalid u v H H0).
  unfold reachable in H1; induction_1n H1.
  * exists nil; unfold valid_epath. 
    exists (empty_path v). (split;[|split;[|split]]).
    - apply empty_path_valid.
    - assert (length (edge_in_path (empty_path v)) = 0). {
        pose proof vpath_iff_epath g (empty_path v) (empty_path_valid g v) as [Hl _].
        rewrite empty_path_vertex in Hl; simpl in Hl. 
        lia.
      }
      destruct (edge_in_path (empty_path v)) eqn: Hle; auto. 
      inversion H1.
    - rewrite empty_path_vertex. simpl. auto.
    - rewrite empty_path_vertex. simpl. auto.
  * apply step_vvalid in H2 as ?; destruct H3 as [_ Hu0].
    apply IHrt in H0 as Hp; auto.
    destruct Hp as [p].
    destruct H2 as [e].
    destruct H3 as [p0 [? [? []]]].
    exists (e :: p).
    exists (concat_path (single_path u u0 e) p0). 
    (split;[|split;[|split]]).
    - apply concat_path_valid; auto. 
      apply single_path_valid; auto. 
      assert (Some (path.tail (single_path u u0 e)) = Some (path.head p0)). 
      2: { inversion H7; subst; reflexivity. }
      erewrite head_valid; eauto. 
      erewrite tail_valid. 
      2: { apply single_path_valid; eauto. }
      unfold Positional.tl_error. 
      rewrite single_path_vertex; simpl. 
      rewrite H5; auto. 
    - pose proof concat_path_edge (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_edge. rewrite H4. simpl. auto.
    - pose proof concat_path_vertex (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_vertex. simpl. auto.
    - pose proof concat_path_vertex (single_path u u0 e) p0 as He; rewrite He. 
      rewrite single_path_vertex. 
      destruct ((vertex_in_path p0)) eqn: Heqn; simpl.
      { inversion H5. }
      { simpl in H6. admit. }
Admitted.

Lemma tree_have_simple_path: 
  forall u v,
  vvalid g u ->
  vvalid g v ->
  exists p, simple_epath g u p v.
Proof.
  intros.
  pose proof (tree_have_path u v H H0) as [p Hp].
  eapply path_simplfier; eauto. 
Admitted.


Lemma tree_add_edge_have_simple_circuit: 
  forall g' u v e,
  addEdgeUndirected g g' u v e ->
  exists w p, simple_circuit g' p w.
Proof.
Admitted.

End TREE.


