Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.epath.
Require Import SetsClass.
(* g1 is the subgraph of g2 *)
Definition subgraph 
  {G1 G2 V E: Type} 
  {pg1: Graph G1 V E} 
  {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) : Prop :=
  (forall x y e, step_aux g1 e x y -> step_aux g2 e x y).

Record subgraph_vertex_eq
  {G1 G2 V E: Type} 
  {pg1: Graph G1 V E} 
  {pg2: Graph G2 V E} 
  (g1: G1) (g2: G2) : Prop := {
  subgraph_vertex: forall x, vvalid g1 x <-> vvalid g2 x;
  subgraph_step_aux: forall x y e, step_aux g1 e x y -> step_aux g2 e x y;
  }.
(*add an edge into directed graph g1*)
Record addEdgeDirected {G V E: Type} {pg1: Graph G V E} {pg2: Graph G V E} 
  (g1: G) (g2: G) (u v: V) (e: E): Prop := {
  addEdge_directed_premise: vvalid g1 u /\ vvalid g1 v /\ ~ evalid g1 e;
  addEdge_directed_vvalid: forall x, vvalid g2 x <-> vvalid g1 x;
  addEdge_directed_evalid: forall a, evalid g2 a <-> evalid g1 a \/ a = e;
  addEdge_directed_step_aux: forall x y a, step_aux g2 a x y <-> step_aux g1 a x y \/ (x = u /\ y = v /\ a = e);
}.

(*add an edge into undirected graph g1*)
Record addEdgeUndirected {G V E: Type} {pg1: Graph G V E} {pg2: Graph G V E} 
  (g1: G) (g2: G) (u v: V) (e: E): Prop := {
  addEdge_undirected_premise: vvalid g1 u /\ vvalid g1 v /\ ~ evalid g1 e;
  addEdge_undirected_vvalid: forall x, vvalid g2 x <-> vvalid g1 x;
  addEdge_undirected_evalid: forall a, evalid g2 a <-> evalid g1 a \/ a = e;
  addEdge_undirected_step_aux: forall x y a, step_aux g2 a x y <-> step_aux g1 a x y \/ (x = u /\ y = v /\ a = e) \/ (x = v /\ y = u /\ a = e);
}.
(*delete an edge from g1*)
Record deleteEdge {G V E: Type} {pg1: Graph G V E} {pg2: Graph G V E} 
  (g1: G) (g2: G) (u v: V) (e: E): Prop := 
{
  deleteEdge_premise: step_aux g1 e u v;
  deleteEdge_vvalid: forall x, vvalid g2 x <-> vvalid g1 x;
  deleteEdge_evalid: forall a, evalid g2 a <-> evalid g1 a /\ a <> e;
  deleteEdge_step_aux: forall x y a, step_aux g2 a x y <-> step_aux g1 a x y /\ a <> e;
}.

Section SUBGRAGH.

Context {G1 G2 V E: Type}
        {graph1: Graph G1 V E}
        {graph2: Graph G2 V E}
        {gvalid1: GValid G1}
        {gvalid2: GValid G2}
        {stepvalid1: StepValid G1 V E}
        {stepvalid2: StepValid G2 V E}
        (g1: G1)
        (g2: G2)
        {g_valid1: @gvalid G1 gvalid1 g1}
        {g_valid2: @gvalid G2 gvalid2 g2}
        (sub: subgraph g1 g2).

Lemma sub_step': forall x y,
  step g1 x y -> 
  step g2 x y.
Proof.
  intros.
  destruct H as [e ?].
  apply sub in H.
  exists e; auto.
Qed.

Lemma sub_reachable: forall x y, 
  reachable g1 x y -> 
  reachable g2 x y.
Proof.
  intros. 
  unfold reachable in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_rt. 
    destruct H0 as [e ?].
    apply sub in H0.
    exists e; auto.
Qed.

Lemma sub_reachable_tl(P: V -> Prop): 
  forall x y, 
  reachable_tl P g1 x y -> reachable_tl P g2 x y.
Proof.
  intros.
  unfold reachable_tl in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_tl_rt; auto.
    destruct H0 as [H0 ?]. 
    split; auto.
    destruct H0 as [e0 H0].
    apply sub in H0.
    exists e0; auto.
Qed.

Lemma sub_reachable_without: forall e x y, 
  reachable_without g1 e x y -> 
  reachable_without g2 e x y.
Proof.
  intros.
  unfold reachable_without in *.
  induction_1n H.
  - reflexivity.
  - transitivity x0; auto.
    apply step_without_rt; auto.
    destruct H0 as [e0 [? ?]].
    exists e0; split; auto.
Qed.

Lemma sub_reverse {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall x y e, 
    step_aux g2 e x y -> 
    evalid g1 e ->
    step_aux g1 e x y \/ step_aux g1 e y x.
Proof.
  intros.
  apply no_empty_edge in H0; auto.
  destruct H0 as [a [b ?]].
  apply sub in H0 as H1.
  eapply step_aux_unique_undirected in H as Heq; eauto.
  destruct Heq as [Heq | Heq]; destruct Heq; subst; tauto.
Qed.

Lemma evalid_sub_vvalid1
  {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall u v e,
    step_aux g2 e u v ->
    evalid g1 e ->
    vvalid g1 v.
Proof.
  intros.
  eapply sub_reverse in H0 as []; eauto;
  [eapply step_vvalid2 | eapply step_vvalid1]; eauto.
Qed.

Lemma evalid_sub_vvalid2
  {no_empty_edge1: NoEmptyEdge G1 V E}
  {step_aux_unique_undirected2: StepUniqueUndirected G2 V E}: 
  forall u v e,
    step_aux g2 e u v ->
    evalid g1 e ->
    vvalid g1 u.
Proof.
  intros.
  eapply sub_reverse in H0 as []; eauto;
  [eapply step_vvalid1 | eapply step_vvalid2]; eauto.
Qed.
    
End SUBGRAGH.



(* Require Export Coq.Classes.EquivDec.

Section GRAPH_OPERATIONS.

Context {G V E: Type}
        {graph: Graph G V E}
        {gvalid: GValid G}
        {stepvalid: StepValid G V E}
        (g1: G)
        (g2: G)
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}
        {eq_dec: EqDec E eq}.

Lemma addEdge_directed_path: forall u v e p x y,
  addEdgeDirected g1 g2 u v e ->
  valid_epath g1 p x y ->
  valid_epath g2 p x y.
Proof.
  induction p; intros.
  * simpl in *; auto.
  * simpl in *; destruct H0 as [w [H1 H2]]. 
    exists w; split; auto.
    apply H; left; auto.
Qed.

Lemma addEdge_undirected_path: forall u v e p x y,
  addEdgeUndirected g1 g2 u v e ->
  valid_epath g1 p x y ->
  valid_epath g2 p x y.
Proof.
  induction p; intros.
  * simpl in *; auto.
  * simpl in *; destruct H0 as [w [H1 H2]]. 
    exists w; split; auto.
    apply H; left; auto.
Qed.

Lemma addEdge_deleteEdge
  {step_aux_unique_directed: StepUniqueDirected G V E}: 
  forall u v e,
  addEdgeDirected g1 g2 u v e <->
  deleteEdge g2 g1 u v e.
Proof.
  intros; split; intros [].
  * split. 
    ** apply addEdge_directed_step_aux0; right; auto.
    ** intros; split; apply addEdge_directed_vvalid0.
    ** intros; split; intros. 
       { split. 
         apply addEdge_directed_evalid0; left; auto. 
         unfold not; intros; subst; tauto. }
       { destruct H. 
         apply addEdge_directed_evalid0 in H as []; auto; congruence. }
    ** intros; split; intros. 
       { split.
         apply addEdge_directed_step_aux0; left; auto.
         unfold not; intros; subst. 
         apply step_evalid in H. tauto. }
       { destruct H. 
         apply addEdge_directed_step_aux0 in H as []; auto. 
         destruct H as [? []]; subst; congruence. }
  * split. 
    ** split; [|split]. 
       { apply deleteEdge_vvalid0; eapply step_vvalid1; eauto. }
       { apply deleteEdge_vvalid0; eapply step_vvalid2; eauto. } 
       { unfold not; intros. apply deleteEdge_evalid0 in H as []; tauto.  }
    ** intros; split; apply deleteEdge_vvalid0.
    ** intros; split; intros. 
       { destruct (eq_dec a e); subst. 
         right; tauto.
         left; apply deleteEdge_evalid0; split; tauto. }
       { destruct H. 
         apply deleteEdge_evalid0; auto.
         subst; eapply step_evalid; eauto. }
    ** intros; split; intros. 
       { destruct (eq_dec e a); subst.
         * assert (e = a) by tauto; subst. 
           eapply step_aux_unique in deleteEdge_premise0 as []; eauto.
         * assert (e <> a) by tauto. 
           left; apply deleteEdge_step_aux0; split; auto. }
       { destruct H. 
         * apply deleteEdge_step_aux0; auto.
         * destruct H as [? []]; subst; congruence. }
Qed.

Lemma addEdge_undirected_deleteEdge
  {undirected: UndirectedGraph G V E}
  {step_aux_unique_undirected: StepUniqueUndirected G V E}: 
  forall u v e,
  addEdgeUndirected g1 g2 u v e <->
  deleteEdge g2 g1 u v e.
Proof.
  intros; split; intros [].
  * split. 
    ** apply addEdge_undirected_step_aux0; right; auto.
    ** intros; split; apply addEdge_undirected_vvalid0.
    ** intros; split; intros. 
       { split.
         apply addEdge_undirected_evalid0; left; auto.
         unfold not; intros; subst; tauto. }
       { destruct H. 
         apply addEdge_undirected_evalid0 in H as []; auto; congruence. }
    ** intros; split; intros. 
       { split.
         apply addEdge_undirected_step_aux0; left; auto.
         unfold not; intros; subst. 
         apply step_evalid in H. tauto. }
       { destruct H. 
         apply addEdge_undirected_step_aux0 in H as []; auto. 
         destruct H as [[? []]|[? []]]; subst; congruence. }
  * split. 
    ** split; [|split]. 
       { apply deleteEdge_vvalid0; eapply step_vvalid1; eauto. }
       { apply deleteEdge_vvalid0; eapply step_vvalid2; eauto. } 
       { unfold not; intros. apply deleteEdge_evalid0 in H as []; tauto.  }
    ** intros; split; apply deleteEdge_vvalid0.
    ** intros; split; intros. 
       { destruct (eq_dec a e); subst.
         * assert (a = e) by tauto; subst.
           eapply step_aux_unique_undirected in deleteEdge_premise0 as []; eauto.
         * assert (a <> e) by tauto.
           left; apply deleteEdge_evalid0; split; auto. }
       { destruct H. 
         * apply deleteEdge_evalid0; auto.
         * subst; eapply step_evalid; eauto. }
    ** intros; split; intros. 
       { destruct (eq_dec e a); subst.
         * assert (e = a) by tauto; subst. 
           eapply step_aux_unique_undirected in deleteEdge_premise0 as [[]|[]]; eauto.
           apply step_sym; auto.
         * assert (e <> a) by tauto. 
           left; apply deleteEdge_step_aux0; split; auto. }
       { destruct H. 
         * apply deleteEdge_step_aux0; auto.
         * destruct H as [[? []]|[? []]]; subst; [|apply step_sym]; auto. }
Qed.

End GRAPH_OPERATIONS. *)