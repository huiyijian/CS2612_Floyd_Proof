Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Wf_nat.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.
Local Open Scope sets.


Section floyd.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {destructn1path: Destructn1Path G V E P path emptypath singlepath concatpath}
        {ind1npath: PathInd1n G V E P path emptypath singlepath concatpath}
        {indn1path: PathIndn1 G V E P path emptypath singlepath concatpath}.

Context {path_unique: forall g p1 p2, 
  path_valid g p1 -> path_valid g p2 -> 
  head p1 = head p2 -> 
  edge_in_path p1 = edge_in_path p2 -> 
  p1 = p2}.

Context {sud: StepUniqueDirected G V E}.
Context {g_valid: gvalid g}.

Context {ew: EdgeWeight G E}.

(** 无负环假设：图中不存在权重和为负的环路 *)
Definition NoNegativeCycle : Prop :=
  forall p, path_valid g p -> head p = tail p -> Z_op_le (Some 0%Z) (path_weight g p).

Context {nnc: NoNegativeCycle}.

Lemma empty_path_edge: forall v, edge_in_path (empty_path v) = nil.
Proof.
  intros v.
  pose proof (vpath_iff_epath g (empty_path v) (empty_path_valid g v)) as [Hlen _].
  rewrite empty_path_vertex in Hlen. simpl in Hlen.
  destruct (edge_in_path (empty_path v)); auto.
  simpl in Hlen. lia.
Qed.

Lemma Z_op_plus_assoc: forall x y z,
  Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z.
Proof.
  intros. destruct x, y, z; simpl; auto.
  f_equal. lia.
Qed.

Lemma Z_op_plus_zero_l: forall x,
  Z_op_plus (Some 0%Z) x = x.
Proof.
  intros. destruct x; simpl; auto.
Qed.

Lemma Zlist_sum_app: forall l1 l2,
  Zlist_sum (l1 ++ l2) = Z_op_plus (Zlist_sum l1) (Zlist_sum l2).
Proof.
  intros l1 l2.
  unfold Zlist_sum.
  induction l1.
  - simpl. symmetry. apply Z_op_plus_zero_l.
  - simpl. rewrite IHl1.
    apply Z_op_plus_assoc.
Qed.

Lemma concat_path_weight: forall g p1 p2,
  path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros. unfold path_weight.
  rewrite concat_path_edge.
  rewrite map_app.
  apply Zlist_sum_app.
Qed.

Notation step := (step g).
Notation reachable := (reachable g).

(** ===== Floyd 算法证明路线 =====

*)
Lemma path_through_empty_is_direct: forall u v p,
  is_path_through_vset g p u v ∅ ->
  is_empty_path p \/ exists e, step_aux g e u v.
Proof.
  intros. destruct H as [[Hp_valid [Hp_head Hp_tail]] Hempty].
  destruct (destruct_1n_path p) as [v_base | p' u_step v_step e_step] eqn:Hdestruct.
  - (* Empty path *)
    left. 
    pose proof (destruct_1n_spec _ _ Hp_valid) as Hspec.
    rewrite Hdestruct in Hspec.
    rewrite Hspec.
    exists v_base. reflexivity.
  - (* Step *)
    right. 
    pose proof (destruct_1n_spec _ _ Hp_valid) as Hspec.
    rewrite Hdestruct in Hspec.
    destruct Hspec as [Hp' [Hhead [Hstep Heq]]].
    destruct (destruct_1n_path p') as [v_base' | p'' u_step' v_step' e_step'] eqn:Hdestruct'.
    + (* p' is empty *)
      pose proof (destruct_1n_spec _ _ Hp') as Hspec'.
      rewrite Hdestruct' in Hspec'.
      exists e_step.
      pose proof (tail_valid _ _ Hp_valid) as Htv.
        rewrite Hp_tail in Htv.
        rewrite Heq in Htv. rewrite Hspec' in Htv.
        rewrite concat_path_vertex in Htv. rewrite empty_path_vertex in Htv. simpl in Htv.
        rewrite single_path_vertex in Htv. simpl in Htv.
        injection Htv as Hv_eq.
  
        pose proof (head_valid _ _ Hp_valid) as Hhv.
         rewrite Hp_head in Hhv.
         rewrite Heq in Hhv. rewrite concat_path_vertex in Hhv.
         rewrite single_path_vertex in Hhv. simpl in Hhv.
         injection Hhv as Hu_eq. 
         
         subst.
         rewrite Hv_eq.
         rewrite Hu_eq.
         exact Hstep.

      + (* p' is not empty *)
      exfalso.
      pose proof (destruct_1n_spec _ _ Hp') as Hspec'.
      rewrite Hdestruct' in Hspec'.
      destruct Hspec' as [Hp'' [Hhead' [Hstep' Heq']]].
      specialize (Hempty v_step).
      apply Hempty.
      exists (single_path u_step v_step e_step), p'.
      repeat split.
      * apply single_path_valid; auto.
      * exact Hp'.
      * intros Hcontra. destruct Hcontra as [vx Hcontra].
        pose proof (single_path_vertex u_step v_step e_step).
        rewrite Hcontra in H. rewrite empty_path_vertex in H.
        discriminate.
      * intros Hcontra. destruct Hcontra as [vx Hcontra].
        rewrite Heq' in Hcontra.
        apply (f_equal vertex_in_path) in Hcontra.
        rewrite concat_path_vertex in Hcontra.
        pose proof (single_path_vertex u_step' v_step' e_step') as Hspv.
        rewrite Hspv in Hcontra. simpl in Hcontra.
        rewrite empty_path_vertex in Hcontra.
        destruct (vertex_in_path p''); simpl in *; discriminate.
      * rewrite Heq. auto.
      * pose proof (single_path_valid _ _ _ _ Hstep) as Hsp_valid.
        pose proof (tail_valid _ _ Hsp_valid) as Htv.
        rewrite single_path_vertex in Htv. simpl in Htv.
        injection Htv. auto.
Qed.


(** ===== 路径基本性质引理 ===== *)

(** 路径拼接保持路径性质 *)
Lemma path_concat_valid: forall (i j k: V) (p1 p2: P), 
  is_path g p1 i j -> 
  is_path g p2 j k -> 
  is_path g (concat_path p1 p2) i k.
Proof.
  intros. destruct H as [Hp1 [Hhead1 Htail1]].
  destruct H0 as [Hp2 [Hhead2 Htail2]].
  split.
  - apply concat_path_valid; auto.
    rewrite Htail1, Hhead2. reflexivity.
  - split.
    + pose proof (head_valid _ _ Hp1) as Hhv1.
      pose proof (concat_path_valid _ _ _ Hp1 Hp2 (eq_trans Htail1 (eq_sym Hhead2))) as Hp.
      pose proof (head_valid _ _ Hp) as Hhv.
      rewrite Hhead1 in Hhv1.
      case_eq (vertex_in_path p1); intros.
      * rename H into Heqvp1.
        pose proof (vpath_iff_epath _ _ Hp1) as [Hlen _].
        rewrite Heqvp1 in Hlen. simpl in Hlen. lia.
      * rename v into v1. rename l into l1. rename H into Heqvp1.
        rewrite concat_path_vertex in Hhv.
        rewrite Heqvp1 in Hhv. rewrite Heqvp1 in Hhv1.
        simpl in Hhv. simpl in Hhv1. injection Hhv1 as Hi. subst v1.
        injection Hhv. auto.
    + pose proof (tail_valid _ _ Hp2) as Htv2.
      pose proof (concat_path_valid _ _ _ Hp1 Hp2 (eq_trans Htail1 (eq_sym Hhead2))) as Hp.
      pose proof (tail_valid _ _ Hp) as Htv.
      rewrite Htail2 in Htv2.
      case_eq (vertex_in_path p2); intros.
      * rename H into Heqvp2.
        pose proof (vpath_iff_epath _ _ Hp2) as [Hlen _].
        rewrite Heqvp2 in Hlen. simpl in Hlen. lia.
      * rename v into v2. rename l into l2. rename H into Heqvp2.
        rewrite concat_path_vertex in Htv.
        destruct l2 as [| v_next l_rest].
        { (* p2 has only 1 vertex *)
          rewrite Heqvp2 in Htv2. simpl in Htv2. injection Htv2 as Hk. subst v2.
          rewrite Heqvp2 in Htv. simpl in Htv. rewrite app_nil_r in Htv.
          pose proof (tail_valid _ _ Hp1) as Htv1.
          rewrite Htail1 in Htv1.
          rewrite <- Htv1 in Htv.
          pose proof (head_valid _ _ Hp2) as Hhv2.
          rewrite Hhead2 in Hhv2.
          rewrite Heqvp2 in Hhv2. simpl in Hhv2. injection Hhv2 as Hj.
          subst k.
          injection Htv as Hfinal. rewrite <- Hj. exact Hfinal.
        }
        { (* p2 has > 1 vertex *)
          rewrite Heqvp2 in Htv2. simpl in Htv2.
          rewrite Heqvp2 in Htv. simpl in Htv.
          assert (Htl: forall A (l1 l2: list A), l2 <> nil -> tl_error (l1 ++ l2) = tl_error l2).
          {
             intros A0 l10 l20 Hnn.
             induction l10 as [| a l10 IH].
             - simpl. reflexivity.
             - simpl. destruct (l10 ++ l20) eqn:Heq.
               + apply app_eq_nil in Heq. destruct Heq. subst. contradiction.
               + assert (Hstep: tl_error (a :: a0 :: l) = tl_error (a0 :: l)).
                   { unfold tl_error. simpl. rewrite Nat.sub_0_r. reflexivity. }
                   rewrite Hstep. apply IH.
          }
          rewrite Htl in Htv.
           - assert (Heq_tl: tl_error (v2 :: v_next :: l_rest) = tl_error (v_next :: l_rest)).
             { unfold tl_error. simpl. rewrite Nat.sub_0_r. reflexivity. }
             rewrite Heq_tl in Htv2.
             rewrite <- Htv in Htv2.
             injection Htv2. auto.
           - discriminate.
        }
Qed.

(** 路径拼接的权重等于两段路径权重之和 *)
Lemma path_concat_weight: forall (i j k: V) (p1 p2: P),
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros.
  unfold path_weight.
  rewrite concat_path_edge.
  rewrite map_app.
  unfold Zlist_sum.
  
  assert (Z_op_plus_assoc: forall x y z, Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z).
            { intros. destruct x, y, z; simpl; try reflexivity. rewrite Z.add_assoc. reflexivity. }
  assert (Z_op_plus_id_l: forall x, Z_op_plus (Some 0%Z) x = x).
  { intros. destruct x; simpl; auto. }
  
  generalize dependent (map (weight g) (edge_in_path p2)).
  intro l2.
  Arguments Z_op_plus : simpl never.
  induction (map (weight g) (edge_in_path p1)).
  - simpl. rewrite Z_op_plus_id_l. reflexivity.
  - simpl. rewrite IHl. rewrite Z_op_plus_assoc. reflexivity.
Qed.

Lemma Z_op_plus_assoc_global: forall x y z, Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z.
Proof.
  intros. destruct x as [x|]; destruct y as [y|]; destruct z as [z|]; unfold Z_op_plus; auto.
  f_equal. apply Z.add_assoc.
Qed.

(** Helper lemmas for list and path *)

Lemma tl_error_app_ne: forall A (l1 l2: list A), l2 <> nil -> tl_error (l1 ++ l2) = tl_error l2.
Proof.
  intros A l1 l2 Hne.
  unfold tl_error.
  rewrite length_app.
  destruct l2.
  - contradiction.
  - simpl. 
    rewrite Nat.add_succ_r. simpl.
    rewrite nth_error_app2.
    + f_equal. lia.
    + lia.
Qed.

Lemma vertex_in_path_not_nil: forall p, path_valid g p -> vertex_in_path p <> nil.
Proof.
  intros p Hp Hcontra.
  pose proof (vpath_iff_epath g p Hp) as Hprop.
  destruct Hprop as [Hlen _].
  rewrite Hcontra in Hlen. simpl in Hlen.
  lia.
Qed.

Lemma is_empty_path_iff_edges_nil: forall p, path_valid g p -> (is_empty_path p <-> edge_in_path p = nil).
Proof.
  intros p Hp. split.
  - intros Hempty. destruct Hempty as [v H]. subst. apply empty_path_edge.
  - intros Hnil.
    destruct (destruct_1n_path p) as [v | p' u v e] eqn:H.
    + exists v. pose proof (destruct_1n_spec _ _ Hp). rewrite H in H0. auto.
    + pose proof (destruct_1n_spec _ _ Hp). rewrite H in H0. destruct H0 as [_ [_ [_ Heq]]].
      rewrite Heq in Hnil. rewrite concat_path_edge in Hnil. rewrite single_path_edge in Hnil.
      destruct (edge_in_path p'); discriminate.
Qed.

Lemma head_concat: forall p1 p2,
  path_valid g p1 -> path_valid g p2 -> tail p1 = head p2 ->
  head (concat_path p1 p2) = head p1.
Proof.
  intros.
  pose proof (head_valid _ _ (concat_path_valid _ _ _ H H0 H1)) as Hh.
  rewrite concat_path_vertex in Hh.
  pose proof (head_valid _ _ H) as Hh1.
  destruct (vertex_in_path p1) eqn:Hv1.
  - apply vertex_in_path_not_nil in H. congruence.
  - simpl in Hh. simpl in Hh1. injection Hh1 as Hh1. subst v.
    injection Hh as Hh. auto.
Qed.

Lemma tail_concat: forall p1 p2,
  path_valid g p1 -> path_valid g p2 -> tail p1 = head p2 ->
  tail (concat_path p1 p2) = tail p2.
Proof.
  intros.
  pose proof (tail_valid _ _ (concat_path_valid _ _ _ H H0 H1)) as Ht.
  rewrite concat_path_vertex in Ht.
  pose proof (tail_valid _ _ H0) as Ht2.
  destruct (vertex_in_path p2) as [|v2 vs2] eqn:Hv2.
  - apply vertex_in_path_not_nil in H0. congruence.
  - simpl in Ht2.
    destruct vs2 as [|v3 vs3].
    + (* p2 is single vertex *)
              simpl in Ht2. injection Ht2 as Ht2. subst v2.
              simpl in Ht. rewrite app_nil_r in Ht.
              pose proof (tail_valid _ _ H) as Ht1.
              rewrite <- Ht1 in Ht. injection Ht as Ht.
              rewrite Ht.
              rewrite H1.
              pose proof (head_valid _ _ H0) as Hh2.
              rewrite Hv2 in Hh2. simpl in Hh2. injection Hh2 as Hh2.
              rewrite Hh2. reflexivity.
    + (* p2 has >= 2 vertices *)
              simpl in Ht.
              rewrite tl_error_app_ne in Ht.
              * assert (Hte: tl_error (v2 :: v3 :: vs3) = tl_error (v3 :: vs3)).
                 { unfold tl_error. simpl. rewrite Nat.sub_0_r. reflexivity. }
                 rewrite Hte in Ht2.
                rewrite <- Ht2 in Ht. injection Ht as Ht. auto.
              * simpl. discriminate.
Qed.

Lemma concat_path_assoc: forall (p1 p2 p3: P),
  path_valid g p1 -> path_valid g p2 -> path_valid g p3 ->
  tail p1 = head p2 ->
  tail p2 = head p3 ->
  concat_path p1 (concat_path p2 p3) = concat_path (concat_path p1 p2) p3.
Proof.
  intros.
  apply path_unique with (g:=g).
  - apply concat_path_valid; auto.
    apply concat_path_valid; auto.
    rewrite head_concat; auto.
  - apply concat_path_valid; auto.
    apply concat_path_valid; auto.
    rewrite tail_concat; auto.
  - assert (Hp23: path_valid g (concat_path p2 p3)) by (apply concat_path_valid; auto).
    assert (Hp12: path_valid g (concat_path p1 p2)) by (apply concat_path_valid; auto).
    assert (Hh23: head (concat_path p2 p3) = head p2) by (apply head_concat; auto).
    assert (Ht12: tail (concat_path p1 p2) = tail p2) by (apply tail_concat; auto).
    rewrite head_concat; [| auto | auto | rewrite Hh23; auto].
     rewrite head_concat; [| auto | auto | rewrite Ht12; auto].
      rewrite head_concat; auto.
   - rewrite concat_path_edge. rewrite concat_path_edge.
    rewrite concat_path_edge. rewrite concat_path_edge.
    rewrite app_assoc. reflexivity.
Qed.

Lemma head_concat_valid: forall p1 p2,
  path_valid g p1 -> path_valid g (concat_path p1 p2) ->
  head (concat_path p1 p2) = head p1.
Proof.
  intros p1 p2 Hp1 Hvalid.
  pose proof (head_valid _ _ Hvalid) as Hh.
  rewrite concat_path_vertex in Hh.
  pose proof (head_valid _ _ Hp1) as Hh1.
  destruct (vertex_in_path p1) eqn:Hv1.
  - apply vertex_in_path_not_nil in Hp1. congruence.
  - simpl in Hh. simpl in Hh1. injection Hh1 as Hh1. subst v.
    injection Hh as Hh. auto.
Qed.


Lemma path_split_by_edges: forall p l1 l2,
  path_valid g p ->
  edge_in_path p = l1 ++ l2 ->
  exists p1 p2, path_valid g p1 /\ path_valid g p2 /\ p = concat_path p1 p2 /\ edge_in_path p1 = l1 /\ edge_in_path p2 = l2 /\ tail p1 = head p2.
Proof.
  intros p l1. revert p.
  induction l1 as [| e l1' IH].
  - intros p l2 Hp Heq.
    exists (empty_path (head p)), p.
    repeat split.
    + apply empty_path_valid.
    + exact Hp.
    + apply (path_unique g); auto.
      * apply concat_path_valid; auto.
        -- apply empty_path_valid.
        -- pose proof (tail_valid _ _ (empty_path_valid g (head p))) as Ht.
           rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht.
           rewrite Ht. reflexivity.
      * symmetry. rewrite head_concat_valid.
        -- pose proof (head_valid _ _ (empty_path_valid g (head p))) as Hh.
           rewrite empty_path_vertex in Hh. simpl in Hh. injection Hh as Hh.
           exact Hh.
        -- apply empty_path_valid.
        -- apply concat_path_valid; auto.
           ++ apply empty_path_valid.
           ++ pose proof (tail_valid _ _ (empty_path_valid g (head p))) as Ht.
              rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht.
              rewrite Ht. reflexivity.
      * rewrite concat_path_edge. rewrite empty_path_edge. simpl. rewrite Heq. reflexivity.
    + rewrite empty_path_edge. reflexivity.
    + rewrite Heq. reflexivity.
    + pose proof (tail_valid _ _ (empty_path_valid g (head p))) as Ht.
      rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht.
      rewrite Ht. reflexivity.
  - intros p l2 Hp Heq.
    destruct (destruct_1n_path p) as [v | p' u v e0] eqn:Hdestruct.
    + pose proof (destruct_1n_spec _ _ Hp) as Hspec. rewrite Hdestruct in Hspec.
       rewrite Hspec in Heq. rewrite empty_path_edge in Heq. discriminate.
    + pose proof (destruct_1n_spec _ _ Hp) as Hspec. rewrite Hdestruct in Hspec. destruct Hspec as [Hp' [Hhead' [Hstep' Heq_p]]].
      rewrite Heq_p in Heq. rewrite concat_path_edge in Heq. rewrite single_path_edge in Heq.
      simpl in Heq. injection Heq as He_eq Heq'.
      subst e0.
      specialize (IH p' l2 Hp' Heq').
      destruct IH as [p1' [p2' [Hp1' [Hp2' [Hsplit' [He1' [He2' Htail_match]]]]]]].
      exists (concat_path (single_path u v e) p1'), p2'.
      repeat split.
      * apply concat_path_valid; auto. apply single_path_valid; auto.
        pose proof (tail_valid _ _ (single_path_valid g u v e Hstep')) as Ht.
         rewrite single_path_vertex in Ht. simpl in Ht. injection Ht as Ht.
         rewrite Ht.
         rewrite <- Hhead'.
          rewrite Hsplit'.
          rewrite head_concat_valid; auto.
           rewrite <- Hsplit'. exact Hp'.
      * exact Hp2'.
      * rewrite Heq_p. rewrite Hsplit'.
        rewrite concat_path_assoc.
        -- reflexivity.
        -- apply single_path_valid; auto.
        -- exact Hp1'.
        -- exact Hp2'.
        -- pose proof (tail_valid _ _ (single_path_valid g u v e Hstep')) as Ht_single.
           rewrite single_path_vertex in Ht_single. simpl in Ht_single. injection Ht_single as Ht_single.
           rewrite Ht_single.
           rewrite <- Hhead'.
           rewrite Hsplit'.
           apply head_concat_valid; auto.
           rewrite <- Hsplit'. exact Hp'.
        -- exact Htail_match.
      * rewrite concat_path_edge. rewrite single_path_edge. rewrite He1'. reflexivity.
      * exact He2'.
      * rewrite tail_concat.
        -- exact Htail_match.
        -- apply single_path_valid; auto.
        -- exact Hp1'.
        -- pose proof (tail_valid _ _ (single_path_valid g u v e Hstep')) as Ht_single.
           rewrite single_path_vertex in Ht_single. simpl in Ht_single. injection Ht_single as Ht_single.
           rewrite Ht_single.
           rewrite <- Hhead'.
           rewrite Hsplit'.
           apply head_concat_valid; auto.
           rewrite <- Hsplit'. exact Hp'.
Qed.

Lemma tail_eq_head_of_valid_concat: forall p1 p2,
  path_valid g p1 -> path_valid g p2 -> ~ is_empty_path p2 ->
  path_valid g (concat_path p1 p2) ->
  tail p1 = head p2.
Proof.
  intros p1 p2 Hp1 Hp2 Hne2 Hvc.
  pose proof (concat_path_edge p1 p2) as He.
  pose proof (path_split_by_edges (concat_path p1 p2) (edge_in_path p1) (edge_in_path p2) Hvc He) as [p1' [p2' [Hp1' [Hp2' [Hcat' [He1' [He2' Hjoin]]]]]]].
  assert (p1 = p1').
  { apply (path_unique g); auto.
    pose proof (head_concat_valid _ _ Hp1 Hvc) as Hhead1.
    assert (Hvc': path_valid g (concat_path p1' p2')). { rewrite <- Hcat'. exact Hvc. }
    pose proof (head_concat_valid _ _ Hp1' Hvc') as Hhead1'.
    rewrite <- Hhead1. rewrite <- Hhead1'. rewrite Hcat'. reflexivity.
   }
  subst p1'.
  assert (p2 = p2').
  { apply (path_unique g); auto.
    destruct (edge_in_path p2) eqn:Hep2.
      + exfalso. apply Hne2. rewrite is_empty_path_iff_edges_nil; auto.
      + assert (Hep: valid_epath g (head p2) (e :: l) (tail p2)).
        { exists p2. repeat split; auto.
          - symmetry. apply (head_valid g); auto.
          - symmetry. apply (tail_valid g); auto.
        }
        assert (Hep': valid_epath g (head p2') (e :: l) (tail p2')).
        { exists p2'. repeat split; auto.
          - symmetry. apply (head_valid g); auto.
          - symmetry. apply (tail_valid g); auto.
        }
        apply valid_epath_cons_inv in Hep.
        apply valid_epath_cons_inv in Hep'.
        destruct Hep as [v [Hstep _]].
        destruct Hep' as [v' [Hstep' _]].
        destruct (step_aux_unique g e (head p2) v (head p2') v' g_valid Hstep Hstep') as [Hh _].
        rewrite Hh. reflexivity.
  }
  subst p2'.
  assumption.
Qed.

(** 如果一条路径经过顶点 k，那么可以分解为两段 *)
Lemma path_decompose_at_vertex: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v (vset ∪ [k]) ->
  In k (vertex_in_path p) ->
  exists p1 p2,
    is_path_through_vset g p1 u k vset /\
    is_path_through_vset g p2 k v vset /\
    Z_op_le (Z_op_plus (path_weight g p1) (path_weight g p2)) (path_weight g p).
Proof.
  intros u v k p vset Hp Hin.
  
  assert (Z_op_le_refl: forall x, Z_op_le x x).
  { intros. destruct x; simpl; lia. }
  assert (Z_op_le_trans: forall x y z, Z_op_le x y -> Z_op_le y z -> Z_op_le x z).
  { intros. destruct x, y, z; simpl in *; try contradiction; try lia; auto. }
  assert (Z_op_plus_le_mono_r: forall a b c, Z_op_le a b -> Z_op_le (Z_op_plus a c) (Z_op_plus b c)).
  { intros. destruct a, b, c; simpl in *; try contradiction; try lia; auto. }
  assert (Single_no_split: forall u v e q1 q2, 
     concat_path q1 q2 = single_path u v e -> 
     path_valid g q1 -> path_valid g q2 ->
     ~ is_empty_path q1 -> ~ is_empty_path q2 -> False).
  {
     intros u0 v0 e0 q1 q2 Hc Hv1 Hv2 Hn1 Hn2.
     rewrite is_empty_path_iff_edges_nil in Hn1; auto.
     rewrite is_empty_path_iff_edges_nil in Hn2; auto.
     pose proof (single_path_edge u0 v0 e0).
     rewrite <- Hc in H. rewrite concat_path_edge in H.
     apply app_eq_unit in H.
     destruct H as [[H1 H2] | [H1 H2]].
     - apply Hn1. exact H1.
     - apply Hn2. exact H2.
  }

  (* Step 1: Split p at the FIRST occurrence of k *)
  assert (exists p1 p2, 
            is_path_through_vset g p1 u k vset /\ 
            is_path_through_vset g p2 k v (vset ∪ [k]) /\
            Z_op_le (Z_op_plus (path_weight g p1) (path_weight g p2)) (path_weight g p)).
  {
    destruct Hp as [[Hp_valid [Hp_head Hp_tail]] H_vset].
    revert u v Hp_head Hp_tail H_vset Hin.
    pattern p.
    apply (path_ind1n g); [| | exact Hp_valid].
    - (* Empty path *)
      intros v0 u v Hp_head Hp_tail H_vset Hin.
      exists (empty_path k), (empty_path k).
      rewrite empty_path_vertex in Hin. simpl in Hin. destruct Hin; [|contradiction]. subst v0.
      pose proof (head_valid _ _ (empty_path_valid g k)) as Hh.
       rewrite empty_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
       rewrite Hh' in Hp_head. subst u.
       pose proof (tail_valid _ _ (empty_path_valid g k)) as Ht.
       rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht'.
       rewrite Ht' in Hp_tail. subst v.
      split; [|split].
      + split.
         * split; [|split].
           { apply empty_path_valid. }
           { exact Hh'. }
           { exact Ht'. }
         * intros x Hfalse. destruct Hfalse as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat _]]]]]]].
            rewrite is_empty_path_iff_edges_nil in Hne1; auto.
            pose proof (concat_path_edge q1 q2).
             rewrite Hcat in H. rewrite empty_path_edge in H.
             symmetry in H.
             apply app_eq_nil in H. destruct H as [H_nil _].
             contradiction.
        + split.
          * split; [|split].
            { apply empty_path_valid. }
            { exact Hh'. }
            { exact Ht'. }
          * intros x Hfalse. destruct Hfalse as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat _]]]]]]].
            rewrite is_empty_path_iff_edges_nil in Hne1; auto.
            pose proof (concat_path_edge q1 q2).
             rewrite Hcat in H. rewrite empty_path_edge in H.
             symmetry in H.
             apply app_eq_nil in H. destruct H as [H_nil _].
             contradiction.
      + unfold path_weight. rewrite empty_path_edge.
         change (Z_op_plus (Some 0%Z) (Some 0%Z)) with (Some 0%Z).
         apply Z_op_le_refl.
    - (* Step: p = concat (single u0 v0 e) p' *)
      intros u_step v_step e p_rest Hstep Hp_rest_valid Hhead_rest IH u v Hp_head Hp_tail H_vset Hin.
      
      destruct (classic (u_step = k)).
      + (* Found k at start *)
        subst u_step.
        assert (Hu: u = k).
         { 
           assert (Hp_valid_local: path_valid g (concat_path (single_path k v_step e) p_rest)).
           {
             apply concat_path_valid.
             - apply single_path_valid. exact Hstep.
             - exact Hp_rest_valid.
             - rewrite Hhead_rest.
               pose proof (tail_valid _ _ (single_path_valid g k v_step e Hstep)) as Ht_single.
               rewrite single_path_vertex in Ht_single. simpl in Ht_single.
               injection Ht_single as Ht_single. exact Ht_single.
           }
           pose proof (head_valid _ _ Hp_valid_local) as Hv.
           rewrite Hp_head in Hv.
           rewrite concat_path_vertex in Hv.
           rewrite single_path_vertex in Hv.
           simpl in Hv.
           injection Hv as Hv. exact Hv.
         }
         rewrite Hu.
         exists (empty_path k), (concat_path (single_path k v_step e) p_rest).
        split; [|split].
        * split.
          { split; [|split].
            - apply empty_path_valid.
            - pose proof (head_valid _ _ (empty_path_valid g k)) as Hh. rewrite empty_path_vertex in Hh. simpl in Hh. injection Hh as Hh2. exact Hh2.
            - pose proof (tail_valid _ _ (empty_path_valid g k)) as Ht. rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht2. exact Ht2.
          }
          { intros x Hfalse. destruct Hfalse as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat _]]]]]]].
            rewrite is_empty_path_iff_edges_nil in Hne1; auto.
            pose proof (concat_path_edge q1 q2).
            rewrite Hcat in H. rewrite empty_path_edge in H.
            symmetry in H. apply app_eq_nil in H. destruct H as [H_nil _].
            contradiction.
          }
        * split.
          { split; [|split].
            - apply concat_path_valid.
              + apply single_path_valid. exact Hstep.
              + exact Hp_rest_valid.
              + rewrite Hhead_rest.
                pose proof (tail_valid _ _ (single_path_valid g k v_step e Hstep)) as Ht_single.
                rewrite single_path_vertex in Ht_single. simpl in Ht_single.
                injection Ht_single as Ht_single. exact Ht_single.
            - rewrite Hp_head. rewrite Hu. reflexivity.
            - rewrite Hp_tail. reflexivity.
          }
          { intros x Hsplit. apply H_vset. exact Hsplit. }
        * unfold path_weight at 1. rewrite empty_path_edge.
          destruct (path_weight g (concat_path (single_path k v_step e) p_rest)) as [w|]; [|apply Z_op_le_refl].
          change (Z_op_plus (Some 0%Z) (Some w)) with (Some w).
          apply Z_op_le_refl.
      + (* u_step != k *)
        assert (Hin_rest: In k (vertex_in_path p_rest)).
        {
          rewrite concat_path_vertex in Hin.
          rewrite single_path_vertex in Hin. simpl in Hin.
          destruct Hin as [Heq | [Heq | Hin]].
          - subst. contradiction. 
          - rewrite <- Heq.
            pose proof (head_valid _ _ Hp_rest_valid) as Hv.
            rewrite Hhead_rest in Hv.
            destruct (vertex_in_path p_rest); simpl in *; try congruence.
            injection Hv as Hv. subst.
            left. reflexivity.
          - destruct (vertex_in_path p_rest).
            + simpl in Hin. contradiction.
            + simpl in Hin. simpl. right. exact Hin.
        }
        
        assert (H_vset_rest: is_path_through_vset g p_rest v_step v (vset ∪ [k])).
        {
           split.
           - split.
             + exact Hp_rest_valid.
             + split.
               * rewrite Hhead_rest. reflexivity.
               * assert (Hp_concat_valid: path_valid g (concat_path (single_path u_step v_step e) p_rest)).
                  {
                    apply concat_path_valid.
                    - apply single_path_valid. exact Hstep.
                    - exact Hp_rest_valid.
                    - rewrite Hhead_rest.
                      pose proof (tail_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Ht_s.
                      rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s. exact Ht_s.
                  }
                  pose proof (tail_valid _ _ Hp_concat_valid) as Ht1.
                  pose proof (tail_valid _ _ Hp_rest_valid) as Ht2.
                 rewrite Hp_tail in Ht1.
                 rewrite concat_path_vertex in Ht1.
                 rewrite single_path_vertex in Ht1. simpl in Ht1.
                 destruct (vertex_in_path p_rest) as [| v0 l] eqn:Hvp.
                  -- pose proof (vertex_in_path_not_nil _ Hp_rest_valid) as Hnn.
                     rewrite Hvp in Hnn. congruence.
                  -- pose proof (head_valid _ _ Hp_rest_valid) as Hhd.
                     rewrite Hhead_rest in Hhd.
                     rewrite Hvp in Hhd. simpl in Hhd. injection Hhd as Hhd. subst v0.
                     simpl in Ht1.
                     assert (Heq_tl: tl_error (u_step :: v_step :: l) = tl_error (v_step :: l)).
                       { unfold tl_error. simpl. f_equal. lia. }
                       rewrite Heq_tl in Ht1. clear Heq_tl.
                       simpl in Ht2.
                        rewrite <- Ht1 in Ht2.
                        injection Ht2 as Ht2. exact Ht2.
           - intros x Hsplit. apply H_vset.
             destruct Hsplit as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
             exists (concat_path (single_path u_step v_step e) q1), q2.
             split; [|split; [|split; [|split; [|split]]]].
             + apply concat_path_valid.
               * apply single_path_valid; auto.
               * auto.
               * pose proof (tail_valid g _ (single_path_valid g _ _ _ Hstep)) as Ht_single.
                 rewrite single_path_vertex in Ht_single. simpl in Ht_single.
                 injection Ht_single as Ht_single. rewrite Ht_single.
                 pose proof (head_valid g _ Hp_rest_valid) as Hhr.
                 rewrite Hhead_rest in Hhr.
                 rewrite <- Hcat in Hhr.
                 assert (Hvalid_cat: path_valid g (concat_path q1 q2)). { rewrite Hcat. exact Hp_rest_valid. }
                 rewrite <- (head_valid _ _ Hvalid_cat) in Hhr.
                 rewrite head_concat_valid in Hhr; auto.
                 injection Hhr as Hhr.
                 exact Hhr.
             + auto.
             + intros Hcontra.
               destruct Hcontra as [v_empty Heq_empty].
               pose proof (concat_path_edge (single_path u_step v_step e) q1) as Hce.
               rewrite Heq_empty in Hce. rewrite empty_path_edge in Hce.
               rewrite single_path_edge in Hce. simpl in Hce.
               discriminate.
             + assumption.
             + rewrite <- concat_path_assoc.
               * rewrite Hcat. reflexivity.
               * apply single_path_valid; auto.
               * auto.
               * auto.
               * pose proof (tail_valid g _ (single_path_valid g _ _ _ Hstep)) as Ht_single.
                 rewrite single_path_vertex in Ht_single. simpl in Ht_single.
                 injection Ht_single as Ht_single.
                 rewrite Ht_single.
                 rewrite <- Hhead_rest.
                 rewrite <- Hcat.
                 apply head_concat_valid; auto.
                 rewrite Hcat. exact Hp_rest_valid.
               * apply tail_eq_head_of_valid_concat; auto.
                  rewrite Hcat. exact Hp_rest_valid.
             + rewrite tail_concat.
               * exact Htl.
               * apply single_path_valid; auto.
               * auto.
               * pose proof (tail_valid g _ (single_path_valid g _ _ _ Hstep)) as Ht_single.
                 rewrite single_path_vertex in Ht_single. simpl in Ht_single. injection Ht_single as Ht_single.
                 rewrite Ht_single.
                 rewrite <- Hhead_rest.
                 rewrite <- Hcat.
                 rewrite head_concat_valid; auto.
                 rewrite Hcat. exact Hp_rest_valid.
        }
        
       destruct (classic (v_step = k)) as [Heq_k | Hneq_k].
       { (* Case 1: v_step = k. Split at v_step. *)
         subst v_step.
         assert (Hsingle_val: path_valid g (single_path u_step k e)).
         { apply single_path_valid. rewrite <- Heq_k. exact Hstep. }
         exists (single_path u_step k e), p_rest.
         split; [|split].
         - (* p1 through vset *)
           split.
           + repeat split.
             * exact Hsingle_val.
             * rewrite <- Hp_head. rewrite head_concat_valid.
               -- rewrite Heq_k. reflexivity.
               -- rewrite Heq_k. exact Hsingle_val.
               -- rewrite Heq_k. apply concat_path_valid.
                  ** exact Hsingle_val.
                  ** exact Hp_rest_valid.
                  ** pose proof (tail_valid g _ Hsingle_val) as Ht.
                     rewrite (single_path_vertex u_step k e) in Ht. simpl in Ht.
                     injection Ht as Ht. rewrite Ht. auto.
             * pose proof (tail_valid g _ Hsingle_val) as Ht.
               rewrite (single_path_vertex u_step k e) in Ht. simpl in Ht.
               injection Ht as Ht. rewrite Ht. auto.
           + intros x Hsplit.
             destruct Hsplit as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
             (* single_path cannot be split into two non-empty paths *)
             exfalso. apply Single_no_split with (u:=u_step) (v:=k) (e:=e) (q1:=q1) (q2:=q2); auto.
         - (* p2 through vset U [k] *)
           rewrite Heq_k in H_vset_rest. exact H_vset_rest.
         - (* weight *)
           rewrite concat_path_weight.
           rewrite Heq_k.
           apply Z_op_le_refl.
       }
       { (* Case 2: v_step != k. Use IH. *)
         specialize (IH _ _ Hhead_rest (proj2 (proj2 (proj1 H_vset_rest))) (proj2 H_vset_rest) Hin_rest).
         destruct IH as [p1' [p2' [Hp1' [Hp2' Hw']]]].
        
         exists (concat_path (single_path u_step v_step e) p1'), p2'.
         split; [|split].
         * (* p1 through vset *)
           pose proof (single_path_valid g u_step v_step e Hstep) as Hsingle_valid.
           pose proof (tail_valid g _ Hsingle_valid) as Ht_single.
           rewrite single_path_vertex in Ht_single. simpl in Ht_single. injection Ht_single as Ht_single.
           pose proof (head_valid g _ Hsingle_valid) as Hh_single.
           rewrite single_path_vertex in Hh_single. simpl in Hh_single. injection Hh_single as Hh_single.
           split.
           -- destruct Hp1' as [[Hp1'_valid [Hp1'_head Hp1'_tail]] Hp1'_split].
              repeat split.
              ++ apply concat_path_valid; auto.
                 rewrite Ht_single. rewrite Hp1'_head. auto.
              ++ rewrite head_concat_valid.
                 ** rewrite Hh_single.
                    rewrite head_concat_valid in Hp_head; [| exact Hsingle_valid | ].
                    2: { apply concat_path_valid; auto. rewrite Ht_single. rewrite Hhead_rest. auto. }
                    rewrite Hh_single in Hp_head. auto.
                 ** exact Hsingle_valid.
                 ** apply concat_path_valid; auto.
                    rewrite Ht_single. rewrite Hp1'_head. auto.
              ++ rewrite tail_concat.
                 ** rewrite Hp1'_tail. auto.
                 ** exact Hsingle_valid.
                 ** auto.
                 ** rewrite Ht_single. rewrite Hp1'_head. auto.
           -- intros x Hsplit.
              destruct Hsplit as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
              pose proof (concat_path_edge q1 q2) as He_edges.
              rewrite Hcat in He_edges.
              rewrite concat_path_edge in He_edges.
              rewrite single_path_edge in He_edges.
              destruct (edge_in_path q1) eqn:Heq1.
              ++ (* q1 empty *)
                 destruct (destruct_1n_path q1) as [v_q1 | q1' u_q1 v_q1 e_q1] eqn:Hdq1.
                 ** exfalso. apply Hne1. exists v_q1.
                    pose proof (destruct_1n_spec _ _ Hv1) as Hspec1.
                    rewrite Hdq1 in Hspec1. exact Hspec1.
                 ** pose proof (destruct_1n_spec _ _ Hv1) as Hspec1.
                    rewrite Hdq1 in Hspec1. destruct Hspec1 as [_ [_ [_ Heq_q1]]].
                    rewrite Heq_q1 in Heq1. rewrite concat_path_edge in Heq1. rewrite single_path_edge in Heq1.
                    discriminate.
              ++ destruct l.
                 ** (* q1 has 1 edge. q1 = single. tail q1 = v_step. *)
                    assert (Hq1_eq: q1 = single_path u_step v_step e).
                    {
                       apply (path_unique g).
                       - exact Hv1.
                       - exact Hsingle_valid.
                       - rewrite <- (head_concat_valid q1 q2); auto.
                          rewrite Hcat.
                          rewrite head_concat_valid.
                           + reflexivity.
                           + apply single_path_valid; auto.
                           + apply concat_path_valid.
                            * exact Hsingle_valid.
                            * destruct Hp1' as [[Hvp1' _] _]. exact Hvp1'.
                            * rewrite Ht_single. destruct Hp1' as [[_ [Hhp1' _]] _]. rewrite Hhp1'. reflexivity.
                           + rewrite Hcat. apply concat_path_valid.
                             * exact Hsingle_valid.
                             * destruct Hp1' as [[Hvp1' _] _]. exact Hvp1'.
                             * rewrite Ht_single. destruct Hp1' as [[_ [Hhp1' _]] _]. rewrite Hhp1'. reflexivity.
                         - assert (Heq_lists: edge_in_path q1 ++ edge_in_path q2 = edge_in_path (single_path u_step v_step e) ++ edge_in_path p1').
                         { rewrite <- concat_path_edge. rewrite Hcat. rewrite concat_path_edge. reflexivity. }
                         rewrite single_path_edge in Heq_lists.
                         rewrite Heq1 in Heq_lists.
                         simpl in Heq_lists. injection Heq_lists as He_eq _.
                         rewrite Heq1. rewrite He_eq. rewrite single_path_edge. reflexivity.
                    }
                    rewrite Hq1_eq in Htl.
                    rewrite Ht_single in Htl.
                    symmetry in Htl. subst x.
                    (* v_step in vset? *)
                    destruct H_vset_rest as [_ Hv_start].
                    (* prove v_step in vset. *)
                    (* Since v_step != k, and v_step in vset U [k]... *)
                    (* We know p goes through vset U [k]. *)
                    (* The split point between single and p_rest is v_step. *)
                    (* So v_step must be in vset U [k]. *)
                    (* Is this explicitly in H_vset? *)
                    (* H_vset says ANY split x in vset U [k]. *)
                    (* Split p = single ++ p_rest. tail single = v_step. *)
                    (* So v_step in vset U [k]. *)
                    assert (Hv_in_k: v_step ∈ (vset ∪ [k])).
                    {
                      apply H_vset.
                      exists (single_path u_step v_step e), p_rest.
                      repeat split.
                      - apply single_path_valid; auto.
                      - exact Hp_rest_valid.
                      - intros Hempty. destruct Hempty as [v_emp Hemp].
                        pose proof (single_path_vertex u_step v_step e) as Hsv.
                        rewrite Hemp in Hsv. rewrite empty_path_vertex in Hsv. simpl in Hsv. discriminate.
                      - intros Hempty.
                        (* p_rest not empty *)
                        rewrite (is_empty_path_iff_edges_nil p_rest Hp_rest_valid) in Hempty.
                        destruct (edge_in_path p_rest) eqn:Hep.
                        + (* p_rest edges nil. If p_rest empty, vertex_in_path=[v_step]. *)
                          apply <- is_empty_path_iff_edges_nil in Hep; auto.
                          destruct Hep as [v_emp Hemp_eq].
                          rewrite Hemp_eq in Hin_rest.
                          rewrite empty_path_vertex in Hin_rest. simpl in Hin_rest. destruct Hin_rest; [|contradiction].
                          subst k.
                          rewrite Hemp_eq in Hp_rest_valid.
                          pose proof (head_valid g _ Hp_rest_valid) as Hhv.
                          rewrite empty_path_vertex in Hhv. simpl in Hhv.
                          rewrite Hemp_eq in Hhead_rest.
                          rewrite Hhead_rest in Hhv.
                          injection Hhv as Hhv.
                          subst v_emp.
                          contradiction.
                        + discriminate.
                      - try reflexivity.
                        pose proof (tail_valid g _ (single_path_valid g u_step v_step e Hstep)) as Ht_s.
                        rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s. exact Ht_s.
                     }
                     destruct Hv_in_k as [Hin_vset | Hin_k].
                      --- assumption.
                      --- simpl in Hin_k. destruct Hin_k. contradiction.
                 ** (* q1 has >1 edges. q1 = single ++ q_sub. *)
                    (* Use path_split_by_edges logic? *)
                    (* Or just assert structure of q1. *)
                    (* Since edge_in_path q1 = e :: l. *)
                    (* q1 starts with e. head q1 = u_step. *)
                    (* So q1 = concat single q_sub. *)
                    (* Then concat single q_sub = q1. *)
                    (* tail q1 = tail q_sub. *)
                    (* concat q_sub q2 = p1'. *)
                    (* So q_sub splits p1'. *)
                    (* tail q_sub in vset (by Hp1'_split). *)
                    (* So x in vset. *)
                    (* Formalize: decompose q1. *)
                    (* Use destruct_1n_spec on q1. *)
                    destruct (destruct_1n_path q1) as [v_q1 | q_sub u_q1 v_q1 e_q1] eqn:Hdq1.
                    { (* q1 empty -> contradiction *)
                       pose proof (destruct_1n_spec _ _ Hv1) as Hspec.
                       rewrite Hdq1 in Hspec.
                       rewrite Hspec in Heq1. rewrite empty_path_edge in Heq1. discriminate.
                    }
                    pose proof (destruct_1n_spec _ _ Hv1) as Hspec.
                    rewrite Hdq1 in Hspec.
                    destruct Hspec as [Hq_sub_valid [Hhead_sub [Hstep_sub Hq1_eq]]].
                    
                    assert (Hvc_cat: path_valid g (concat_path (single_path u_step v_step e) p1')).
                    {
                         destruct Hp1' as [[Hp1'_valid [Hp1'_head _]] _].
                         apply concat_path_valid.
                         - exact Hsingle_valid.
                         - exact Hp1'_valid.
                         - rewrite Ht_single. rewrite Hp1'_head. reflexivity.
                    }

                    assert (Hsingle_eq: single_path u_q1 v_q1 e_q1 = single_path u_step v_step e).
                     {
                       apply (path_unique g).
                       - apply single_path_valid. exact Hstep_sub.
                       - exact Hsingle_valid.
                       - (* heads equal *)
                        rewrite <- (head_concat (single_path u_q1 v_q1 e_q1) q_sub).
                        2: { apply single_path_valid. exact Hstep_sub. }
                        2: { exact Hq_sub_valid. }
                        2: { 
                           pose proof (tail_valid g _ (single_path_valid g _ _ _ Hstep_sub)) as Ht_s.
                           rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s.
                           rewrite Ht_s. symmetry. exact Hhead_sub.
                        }
                        rewrite <- Hq1_eq.
                        
                        rewrite <- (head_concat_valid q1 q2).
                        2: { exact Hv1. }
                        2: { rewrite Hcat. exact Hvc_cat. }
                        
                        rewrite Hcat.
                        rewrite head_concat_valid.
                        2: { exact Hsingle_valid. }
                        2: { exact Hvc_cat. }
                        
                        reflexivity.
                       - rewrite single_path_edge. rewrite single_path_edge.
                          rewrite Hq1_eq in Heq1.
                          rewrite concat_path_edge in Heq1.
                          rewrite single_path_edge in Heq1.
                          simpl in Heq1.
                          injection Heq1 as He_eq _.
                          rewrite He_eq.
                          simpl in He_edges.
                          injection He_edges as He_e0e.
                          rewrite <- He_e0e.
                          reflexivity.
                      }
                    
                    rewrite Hsingle_eq in Hq1_eq.
                    
                    assert (Hp1'_split_struct: concat_path q_sub q2 = p1').
                    {
                       apply (path_unique g).
                       - assert (Htail_conn: tail q_sub = head q2).
                         {
                             assert (Htail_q1: tail q1 = head q2).
                             { apply tail_eq_head_of_valid_concat; auto. rewrite Hcat. exact Hvc_cat. }
                             rewrite Hq1_eq in Htail_q1.
                             rewrite tail_concat in Htail_q1.
                             - rewrite <- Htail_q1. reflexivity.
                             - exact Hsingle_valid.
                             - exact Hq_sub_valid.
                             - apply f_equal with (f := vertex_in_path) in Hsingle_eq.
                               repeat rewrite single_path_vertex in Hsingle_eq.
                               injection Hsingle_eq as _ Hv_eq.
                               rewrite Hv_eq in Hhead_sub.
                               rewrite Ht_single. symmetry. exact Hhead_sub.
                         }
                         apply concat_path_valid.
                         + exact Hq_sub_valid.
                         + exact Hv2.
                         + exact Htail_conn.
                       - destruct Hp1' as [[Hp1'_valid _] _]. exact Hp1'_valid.
                       - (* heads equal *)
                         rewrite head_concat_valid.
                         + apply f_equal with (f := vertex_in_path) in Hsingle_eq.
                           repeat rewrite single_path_vertex in Hsingle_eq.
                           injection Hsingle_eq as _ Hv_eq.
                           destruct Hp1' as [[_ [Hp1'_head _]] _].
                           rewrite Hp1'_head.
                           rewrite Hhead_sub. rewrite Hv_eq. reflexivity.
                         + exact Hq_sub_valid.
                         + apply concat_path_valid.
                           * exact Hq_sub_valid.
                           * exact Hv2.
                           * (* tail q_sub = head q2 again? Reuse Htail_conn proof or assert earlier *)
                             assert (Htail_q1: tail q1 = head q2).
                             { apply tail_eq_head_of_valid_concat; auto. rewrite Hcat. exact Hvc_cat. }
                             rewrite Hq1_eq in Htail_q1.
                             rewrite tail_concat in Htail_q1.
                             -- rewrite <- Htail_q1. reflexivity.
                             -- exact Hsingle_valid.
                             -- exact Hq_sub_valid.
                             -- apply f_equal with (f := vertex_in_path) in Hsingle_eq.
                                repeat rewrite single_path_vertex in Hsingle_eq.
                                injection Hsingle_eq as _ Hv_eq.
                                rewrite Hv_eq in Hhead_sub.
                                rewrite Ht_single. symmetry. exact Hhead_sub.
                        - apply f_equal with (f := edge_in_path) in Hcat.
                          rewrite Hq1_eq in Hcat.
                          repeat rewrite concat_path_edge in Hcat.
                          repeat rewrite single_path_edge in Hcat.
                          injection Hcat as He_eq.
                          rewrite concat_path_edge.
                          exact He_eq.
                    }
                    
                    destruct Hp1' as [_ Hp1'_split_cond].
                    assert (Hx_in_vset: x ∈ vset).
                    {
                      apply Hp1'_split_cond.
                      exists q_sub, q2.
                      split; [|split; [|split; [|split; [|split]]]].
                      - exact Hq_sub_valid.
                      - exact Hv2.
                      - intros Hempty_sub.
                        rewrite is_empty_path_iff_edges_nil in Hempty_sub; auto.
                        rewrite Hq1_eq in Heq1.
                        rewrite concat_path_edge in Heq1.
                        rewrite single_path_edge in Heq1.
                        rewrite Hempty_sub in Heq1.
                        simpl in Heq1.
                        injection Heq1 as _ Hl.
                        rewrite Hl in *. discriminate.
                      - exact Hne2.
                      - exact Hp1'_split_struct.
                      - rewrite Hq1_eq in Htl.
                        rewrite tail_concat in Htl; auto.
                        + apply f_equal with (f := vertex_in_path) in Hsingle_eq.
                          repeat rewrite single_path_vertex in Hsingle_eq.
                          injection Hsingle_eq as _ Hv_eq.
                          rewrite Hv_eq in Hhead_sub.
                          rewrite Ht_single. symmetry. exact Hhead_sub.
                    }
                    exact Hx_in_vset.
        * (* p2 through vset U [k] *)
           exact Hp2'.
         * (* weight *)
           rewrite concat_path_weight.
           rewrite concat_path_weight.
           rewrite <- Z_op_plus_assoc_global.
           assert (Z_op_plus_le_mono_l: forall a b c, Z_op_le b c -> Z_op_le (Z_op_plus a b) (Z_op_plus a c)).
          { intros a b c Hle. unfold Z_op_plus in *. destruct a; destruct b; destruct c; simpl in *; try contradiction; try lia; auto. }
           apply Z_op_plus_le_mono_l.
           exact Hw'.
  }
  }
  destruct H as [p1 [p2 [Hp1 [Hp2 Hw1]]]].

  (* Step 2: Remove cycles from p2 *)
  assert (Hstep2: exists p2', 
            is_path_through_vset g p2' k v vset /\ 
            Z_op_le (path_weight g p2') (path_weight g p2)).
  {
     clear Hp1 Hw1 Hp Hin p p1.
     destruct Hp2 as [[Hp2_valid [Hp2_head Hp2_tail]] H_vset2].
     revert k v Hp2_head Hp2_tail H_vset2.
     pattern p2.
     apply (path_indn1 g); [| | exact Hp2_valid].
     - (* Empty path *)
        intros v0 k v Hp2_head Hp2_tail H_vset2.
         exists (empty_path k).
         pose proof (head_valid _ _ (empty_path_valid g v0)) as Hh.
       rewrite empty_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
       rewrite Hh' in Hp2_head. subst v0.
        pose proof (tail_valid _ _ (empty_path_valid g k)) as Ht.
        rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht'.
        rewrite Ht' in Hp2_tail. subst v.
        split.
       + repeat split.
          * apply empty_path_valid.
         * pose proof (head_valid _ _ (empty_path_valid g k)) as Hh2.
            rewrite empty_path_vertex in Hh2. simpl in Hh2. injection Hh2 as Hh2'. exact Hh2'.
          * pose proof (tail_valid _ _ (empty_path_valid g k)) as Ht2.
            rewrite empty_path_vertex in Ht2. simpl in Ht2. injection Ht2 as Ht2'. exact Ht2'.
         * intros x Hfalse.
             destruct Hfalse as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
             rewrite is_empty_path_iff_edges_nil in Hne1; auto.
             pose proof (concat_path_edge q1 q2).
             rewrite Hcat in H. rewrite empty_path_edge in H.
             symmetry in H.
             apply app_eq_nil in H. destruct H as [H_nil _].
             contradiction.
       + unfold path_weight. rewrite empty_path_edge.
          change (Z_op_plus (Some 0%Z) (Some 0%Z)) with (Some 0%Z).
          apply Z_op_le_refl.
     - (* Step: p2 = concat p_prev (single u0 v0 e) *)
      intros u_step v_step e p_prev Hstep Hp_prev_valid Htail_prev IH k v Hp2_head Hp2_tail H_vset2.
      
      destruct (classic (v_step = k)) as [Hv_step_eq | Hv_step_neq].
      + (* Ends at k. Whole path is k -> ... -> k. *)
          subst v_step.
          assert (v = k) as Hvk.
          { rewrite <- Hp2_tail. rewrite tail_concat.
            - pose proof (tail_valid _ _ (single_path_valid g u_step k e Hstep)) as Ht.
              rewrite single_path_vertex in Ht. simpl in Ht. injection Ht as Ht'. exact Ht'.
            - exact Hp_prev_valid.
            - apply single_path_valid; exact Hstep.
            - rewrite Htail_prev.
              pose proof (head_valid _ _ (single_path_valid g _ _ _ Hstep)) as Hh_s.
              rewrite single_path_vertex in Hh_s. simpl in Hh_s. injection Hh_s as Hh_s.
              rewrite Hh_s. reflexivity. }
          subst v.
          exists (empty_path k).
          split.
          * repeat split.
             { apply empty_path_valid. }
             { pose proof (head_valid _ _ (empty_path_valid g k)) as Hh.
               rewrite empty_path_vertex in Hh. simpl in Hh. injection Hh as Hh'. exact Hh'. }
             { pose proof (tail_valid _ _ (empty_path_valid g k)) as Ht.
               rewrite empty_path_vertex in Ht. simpl in Ht. injection Ht as Ht'.
               rewrite Ht'.
               rewrite tail_concat.
                - pose proof (tail_valid _ _ (single_path_valid g u_step k e Hstep)) as Ht_s.
                  rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s'.
                  rewrite Ht_s'. reflexivity.
                - exact Hp_prev_valid.
               - apply single_path_valid; exact Hstep.
               - rewrite Htail_prev.
                 pose proof (head_valid _ _ (single_path_valid g _ _ _ Hstep)) as Hh_s.
                 rewrite single_path_vertex in Hh_s. simpl in Hh_s. injection Hh_s as Hh_s.
                 rewrite Hh_s. reflexivity. }
             { intros x Hfalse.
               destruct Hfalse as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
               rewrite is_empty_path_iff_edges_nil in Hne1; auto.
               pose proof (concat_path_edge q1 q2) as H_edges.
               rewrite Hcat in H_edges. rewrite empty_path_edge in H_edges.
               symmetry in H_edges.
               apply app_eq_nil in H_edges. destruct H_edges as [H_nil _].
               contradiction. }
          * (* Weight 0 <= Weight cycle *)
            assert (tail p_prev = head (single_path u_step k e)) as Hlink.
            { rewrite Htail_prev.
              pose proof (head_valid _ _ (single_path_valid g u_step k e Hstep)) as Hh.
              rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
              rewrite Hh'. reflexivity. }
            pose proof (nnc (concat_path p_prev (single_path u_step k e))) as Hnnc.
            specialize (Hnnc (concat_path_valid _ _ _ Hp_prev_valid (single_path_valid _ _ _ _ Hstep) Hlink)).
            eapply Z_op_le_trans.
            2: { apply Hnnc.
                 rewrite Hp2_head.
                 rewrite tail_concat; [|exact Hp_prev_valid|apply single_path_valid; exact Hstep|exact Hlink].
                 pose proof (tail_valid _ _ (single_path_valid g u_step k e Hstep)) as Ht_s.
                 rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s'.
                 rewrite Ht_s'. reflexivity. }
            unfold path_weight. rewrite empty_path_edge. apply Z_op_le_refl.
       + (* v_step != k *)
          destruct (classic (u_step = k)) as [Heq | Hneq].
          * (* Last step is k -> v_step. *)
            subst u_step.
            match goal with H: tail p_prev = k |- _ => rename H into Htail_prev_k; rewrite Htail_prev_k in Hstep end.
           assert (v_step = v) as Hv.
           { rewrite <- Hp2_tail. rewrite tail_concat.
             - rewrite Htail_prev_k.
               pose proof (tail_valid _ _ (single_path_valid g k v_step e Hstep)) as Ht_s.
               rewrite single_path_vertex in Ht_s. simpl in Ht_s. injection Ht_s as Ht_s'.
               rewrite Ht_s'. reflexivity.
             - exact Hp_prev_valid.
             - rewrite Htail_prev_k.
               apply single_path_valid; exact Hstep.
             - rewrite Htail_prev_k.
               pose proof (head_valid _ _ (single_path_valid g k v_step e Hstep)) as Hh_s.
               rewrite single_path_vertex in Hh_s. simpl in Hh_s. injection Hh_s as Hh_s'.
               rewrite Hh_s'. reflexivity.
           }
           subst v_step.
           assert (tail p_prev = k) as Htail_prev_k_dup by exact Htail_prev_k.
           assert (head p_prev = k) as Hhead_prev.
           { rewrite <- Hp2_head.
             symmetry. apply head_concat_valid.
             - exact Hp_prev_valid.
             - apply concat_path_valid.
               + exact Hp_prev_valid.
               + apply single_path_valid. rewrite Htail_prev_k. exact Hstep.
               + rewrite Htail_prev_k.
                 pose proof (head_valid _ _ (single_path_valid g k v e Hstep)) as Hh_s.
                 rewrite single_path_vertex in Hh_s. simpl in Hh_s. injection Hh_s as Hh_s.
                 rewrite Hh_s. reflexivity. }
           assert (is_path_through_vset g p_prev k k (vset ∪ [k])) as Hp_prev_vset.
           {
             unfold is_path_through_vset. split.
             - unfold is_path. repeat split.
               + exact Hp_prev_valid.
               + exact Hhead_prev.
               + exact Htail_prev_k.
             - intros x Hx. apply H_vset2.
               destruct Hx as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
               exists q1, (concat_path q2 (single_path k v e)).
                assert (path_valid g (concat_path q2 (single_path k v e))) as Hvalid_q2_single.
                { apply concat_path_valid.
                  - exact Hv2.
                  - apply single_path_valid; exact Hstep.
                  - assert (head (single_path k v e) = k) as Hh_s.
                    { pose proof (head_valid _ _ (single_path_valid g k v e Hstep)) as H.
                      rewrite single_path_vertex in H. simpl in H. injection H as H. exact H. }
                    rewrite Hh_s.
                    assert (tail q1 = head q2) as Htail_match.
                    { apply tail_eq_head_of_valid_concat; auto. rewrite Hcat. exact Hp_prev_valid. }
                    rewrite <- Htail_prev_k.
                    rewrite <- Hcat.
                    symmetry. apply tail_concat; auto. }
                split. { exact Hv1. }
                split. { exact Hvalid_q2_single. }
                split. { exact Hne1. }
                split.
                { intros Hempty. 
                   assert (is_empty_path (concat_path q2 (single_path k v e)) <-> edge_in_path (concat_path q2 (single_path k v e)) = nil) as Hiff.
                   { apply is_empty_path_iff_edges_nil. exact Hvalid_q2_single. }
                   rewrite Hiff in Hempty.
                   rewrite concat_path_edge in Hempty. rewrite single_path_edge in Hempty.
                   apply app_eq_nil in Hempty. destruct Hempty as [_ Hempty]. simpl in Hempty. discriminate Hempty. }
                  split.
                   { assert (path_valid g (single_path k v e)) as Hsingle_valid by (apply single_path_valid; exact Hstep).
                     assert (tail q1 = head q2) as Htail_match.
                     { apply tail_eq_head_of_valid_concat; auto. rewrite Hcat. exact Hp_prev_valid. }
                     assert (tail q2 = k) as Htail_q2.
                     { rewrite <- Htail_prev_k. rewrite <- Hcat.
                       symmetry. apply tail_concat; auto. }
                     assert (head (single_path k v e) = k) as Hhead_single.
                     { pose proof (head_valid _ _ Hsingle_valid) as H.
                       rewrite single_path_vertex in H. simpl in H. injection H as H. exact H. }
                     rewrite concat_path_assoc; auto.
                     2: { rewrite Hhead_single. exact Htail_q2. }
                     rewrite Hcat.
                     assert (single_path k v e = single_path (tail p_prev) v e) as Heq_single.
                     { f_equal. rewrite Htail_prev_k. reflexivity. }
                     rewrite Heq_single. reflexivity. }
                { exact Htl. }
           }
           exists (single_path k v e).
            split.
            { (* p2' = single_path k v e *)
              unfold is_path_through_vset. split.
               - repeat split.
                 + apply single_path_valid; exact Hstep.
                 + pose proof (head_valid _ _ (single_path_valid g k v e Hstep)) as Hh.
                   rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'. exact Hh'.
                 + pose proof (tail_valid _ _ (single_path_valid g k v e Hstep)) as Ht.
                   rewrite single_path_vertex in Ht. simpl in Ht. injection Ht as Ht'. exact Ht'.
               - intros x Hcontra.
                 destruct Hcontra as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
                 apply f_equal with (f := edge_in_path) in Hcat.
                 rewrite concat_path_edge in Hcat.
                 rewrite single_path_edge in Hcat.
                 assert (length (edge_in_path q1 ++ edge_in_path q2) = 1) as Hlen.
                 { rewrite Hcat. simpl. reflexivity. }
                 rewrite length_app in Hlen.
                 destruct (edge_in_path q1) eqn:Heq1.
                 + exfalso. apply Hne1. apply is_empty_path_iff_edges_nil. exact Hv1. exact Heq1.
                  + destruct (edge_in_path q2) eqn:Heq2.
                    * exfalso. apply Hne2. apply is_empty_path_iff_edges_nil. exact Hv2. exact Heq2.
                    * simpl in Hlen. lia.
            }
            { (* weight *)
              rewrite Htail_prev_k.
              rewrite concat_path_weight.
              assert (Z_op_plus_comm: forall a b, Z_op_plus a b = Z_op_plus b a).
               { intros. destruct a as [za|]; destruct b as [zb|]; unfold Z_op_plus; auto. f_equal. apply Z.add_comm. }
              rewrite Z_op_plus_comm.
              apply Z_op_le_trans with (y := Z_op_plus (path_weight g (single_path k v e)) (Some 0%Z)).
              { destruct (path_weight g (single_path k v e)); simpl.
                - rewrite Z.add_0_r. apply Z.le_refl.
                - exact I.
              }
              assert (Z_op_plus_le_mono_l: forall a b c, Z_op_le a b -> Z_op_le (Z_op_plus c a) (Z_op_plus c b)).
              { intros a0 b0 c0 Hle. rewrite (Z_op_plus_comm c0 a0). rewrite (Z_op_plus_comm c0 b0). apply Z_op_plus_le_mono_r. exact Hle. }
              apply Z_op_plus_le_mono_l.
              assert (head p_prev = tail p_prev) as Hcycle.
               { rewrite Hhead_prev. rewrite Htail_prev_k. reflexivity. }
               pose proof (nnc p_prev Hp_prev_valid Hcycle) as Hw_nnc.
               exact Hw_nnc.
            }
         * (* u_step != k *)
            assert (head p_prev = k) as Hhead_prev.
            { rewrite <- Hp2_head. symmetry. apply head_concat_valid.
              - exact Hp_prev_valid.
              - apply concat_path_valid.
                + exact Hp_prev_valid.
                + apply single_path_valid; exact Hstep.
                + rewrite Htail_prev.
                  pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                  rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                  rewrite Hh'. reflexivity.
            }
            assert (is_path_through_vset g p_prev k u_step (vset ∪ [k])) as Hprev_vset.
            {
               repeat split.
               - exact Hp_prev_valid.
               - exact Hhead_prev.
              - exact Htail_prev.
              - intros x Hsplit. apply H_vset2.
                 destruct Hsplit as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
                  assert (tail q1 = head q2) as Hq1q2.
                  { apply tail_eq_head_of_valid_concat; auto. rewrite Hcat. exact Hp_prev_valid. }
                   assert (tail q2 = u_step) as Htail_q2.
                   { rewrite <- Hcat in Htail_prev. rewrite tail_concat in Htail_prev.
                     exact Htail_prev.
                     exact Hv1.
                     exact Hv2.
                     exact Hq1q2. }
                  exists q1, (concat_path q2 (single_path u_step v_step e)).
                   repeat split.
                   + exact Hv1.
                   + apply concat_path_valid.
                     * exact Hv2.
                     * apply single_path_valid; exact Hstep.
                     * pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                       rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                       rewrite Hh'. exact Htail_q2.
                   + exact Hne1.
                   + intros Hempty. 
                     rewrite is_empty_path_iff_edges_nil in Hempty.
                     rewrite concat_path_edge in Hempty. rewrite single_path_edge in Hempty.
                     destruct (edge_in_path q2); discriminate.
                     apply concat_path_valid.
                     * exact Hv2.
                     * apply single_path_valid; exact Hstep.
                     * rewrite Htail_q2.
                       pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                       rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                       rewrite Hh'. reflexivity.
                   + rewrite concat_path_assoc.
                     * rewrite Hcat. reflexivity.
                     * exact Hv1.
                     * exact Hv2.
                     * apply single_path_valid; exact Hstep.
                     * exact Hq1q2.
                     * pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                       rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                       rewrite Hh'. exact Htail_q2.
                   + exact Htl.
            }
            destruct Hprev_vset as [_ Hsplit].
            specialize (IH k u_step Hhead_prev Htail_prev Hsplit).
           destruct IH as [p_prev' [Hp_prev' Hw]].
            destruct Hp_prev' as [[Hp'_valid [Hp'_head Hp'_tail]] Hp'_vset].
            assert (Hp_new_valid: path_valid g (concat_path p_prev' (single_path u_step v_step e))).
            { apply concat_path_valid.
              - exact Hp'_valid.
              - apply single_path_valid; exact Hstep.
              - rewrite Hp'_tail. 
                pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                rewrite Hh'. reflexivity. }
            assert (v = v_step) as Hv_eq.
             { rewrite <- Hp2_tail. rewrite tail_concat.
               - pose proof (tail_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Ht.
                 rewrite single_path_vertex in Ht. simpl in Ht. injection Ht as Ht'.
                 exact Ht'.
               - exact Hp_prev_valid.
               - apply single_path_valid; exact Hstep.
               - rewrite Htail_prev.
                 pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                 rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                 rewrite Hh'. reflexivity. }
            exists (concat_path p_prev' (single_path u_step v_step e)).
           split.
           { unfold is_path_through_vset. repeat split.
             - exact Hp_new_valid.
             - rewrite head_concat_valid; auto.
             - rewrite tail_concat; auto.
               + rewrite Hv_eq.
                 pose proof (tail_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Ht.
                 rewrite single_path_vertex in Ht. simpl in Ht. injection Ht as Ht'.
                 rewrite Ht'. reflexivity.
               + apply single_path_valid; exact Hstep.
               + rewrite Hp'_tail.
                 pose proof (head_valid _ _ (single_path_valid g u_step v_step e Hstep)) as Hh.
                 rewrite single_path_vertex in Hh. simpl in Hh. injection Hh as Hh'.
                 rewrite Hh'. reflexivity.
             - intros x Hsplit_x.
              destruct Hsplit_x as [q1 [q2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htl]]]]]]].
              (* Split analysis *)
              assert (Hedges: edge_in_path q1 ++ edge_in_path q2 = edge_in_path p_prev' ++ (e :: nil)).
               {
                 apply (f_equal edge_in_path) in Hcat.
                 rewrite concat_path_edge in Hcat.
                 rewrite concat_path_edge in Hcat.
                 rewrite single_path_edge in Hcat.
                 exact Hcat.
               }
              remember (edge_in_path q2) as l_edges eqn:Heq_edges.
              destruct l_edges as [| e0 l] eqn:Heq2.
              *** (* q2 empty *)
                  rewrite Heq_edges in Heq2. symmetry in Heq2.
                  elim Hne2. rewrite is_empty_path_iff_edges_nil; auto.
              *** destruct l as [| e1 l'].
                  **** (* q2 has 1 edge. q2 = single. *)
                       assert (Heq_final: edge_in_path q2 = e0 :: nil).
                        { rewrite <- Heq_edges. try exact Heq2. reflexivity. }
                        try rewrite Heq_final in Hedges.
                       apply app_inj_tail in Hedges. destruct Hedges as [He_eq Hedges]. subst e0.
                       assert (Hp1_eq_prev: q1 = p_prev').
                        { apply path_unique with g; auto.
                          rewrite <- (head_concat_valid _ q2 Hv1).
                          2: { rewrite Hcat. exact Hp_new_valid. }
                          rewrite Hcat.
                          rewrite (head_concat_valid _ (single_path u_step v_step e) Hp'_valid).
                          2: exact Hp_new_valid.
                          reflexivity.
                        }
                       subst q1.
                         rewrite <- Htl. rewrite Hp'_tail.
                         assert (Hin: SetsEle.In u_step (Sets.union vset (Sets.singleton k))).
                         { apply H_vset2.
                           exists p_prev, (single_path u_step v_step e).
                          repeat split.
                          - exact Hp_prev_valid.
                          - apply single_path_valid; auto.
                          - intros Hempty. rewrite is_empty_path_iff_edges_nil in Hempty; auto.
                             destruct (destruct_1n_path p_prev) as [v_base | p_prev_inner u_prev v_prev e_prev] eqn:Hdestruct_prev.
                             { pose proof (destruct_1n_spec _ _ Hp_prev_valid) as Hspec.
                               rewrite Hdestruct_prev in Hspec.
                               subst p_prev.
                               pose proof (head_valid _ _ Hp_prev_valid) as Hh_prev.
                              rewrite empty_path_vertex in Hh_prev. simpl in Hh_prev. injection Hh_prev as Hh_base.
                              rewrite Hh_base in Hhead_prev.
                              pose proof (tail_valid _ _ Hp_prev_valid) as Ht_prev.
                              rewrite empty_path_vertex in Ht_prev. simpl in Ht_prev. injection Ht_prev as Ht_base.
                              rewrite Ht_base in Htail_prev.
                              rewrite Hhead_prev in Htail_prev.
                              symmetry in Htail_prev. contradiction. }
                             { pose proof (destruct_1n_spec _ _ Hp_prev_valid) as Hspec.
                               rewrite Hdestruct_prev in Hspec.
                               destruct Hspec as [_ [_ [_ Heq_prev]]].
                               subst p_prev. rewrite concat_path_edge in Hempty. rewrite single_path_edge in Hempty.
                              destruct (edge_in_path p_prev_inner); discriminate. }
                          - intros Hempty. rewrite is_empty_path_iff_edges_nil in Hempty.
                            2: { apply single_path_valid; exact Hstep. }
                             rewrite single_path_edge in Hempty. discriminate.
                          - exact Htail_prev.
                        }
                        destruct Hin as [H|H].
                        { exact H. }
                        { destruct H; contradiction. }
                   **** (* q2 has > 1 edge *)
                        destruct (@List.exists_last E (e0 :: e1 :: l') ltac:(discriminate)) as [l_pre [last Heq2_split]].
                        assert (Heq_final: edge_in_path q2 = l_pre ++ (last :: nil)).
                        { rewrite <- Heq_edges. try rewrite Heq2. exact Heq2_split. }
                         rewrite Heq2_split in Hedges.
                        rewrite app_assoc in Hedges.
                        apply app_inj_tail in Hedges. destruct Hedges as [He_eq Hedges]. subst last.
                       symmetry in He_eq.
                        pose proof (path_split_by_edges _ _ _ Hp'_valid He_eq) as [p1_split [p2_split [Hp1s [Hp2s [Hcat_split [He1s [He2s Htail_split]]]]]]].
                       assert (Hp1_eq_q1: p1_split = q1).
                        { apply path_unique with g; auto.
                          rewrite <- (head_concat_valid _ p2_split Hp1s).
                          2: { rewrite <- Hcat_split. exact Hp'_valid. }
                          rewrite <- Hcat_split.
                          rewrite <- (head_concat_valid _ q2 Hv1).
                          2: { rewrite Hcat. exact Hp_new_valid. }
                          rewrite Hcat.
                          rewrite (head_concat_valid _ (single_path u_step v_step e) Hp'_valid).
                          2: exact Hp_new_valid.
                          reflexivity.
                        }
                       apply Hp'_vset.
                       exists p1_split, p2_split.
                       repeat split; auto.
                       { intros Hempty. rewrite is_empty_path_iff_edges_nil in Hempty; auto.
                         rewrite He1s in Hempty.
                         rewrite is_empty_path_iff_edges_nil in Hne1; auto. }
                       { intros Hempty. rewrite is_empty_path_iff_edges_nil in Hempty; auto.
                         rewrite He2s in Hempty.
                         rewrite Hempty in Heq2_split. simpl in Heq2_split.
                         destruct l'; discriminate. }
                        { rewrite Hp1_eq_q1. exact Htl. }

            }
            { 
                rewrite concat_path_weight.
                { rewrite concat_path_weight.
                  apply Z_op_plus_le_mono_r; exact Hw.
                }
              }
  }
  destruct Hstep2 as [p2' [Hp2' Hw2]].

  exists p1, p2'.
  split; [|split].
  - exact Hp1.
  - exact Hp2'.
  - apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
    + assert (Z_op_plus_le_mono_l: forall a b c, Z_op_le b c -> Z_op_le (Z_op_plus a b) (Z_op_plus a c)).
      { intros a0 b0 c0 Hle. 
        assert (Hcomm: forall x y, Z_op_plus x y = Z_op_plus y x).
        { intros. destruct x, y; unfold Z_op_plus; simpl; auto. f_equal. apply Z.add_comm. }
        rewrite (Hcomm a0 b0). rewrite (Hcomm a0 c0).
        apply Z_op_plus_le_mono_r. exact Hle.
      }
      apply Z_op_plus_le_mono_l. exact Hw2.
    + exact Hw1.
Qed.

(** 通过 vset 的路径，可以扩展到通过 vset ∪ {k} 的路径集合 *)
Lemma path_vset_mono: forall (u v k: V) (p: P) (vset: V -> Prop),
  is_path_through_vset g p u v vset ->
  is_path_through_vset g p u v (vset ∪ [k]).
Proof.
  intros. destruct H as [Hpath Hvs].
  split; auto.
  intros x Hx.
  apply Hvs in Hx.
  left. auto.
Qed.



Lemma list_app_eq_length {A: Type}: forall (l1 l3 l2 l4: list A),
  length l1 = length l3 ->
  l1 ++ l2 = l3 ++ l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  intros l1. induction l1 as [|x xs IH].
  - destruct l3 as [|y ys].
    + intros. split; auto.
    + intros. simpl in H. discriminate.
  - destruct l3 as [|y ys].
    + intros. simpl in H. discriminate.
    + intros l2 l4 Hlen Hedges.
       simpl in Hlen. apply Nat.succ_inj in Hlen.
       assert (Heq: x = y /\ xs ++ l2 = ys ++ l4).
       {
         split.
         - pose proof (f_equal (fun l => match l with | nil => x | h :: _ => h end) Hedges).
           simpl in H. assumption.
         - pose proof (f_equal (fun l => match l with | nil => nil | _ :: t => t end) Hedges).
           simpl in H. assumption.
       }
       destruct Heq as [Hh Ht].
       assert (xs = ys /\ l2 = l4).
       { apply (IH ys l2 l4); auto. }
       destruct H as [Heq1 Heq2].
       subst. split; auto.
Qed.

Lemma app_eq_prefix {A: Type}: forall (l1 l2 l3 l4: list A),
  l1 ++ l2 = l3 ++ l4 ->
  length l1 <= length l3 ->
  exists l_rest, l3 = l1 ++ l_rest /\ l2 = l_rest ++ l4.
Proof.
  intros l1 l2 l3 l4 H Hlen.
  exists (skipn (length l1) l3).
  assert (Hfirst: firstn (length l1) l3 = l1).
  {
    apply (f_equal (firstn (length l1))) in H.
    rewrite firstn_app in H.
    rewrite firstn_all in H.
    replace (length l1 - length l1) with 0 in H by lia.
    simpl in H.
    rewrite app_nil_r in H.
    rewrite firstn_app in H.
    replace (length l1 - length l3) with 0 in H by lia.
    simpl in H.
    rewrite app_nil_r in H.
    symmetry; auto.
  }
  split.
   - rewrite <- (firstn_skipn (length l1) l3) at 1.
     rewrite Hfirst. reflexivity.
   - rewrite <- (firstn_skipn (length l1) l3) in H.
    rewrite Hfirst in H.
    rewrite <- app_assoc in H.
    apply app_inv_head in H.
    symmetry; auto.
Qed.

Lemma path_concat_vset_k: forall u v k p1 p2 vset,
  is_path_through_vset g p1 u k vset ->
  is_path_through_vset g p2 k v vset ->
  is_path_through_vset g (concat_path p1 p2) u v (vset ∪ [k]).
Proof.
  intros. destruct H as [Hp1 Hvs1]. destruct H0 as [Hp2 Hvs2].
  destruct Hp1 as [Hv1 [Hh1 Ht1]].
  destruct Hp2 as [Hv2 [Hh2 Ht2]].
  assert (Hlink: tail p1 = head p2). { rewrite Ht1. rewrite Hh2. reflexivity. }
  assert (Hvalid_concat: path_valid g (concat_path p1 p2)).
  { apply concat_path_valid; auto. }
  split.
  - unfold is_path. repeat split.
    + exact Hvalid_concat.
    + rewrite head_concat_valid; auto.
    + rewrite tail_concat; auto.
  - intros x Hsplit.
    destruct Hsplit as [q1 [q2 [Hvq1 [Hvq2 [Hne1 [Hne2 [Hcat Htail]]]]]]].
    pose proof (concat_path_edge p1 p2) as Hedges.
    rewrite <- Hcat in Hedges.
    rewrite concat_path_edge in Hedges.
    
    destruct (le_lt_dec (length (edge_in_path q1)) (length (edge_in_path p1))) as [Hle | Hgt].
    + (* q1 <= p1 *)
      destruct (Nat.eq_dec (length (edge_in_path q1)) (length (edge_in_path p1))) as [Heq_len | Hneq_len].
      * (* q1 = p1 *)
        right.
        assert (Hedges_split: edge_in_path q1 = edge_in_path p1 /\ edge_in_path q2 = edge_in_path p2).
        { apply list_app_eq_length; auto. }
        destruct Hedges_split as [Heq1 Heq2].
        assert (q1 = p1).
        { apply path_unique with g; auto.
          transitivity (head (concat_path q1 q2)).
          - symmetry. apply head_concat_valid.
            + exact Hvq1.
            + rewrite Hcat. exact Hvalid_concat.
          - rewrite Hcat. apply head_concat_valid.
            + exact Hv1.
            + exact Hvalid_concat.
        }
        subst q1. rewrite Ht1 in Htail. subst x. 
        unfold SetsEle.In, Sets.singleton. reflexivity.
      * (* q1 < p1 *)
        left. apply Hvs1.
        apply (app_eq_prefix (edge_in_path q1) (edge_in_path q2) (edge_in_path p1) (edge_in_path p2)) in Hedges; [|lia].
        destruct Hedges as [l_rest [Heq_p1 Heq_rest]].
        pose proof (path_split_by_edges p1 (edge_in_path q1) l_rest Hv1 Heq_p1) as [p1a [p1b [Hp1a [Hp1b [Hp1_split [He1 [He2 Htail_p]]]]]]].
        assert (p1a = q1).
        { apply path_unique with g; auto.
          transitivity (head p1).
          - rewrite Hp1_split. symmetry. apply head_concat_valid.
            + exact Hp1a.
            + rewrite <- Hp1_split. exact Hv1.
          - transitivity (head (concat_path p1 p2)).
            + symmetry. apply head_concat_valid.
              * exact Hv1.
              * exact Hvalid_concat.
            + rewrite <- Hcat. apply head_concat_valid.
              * exact Hvq1.
              * rewrite Hcat. exact Hvalid_concat.
        }
        subst p1a.
        exists q1, p1b.
        repeat split.
        -- exact Hp1a.
        -- exact Hp1b.
        -- exact Hne1.
        -- intros Hempty. rewrite is_empty_path_iff_edges_nil in Hempty; auto.
           assert (Hlen_p1: length (edge_in_path p1) = length (edge_in_path q1) + length (edge_in_path p1b)).
           { rewrite Hp1_split. rewrite concat_path_edge. rewrite app_length. reflexivity. }
           rewrite Hempty in Hlen_p1. simpl in Hlen_p1.
           lia.
        -- symmetry. exact Hp1_split.
        -- exact Htail.
    + (* q1 > p1 *)
      left. apply Hvs2.
      symmetry in Hedges.
      apply (app_eq_prefix (edge_in_path p1) (edge_in_path p2) (edge_in_path q1) (edge_in_path q2)) in Hedges; [|lia].
      destruct Hedges as [l_rest [Heq_q1 Heq_rest]].
      pose proof (path_split_by_edges q1 (edge_in_path p1) l_rest Hvq1 Heq_q1) as [q1a [q1b [Hq1a [Hq1b [Hq1_split [He1 [He2 Htail_q]]]]]]].
      assert (q1a = p1).
      { apply path_unique with g; auto.
        transitivity (head q1).
        - rewrite Hq1_split. symmetry. apply head_concat_valid.
          + exact Hq1a.
          + rewrite <- Hq1_split. exact Hvq1.
        - transitivity (head (concat_path q1 q2)).
          + symmetry. apply head_concat_valid.
            * exact Hvq1.
            * rewrite Hcat. exact Hvalid_concat.
          + rewrite Hcat. apply head_concat_valid.
            * exact Hv1.
            * exact Hvalid_concat.
      }
      subst q1a.
      assert (Hne_q1b: ~ is_empty_path q1b).
      { intros H. rewrite is_empty_path_iff_edges_nil in H; auto.
        assert (Hlen_q1: length (edge_in_path q1) = length (edge_in_path p1) + length (edge_in_path q1b)).
        { rewrite Hq1_split. rewrite concat_path_edge. rewrite app_length. reflexivity. }
        rewrite H in Hlen_q1. simpl in Hlen_q1.
        lia.
      }
      
      assert (Htail_q1b: tail q1b = head q2).
      { 
        assert (Htail_q1: tail q1 = tail q1b).
        { rewrite Hq1_split. apply tail_concat; auto. }
        rewrite <- Htail_q1.
        apply tail_eq_head_of_valid_concat; auto.
        rewrite Hcat. exact Hvalid_concat.
      }

      assert (Hp2_split: p2 = concat_path q1b q2).
      { apply path_unique with g; auto.
        - apply concat_path_valid; auto.
        - rewrite head_concat_valid; auto.
          + rewrite <- Hlink. exact Htail_q.
          + apply concat_path_valid; auto.
        - rewrite concat_path_edge; auto.
          rewrite He2. rewrite Heq_rest.
          reflexivity.
      }
      exists q1b, q2.
      repeat split.
      -- exact Hq1b.
      -- exact Hvq2.
      -- exact Hne_q1b.
      -- exact Hne2.
      -- symmetry. exact Hp2_split.
      -- rewrite <- Htail. rewrite Hq1_split. rewrite tail_concat; auto.
Qed.

(** ===== 最短路径基本性质引理 ===== *)

(** 路径集合单调性蕴含最短距离单调性 *)
Lemma min_distance_vset_mono: forall u v k vset w1 w2,
  min_weight_distance_in_vset g u v vset w1 ->
  min_weight_distance_in_vset g u v (vset ∪ [k]) w2 ->
  Z_op_le w2 w1.
Proof.
  intros.
  unfold min_weight_distance_in_vset in *.
  apply (min_default_le Z_op_le (path_weight g) (path_weight g) 
         (fun p => is_path_through_vset g p u v vset)
         (fun p => is_path_through_vset g p u v (vset ∪ [k]))
         None w1 w2); auto.
  intros p Hp.
  exists p. split.
  - apply path_vset_mono. assumption.
  - apply Z_op_le_refl.
Qed.


Lemma min_value_of_subset_with_default_spec {A: Type}:
  forall (P: A -> Prop) (f: A -> option Z) n,
  min_value_of_subset_with_default Z_op_le P f None n <->
  ((forall z, n = Some z -> exists a, P a /\ f a = Some z) /\
   (forall a, P a -> Z_op_le n (f a))).
Proof.
  intros.
  unfold min_value_of_subset_with_default.
  split.
  - intros [[Hmin Hle] | [Hem Heq]].
    + destruct Hmin as [a [[Ha_in Hmin] Heq_n]].
      split.
      * intros z Hz. subst n. exists a. split; auto.
      * intros b Hb. rewrite <- Heq_n. apply Hmin; auto.
    + split.
      * intros z Hz. subst n. discriminate.
      * intros b Hb. subst n. apply Hem; auto.
  - intros [Hex Hmin].
    destruct n as [z|].
    + left. split.
      * destruct (Hex z eq_refl) as [a [Ha_in Heq_a]].
        exists a. split. split; auto.
        intros b Hb. rewrite Heq_a. apply Hmin; auto.
        auto.
      * simpl; auto.
    + right. split; [|auto].
      intros a Ha. apply Hmin; auto.
Qed.

Lemma min_weight_distance_in_vset_stable: forall u v k vset w,
  (u = k \/ v = k) ->
  min_weight_distance_in_vset g u v (vset ∪ [k]) w <->
  min_weight_distance_in_vset g u v vset w.
Proof.
  intros u v k vset w H_end.
  
  assert (Z_op_le_antisym: forall x y, Z_op_le x y -> Z_op_le y x -> x = y).
  { intros x0 y0 Hxy Hyx. destruct x0, y0; simpl in *; try contradiction; try lia; auto. f_equal. lia. }
  
  split; intro H.
  - apply min_value_of_subset_with_default_spec in H.
    apply min_value_of_subset_with_default_spec.
    destruct H as [Hex Hmin].
    split.
    + intros z Hz.
      destruct (Hex z Hz) as [p [Hp_valid Hp_w]].
      destruct H_end as [Heq_u | Heq_v].
      * subst u.
        assert (Hin_k: In k (vertex_in_path p)).
        { 
          destruct Hp_valid as [[Hpv [Hh _]] _]. 
          pose proof (head_valid g p Hpv) as Hhv.
          rewrite Hh in Hhv.
          destruct (vertex_in_path p) eqn:Hvp.
          - simpl in Hhv. discriminate.
          - simpl in Hhv. injection Hhv as Hhv'. subst v0.
            simpl. left. reflexivity.
        }
        pose proof (path_decompose_at_vertex _ _ _ _ _ Hp_valid Hin_k) as [p1 [p2 [Hp1 [Hp2 Hw_sum]]]].
        exists p2.
        split.
        -- exact Hp2.
        -- apply Z_op_le_antisym.
           { rewrite Hp_w in Hw_sum.
             apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
              { assert (Hw_p1: Z_op_le (Some 0%Z) (path_weight g p1)).
                 { destruct Hp1 as [[Hv1 [Hh1 Ht1]] _].
                   apply nnc; [ exact Hv1 | rewrite Hh1, Ht1; reflexivity ]. }
                 destruct (path_weight g p1) as [w1|].
                 2: { destruct (path_weight g p2); simpl; unfold Z_op_plus; simpl; unfold Z_op_le; trivial. }
                 destruct (path_weight g p2) as [w2|].
                 2: { simpl; unfold Z_op_plus; simpl; unfold Z_op_le; trivial. }
                 simpl in *. unfold Z_op_le in Hw_p1. lia. }
              { exact Hw_sum. } }
           { rewrite Hz in Hmin.
              apply Hmin.
              apply path_vset_mono.
              exact Hp2. }
      * subst v.
        assert (Hin_k: In k (vertex_in_path p)).
        { 
          destruct Hp_valid as [[Hpv [_ Ht]] _].
          pose proof (tail_valid g p Hpv) as Htv.
          rewrite Ht in Htv.
          unfold tl_error in Htv.
          symmetry in Htv.
          apply nth_error_In in Htv.
          exact Htv.
        }
        pose proof (path_decompose_at_vertex _ _ _ _ _ Hp_valid Hin_k) as [p1 [p2 [Hp1 [Hp2 Hw_sum]]]].
        exists p1.
        split.
        -- exact Hp1.
        -- rewrite <- Hp_w.
           apply Z_op_le_antisym.
           { apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
              { assert (Hw_p2: Z_op_le (Some 0%Z) (path_weight g p2)).
                 { destruct Hp2 as [[Hv2 [Hh2 Ht2]] _].
                   apply nnc; [ exact Hv2 | rewrite Hh2, Ht2; reflexivity ]. }
                 destruct (path_weight g p1) as [w1|].
                  { destruct (path_weight g p2) as [w2|].
                    { simpl in *. unfold Z_op_le in Hw_p2. lia. }
                    { simpl; unfold Z_op_plus; unfold Z_op_le; auto. } }
                  { simpl; unfold Z_op_plus; unfold Z_op_le; auto. } }
              { exact Hw_sum. } }
           { rewrite Hp_w. rewrite <- Hz.
              apply Hmin.
              apply path_vset_mono.
              exact Hp1. }
    + intros p Hp.
      apply Hmin.
      apply path_vset_mono.
      exact Hp.
  - assert (H_rev: min_weight_distance_in_vset g u v (vset ∪ [k]) w).
    {
      apply min_value_of_subset_with_default_spec.
      split.
      - apply min_value_of_subset_with_default_spec in H.
        destruct H as [Hex Hmin].
        intros z Hz.
        destruct (Hex z Hz) as [p [Hp_valid Hp_w]].
        exists p. split; auto.
        apply path_vset_mono.
        exact Hp_valid.
      - intros p Hp.
        destruct H_end as [Heq_u | Heq_v].
        + subst u.
          assert (Hin_k: In k (vertex_in_path p)).
          { destruct Hp as [[Hpv [Hh _]] _]. 
            pose proof (head_valid g p Hpv) as Hhv.
            rewrite Hh in Hhv.
            destruct (vertex_in_path p) eqn:Hvp.
            - simpl in Hhv. discriminate.
            - simpl in Hhv. injection Hhv as Hhv'. subst v0.
              simpl. left. reflexivity. }
          pose proof (path_decompose_at_vertex _ _ _ _ _ Hp Hin_k) as [p1 [p2 [Hp1 [Hp2 Hw_sum]]]].
          apply min_value_of_subset_with_default_spec in H.
          destruct H as [_ Hmin].
          specialize (Hmin p2 Hp2).
          apply Z_op_le_trans with (y := path_weight g p2).
          { exact Hmin. }
          { apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
            - assert (Hw_p1: Z_op_le (Some 0%Z) (path_weight g p1)).
              { destruct Hp1 as [[Hv1 [Hh1 Ht1]] _]. apply nnc; [exact Hv1|rewrite Hh1, Ht1; reflexivity]. }
              destruct (path_weight g p1) as [w1|]; destruct (path_weight g p2) as [w2|]; simpl in *; try lia; try auto; try (unfold Z_op_le in *; lia).
            - exact Hw_sum.
          }
        + subst v.
          assert (Hin_k: In k (vertex_in_path p)).
          { destruct Hp as [[Hpv [_ Ht]] _].
            pose proof (tail_valid g p Hpv) as Htv.
            rewrite Ht in Htv. unfold tl_error in Htv.
            symmetry in Htv.
            apply nth_error_In in Htv. exact Htv. }
          pose proof (path_decompose_at_vertex _ _ _ _ _ Hp Hin_k) as [p1 [p2 [Hp1 [Hp2 Hw_sum]]]].
          apply min_value_of_subset_with_default_spec in H.
          destruct H as [_ Hmin].
          specialize (Hmin p1 Hp1).
          apply Z_op_le_trans with (y := path_weight g p1).
          { exact Hmin. }
          { apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
            - assert (Hw_p2: Z_op_le (Some 0%Z) (path_weight g p2)).
              { destruct Hp2 as [[Hv2 [Hh2 Ht2]] _]. apply nnc; [exact Hv2|rewrite Hh2, Ht2; reflexivity]. }
              destruct (path_weight g p1) as [w1|]; destruct (path_weight g p2) as [w2|]; simpl in *; try lia; try auto; try (unfold Z_op_le in *; lia).
            - exact Hw_sum.
          }
    }
    exact H_rev.
Qed.


Lemma floyd_relaxation_correct: 
  forall (i j k: V) (vset: V -> Prop) (w_ik w_kj w_ij: option Z),
    min_weight_distance_in_vset g i k vset w_ik -> 
    min_weight_distance_in_vset g k j vset w_kj -> 
    min_weight_distance_in_vset g i j vset w_ij ->
    min_weight_distance_in_vset g i j (vset ∪ [k]) (Z_op_min w_ij (Z_op_plus w_ik w_kj)).
Proof.
  intros.
  unfold min_weight_distance_in_vset in *.
  rewrite min_value_of_subset_with_default_spec in H.
  rewrite min_value_of_subset_with_default_spec in H0.
  rewrite min_value_of_subset_with_default_spec in H1.
  apply min_value_of_subset_with_default_spec.
  split.
  - (* Existence *)
    intros z Hz.
    destruct w_ij as [z_ij|], w_ik as [z_ik|], w_kj as [z_kj|]; simpl in Hz.
    + destruct (Z.min_spec z_ij (z_ik + z_kj)) as [[Hle Heq] | [Hle Heq]]; rewrite Heq in Hz; injection Hz as Hz'; subst z.
      * destruct H1 as [H1_reach _]. specialize (H1_reach _ eq_refl).
        destruct H1_reach as [p [Hp_valid Hp_weight]].
        exists p. split; auto. apply path_vset_mono; auto.
      * destruct H as [H_ik_reach _]. specialize (H_ik_reach _ eq_refl).
        destruct H0 as [H_kj_reach _]. specialize (H_kj_reach _ eq_refl).
        destruct H_ik_reach as [p1 [Hp1_valid Hp1_weight]].
        destruct H_kj_reach as [p2 [Hp2_valid Hp2_weight]].
        exists (concat_path p1 p2).
        split.
        -- apply path_concat_vset_k; auto.
        -- destruct Hp1_valid as [[Hv1 [Hh1 Ht1]] Hi1]. destruct Hp2_valid as [[Hv2 [Hh2 Ht2]] Hi2].
            rewrite path_concat_weight by (assumption || (rewrite Ht1, Hh2; reflexivity)).
            rewrite Hp1_weight, Hp2_weight. reflexivity.
    (* Case 2: S, S, N *)
    + injection Hz as Hz'; subst z.
      destruct H1 as [H1_reach _]. specialize (H1_reach _ eq_refl).
      destruct H1_reach as [p [Hp_valid Hp_weight]].
      exists p. split; auto. apply path_vset_mono; auto.
    (* Case 3: S, N, S *)
    + injection Hz as Hz'; subst z.
      destruct H1 as [H1_reach _]. specialize (H1_reach _ eq_refl).
      destruct H1_reach as [p [Hp_valid Hp_weight]].
      exists p. split; auto. apply path_vset_mono; auto.
    (* Case 4: S, N, N *)
    + injection Hz as Hz'; subst z.
      destruct H1 as [H1_reach _]. specialize (H1_reach _ eq_refl).
      destruct H1_reach as [p [Hp_valid Hp_weight]].
      exists p. split; auto. apply path_vset_mono; auto.
    (* Case 5: N, S, S *)
    + destruct H as [H_ik_reach _]. specialize (H_ik_reach _ eq_refl).
      destruct H0 as [H_kj_reach _]. specialize (H_kj_reach _ eq_refl).
      destruct H_ik_reach as [p1 [Hp1_valid Hp1_weight]].
      destruct H_kj_reach as [p2 [Hp2_valid Hp2_weight]].
      simpl in Hz. injection Hz as Hz'; subst z.
      exists (concat_path p1 p2).
      split.
      -- apply path_concat_vset_k; auto.
      -- destruct Hp1_valid as [[Hv1 [Hh1 Ht1]] Hi1]. destruct Hp2_valid as [[Hv2 [Hh2 Ht2]] Hi2].
         rewrite path_concat_weight by (assumption || (rewrite Ht1, Hh2; reflexivity)).
         rewrite Hp1_weight, Hp2_weight. reflexivity.
    (* Case 6: N, S, N *)
    + simpl in Hz. discriminate.
    (* Case 7: N, N, S *)
    + simpl in Hz. discriminate.
    (* Case 8: N, N, N *)
    + simpl in Hz. discriminate.
      
  - (* Minimality *)
    intros p Hp_valid.
    destruct (classic (In k (vertex_in_path p))).
    + (* Visits k *)
      pose proof (path_decompose_at_vertex _ _ _ _ _ Hp_valid H2) as [p1 [p2 [Hp1 [Hp2 Hw]]]].
      destruct w_ik as [z_ik|].
      * destruct H as [_ H_ik_min]. specialize (H_ik_min p1 Hp1).
        destruct w_kj as [z_kj|].
        -- destruct H0 as [_ H_kj_min]. specialize (H_kj_min p2 Hp2).
           simpl.
           destruct w_ij as [z_ij|].
           ++ apply Z_op_le_trans with (y := Some (z_ik + z_kj)%Z).
              ** simpl. apply Z.le_min_r.
              ** apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
                 *** simpl. destruct (path_weight g p1); [|exact I]. destruct (path_weight g p2); [|exact I]. simpl in *. lia.
                 *** exact Hw.
           ++ (* w_ij = None. min is sum. *)
              apply Z_op_le_trans with (y := Z_op_plus (path_weight g p1) (path_weight g p2)).
              ** simpl. destruct (path_weight g p1); [|exact I]. destruct (path_weight g p2); [|exact I]. simpl in *. lia.
              ** assumption.
        -- (* w_kj is None. *)
           destruct H0 as [_ H_min].
           specialize (H_min p2 Hp2).
           destruct (path_weight g p2) as [w2|].
           ++ unfold Z_op_le in H_min. contradiction.
           ++ destruct (path_weight g p1); simpl in Hw; destruct (path_weight g p); try (unfold Z_op_le in Hw; contradiction); destruct w_ij; simpl; auto.
      * (* w_ik is None *)
         destruct H as [_ H_min].
         specialize (H_min p1 Hp1).
         destruct (path_weight g p1) as [w1|].
         -- unfold Z_op_le in H_min. contradiction.
          -- unfold Z_op_plus in Hw; simpl in Hw. destruct (path_weight g p); [unfold Z_op_le in Hw; simpl in Hw; inversion Hw|].
            destruct w_ij; simpl; auto.
    + (* Doesn't visit k *)
      assert (is_path_through_vset g p i j vset).
      {
         destruct Hp_valid as [Hpath Hinter].
         split; [assumption|].
         intros x Hx.
         specialize (Hinter x Hx).
         destruct Hinter as [|Hk]; [assumption|].
         unfold Sets.singleton, SetsEle.In in Hk. subst. exfalso. apply H2.
         destruct Hx as [p1 [p2 [Hv1 [Hv2 [Hne1 [Hne2 [Hcat Htail]]]]]]].
         rewrite <- Hcat.
         rewrite concat_path_vertex.
         apply in_app_iff. left.
         pose proof (tail_valid g p1 Hv1) as Htv.
          unfold tl_error in Htv.
          symmetry in Htv.
           apply nth_error_In in Htv.
           rewrite Htail in Htv.
           exact Htv.
      }
      destruct H1 as [_ H_ij_min]. specialize (H_ij_min p H3).
      apply Z_op_le_trans with (y := w_ij); [|exact H_ij_min].
       destruct w_ij as [z_ij|], w_ik as [z_ik|], w_kj as [z_kj|]; simpl; auto; try apply Z.le_min_l; try apply Z.le_refl.
Qed.

End floyd.
