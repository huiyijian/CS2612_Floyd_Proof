(** This library aims to express abstract maps using Coq function type. *)
(** Inspired by `Maps` from Software Foundation Volumn 1, 
    https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
*)
Require Export Coq.Classes.EquivDec.

Section total_map.
Context {K V: Type} `{EqDec K eq}.

Definition t_empty (v: V): K -> V := fun _ => v.

Definition t_set (m: K -> V) (k: K) (v: V): K -> V :=
  fun k' => if k == k' then v else m k'.

Lemma t_update_eq: forall (m: K -> V) k v,
  (t_set m k v) k = v.
Proof.
  intros. unfold t_set.
  destruct (equiv_dec k k) as [Heq | Hneq].
  - reflexivity.
  - exfalso; apply Hneq; reflexivity.
Qed.

Lemma t_update_neq: forall (m: K -> V) k v k',
  k <> k' ->
  (t_set m k v) k' = m k'.
Proof.
  intros. unfold t_set.
  destruct (equiv_dec k k') as [Heq | Hneq].
  - subst. contradiction.
  - reflexivity.
Qed.

End total_map.

Declare Scope map_scope.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity) : map_scope.

Notation "x '!->' v ';' m" := (t_set m x v)
  (at level 100, v at next level, right associativity) : map_scope.
