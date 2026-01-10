
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Lemma list_snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  Search nil "last".
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.
