
Require Import Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import MaxMinLib.MaxMin.


Section Z.

Theorem Z_le_total: forall x y, {Z.le x y} + {Z.le y x}.
Proof. intros. destruct (Z_le_dec x y); [left | right]; lia. Qed.

#[export] Instance Zle_TotalOrder: TotalOrder Z.le := {
  le_refl := Z.le_refl;
  le_trans := Z.le_trans;
  le_antisym := Z.le_antisymm;
  le_total := Z_le_total;
}.

End Z.

Section Nat.

Theorem Nat_le_total: forall x y, {Nat.le x y} + {Nat.le y x}.
Proof. intros. destruct (le_ge_dec x y); [left | right]; auto. Qed. 

#[export] Instance NatLe_TotalOrder: TotalOrder Nat.le := {
  le_refl := Nat.le_refl;
  le_trans := Nat.le_trans;
  le_antisym := Nat.le_antisymm;
  le_total := Nat_le_total;
}.

End Nat.

Section Nat_op.

Definition Nat_op_le: option nat -> option nat -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Nat.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Nat_op_plus: option nat -> option nat -> option nat :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Nat_op_min: option nat -> option nat -> option nat :=
  fun x y => match x, y with
  | Some x, Some y => Some (min x y)
  | None, _ => y
  | _, None => x
  end.

Theorem Nat_op_le_refl: forall x, Nat_op_le x x.
Proof. intros. destruct x; simpl; auto. Qed.

Theorem Nat_op_le_trans: forall x y z, Nat_op_le x y -> Nat_op_le y z -> Nat_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Nat_op_le_antisym: forall x y, Nat_op_le x y -> Nat_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed.

Theorem Nat_op_le_total: forall x y, {Nat_op_le x y} + {Nat_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Nat_le_total.
Qed.

#[export] Instance Nat_op_le_TotalOrder: TotalOrder Nat_op_le := {
  le_refl := Nat_op_le_refl;
  le_trans := Nat_op_le_trans;
  le_antisym := Nat_op_le_antisym;
  le_total := Nat_op_le_total
}.

End Nat_op.

Section Z_op.

Local Open Scope Z.
Definition Z_op_le: option Z -> option Z -> Prop := 
  fun x y => match x, y with
  | Some x, Some y => Z.le x y
  | _, None => True
  | None, _ => False
  end.

Definition Z_op_plus: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some x, Some y => Some (x + y)
  | None, _ => None
  | _, None => None
  end.

Definition Z_op_min: option Z -> option Z -> option Z :=
  fun x y => match x, y with
  | Some x, Some y => Some (Z.min x y)
  | None, _ => y
  | _, None => x
  end.

Theorem Z_op_le_refl: forall x, Z_op_le x x.
Proof. intros. destruct x; simpl; lia. Qed.

Theorem Z_op_le_trans: forall x y z, Z_op_le x y -> Z_op_le y z -> Z_op_le x z. 
Proof. intros. destruct x, y, z; simpl in *; lia. Qed. 

Theorem Z_op_le_antisym: forall x y, Z_op_le x y -> Z_op_le y x -> x = y.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  - f_equal; lia.
  - exfalso; auto.
  - exfalso; auto.
Qed. 

Theorem Z_op_le_total: forall x y, {Z_op_le x y} + {Z_op_le y x}.
Proof. 
  intros. destruct x, y; simpl in *; auto. 
  apply Z_le_total.
Qed.

#[export] Instance Z_op_le_TotalOrder: TotalOrder Z_op_le := {
  le_refl := Z_op_le_refl;
  le_trans := Z_op_le_trans;
  le_antisym := Z_op_le_antisym;
  le_total := Z_op_le_total
}.

End Z_op.
