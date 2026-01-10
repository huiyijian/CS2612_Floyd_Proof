Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic.

Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope monad.
Export CPO_lift.
Local Open Scope order_scope.

(*************************************************************************************************************)
(**********************************          monad program registerd         *********************************)
(**********************************                program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)

#[export] Instance oLub_program {Σ A: Type} : OmegaLub (MonadErr.M Σ A) :=
  ProgramPO.indexed_union.

#[export] Instance bot_program {Σ A: Type} : Bot (MonadErr.M Σ A) :=
  ProgramPO.bot.

#[export] Instance oCPO_program {Σ A: Type} : CompletePartialOrder_Setoid (MonadErr.M Σ A).
Proof.
  split.
  + apply program_PO.
  + unfold seq_mono, seq_least_upper_bound, seq_upper_bound.
    unfold omega_lub, order_rel, program_order, oLub_program; simpl.
    intros T H.
    split.
    - intros n.
      specialize (H n) as [H H1].
      constructor;simpl in *. 
      * sets_unfold. intros.
        exists n.
        tauto.
      * sets_unfold. intros.
        exists n.
        tauto.
    - intros a H0.
      constructor;simpl in *.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [H0 _]. eapply H0;eauto.
      * sets_unfold.
        intros.
        destruct H1 as [n ?].
        specialize (H0 n) as [_ H0]. eapply H0;eauto.
  + unfold least_element.
    unfold bot, order_rel, program_order, bot_program; simpl.
    intros a.
    constructor;simpl.
    sets_unfold. 
    tauto.
    sets_unfold. 
    tauto.
Qed.

(*************************************************************************************************************)
(**********************************     lift monad program registerd         *********************************)
(**********************************           B -> program Σ A               *********************************)
(**********************************   class                                  *********************************)
(**********************************     1 : Order                            *********************************)
(**********************************       1.1 : Transitive                   *********************************)
(**********************************       1.2 : Reflexiitive                 *********************************)
(**********************************     2 : PartialOrder_Setoid              *********************************)
(**********************************     3 : OmegaCompletePartialOrder_Setoid *********************************)
(*************************************************************************************************************)
#[export] Instance Transitive_lift  {A: Type} {B: Type} {RB: Order B} {TB: Transitive (@order_rel B _) } 
  : Transitive (@order_rel (A -> B) _ ).
Proof.
  unfold Transitive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  etransitivity;eauto.
Qed.

#[export] Instance Reflexive_lift  {A: Type} {B: Type} {RB: Order B} {ReflB: Reflexive (@order_rel B _) } 
  : Reflexive (@order_rel (A -> B) _ ).
Proof.
  unfold Reflexive, order_rel, R_lift, LiftConstructors.lift_rel2.
  intros.
  reflexivity.
Qed.



(*************************************************************************************************************)
(**********************************     mono and continuous_lemmas           *********************************)
(*************************************************************************************************************)
Section mono_and_continuous_lemmas.
  Import MonadErr.
  Import MonadNotation.
  Context {Σ: Type}.

  Notation " ⋃  a " := (omega_lub a): order_scope.

  Definition increasing {A: Type} {RA: Order A } (T : nat -> A):= @seq_mono A RA T.

  Definition mono {A: Type} {RA: Order A}  {B: Type} {RB: Order B}  
    (f : A -> B) := Proper (order_rel ==> order_rel) f.
  Definition continuous {A: Type} {RA: Order A} {oLubA: OmegaLub A}
          {B: Type} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := @seq_continuous  A RA oLubA B EB oLubB f.
  Definition mono_cont {A: Type} {RA: Order A} {oLubA: OmegaLub A} {B: Type} {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B}
    (f : A -> B) := mono f /\ continuous f.

  Lemma BW_fixpoint'{A: Type} {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}
        {equ: Equivalence equiv}
        {CPO: CompletePartialOrder_Setoid A} f:
    mono_cont f ->
    BW_fix f == f (BW_fix f).
  Proof.
    unfold mono_cont; intros.
    apply BourbakiWitt_fixpoint; tauto.
  Qed.

  Lemma increasing_program_plus : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    increasing c -> c n <= c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le : forall {A B:Type} (m n: nat) (c: nat -> A -> program Σ B), 
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus;auto.
  Qed.

  Lemma increasing_program_plus' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    increasing c -> c n <= c (n + m).
  Proof.
    induction m;intros.
    - assert (n + 0 = n) by lia. rewrite H0.
      reflexivity.
    - assert (n + S m = S (n + m)) by lia.
      rewrite H0.
      transitivity (c (n + m)).
      eapply IHm;auto.
      eapply H.
  Qed. 

  Lemma increasing_program_le' : forall {B:Type} (m n: nat) (c: nat -> program Σ B), 
    (n <= m)%nat ->  increasing c  -> c n <= c m.
  Proof.
    intros.
    assert (m = n + (m - n)) by lia.
    rewrite H1.
    eapply increasing_program_plus' ;auto.
  Qed.

  Lemma mono_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono (fun W => f W a)) ->
      mono f.
  Proof.
    unfold mono, Proper, respectful.
    unfold order_rel, R_lift, LiftConstructors.lift_rel2, order_rel.
    sets_unfold; intros.
    eapply H; auto.
  Qed.

  Lemma mono_bind {A B C D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful.
    intros.
    specialize (H x y H1).
    inversion H. 
    constructor; unfold_monad. 
    - unfold nrm_nrm.
      intros s0 b s2 [d [s1 [Hc1 Hc2]]].
      apply nrmle in Hc1.
      specialize (H0 d x y H1).
      inversion H0.
      apply nrmle0 in Hc2.
      exists d, s1.
      tauto.
    - unfold nrm_err; sets_unfold.
      intros s [? | [d [s1 [Hn He]]]].
      + apply errle in H2; tauto.
      + specialize (H0 d x y H1).
        inversion H0.
        apply nrmle in Hn.
        apply errle0 in He.
        right; exists d, s1.
        tauto.
  Qed.

  Lemma mono_bind' {B C D: Type}:
    forall  (c1: (program Σ B) -> program Σ D) (c2: (program Σ B) -> D -> program Σ C),
      mono c1 ->
      (forall d, mono (fun W => c2 W d)) -> 
      mono (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful.
    intros.
    specialize (H x y H1).
    inversion H. 
    constructor; simpl; unfold_monad. 
    - unfold nrm_nrm.
      intros s0 b s2 [d [s1 [Hc1 Hc2]]].
      apply nrmle in Hc1.
      specialize (H0 d x y H1).
      inversion H0.
      apply nrmle0 in Hc2.
      exists d, s1.
      tauto.
    - unfold nrm_err; sets_unfold.
      intros s [? | [d [s1 [Hn He]]]].
      + apply errle in H2; tauto.
      + specialize (H0 d x y H1).
        inversion H0.
        apply nrmle in Hn.
        apply errle0 in He.
        right; exists d, s1.
        tauto.
  Qed.

  Lemma mono_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    intros.
    specialize (H x y H1).
    specialize (H0 x y H1).
    constructor; simpl; sets_unfold.
    - intros s0 d s1 [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
    - intros s [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
  Qed.

  Lemma mono_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      mono c1 -> mono c2 ->
      mono (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono, Proper, respectful, choice.
    intros.
    specialize (H x y H1).
    specialize (H0 x y H1).
    constructor; simpl; sets_unfold.
    - intros s0 d s1 [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
    - intros s [? | ?].
      + apply H in H2; tauto.
      + apply H0 in H2; tauto.
  Qed.

  Lemma continuous_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, continuous (fun W => f W a)) ->
      continuous f.
  Proof.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; intros; apply H in H1; tauto.
  Qed.

  Lemma continuous_const {A B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: A -> program Σ B) => f).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; 
    unfold omega_lub, oLub_program, ProgramPO.indexed_union;
    sets_unfold; simpl; intros.
    exists 0; auto.
    destruct H0; auto.
    exists 0; auto.
    destruct H0; auto.
  Qed.

  Lemma continuous_const' {B C: Type}:
    forall (f: program Σ C),
      continuous (fun (W: program Σ B) => f).
  Proof.
    intros.
    unfold continuous, seq_continuous, seq_mono.
    intros.
    do 2 constructor; 
    unfold omega_lub, oLub_program, ProgramPO.indexed_union;
    sets_unfold; simpl; intros.
    exists 0; auto.
    destruct H0; auto.
    exists 0; auto.
    destruct H0; auto.
  Qed.

  Lemma continuous_bind {A B C D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, seq_continuous, Proper, respectful.
    unfold_monad; intros.
    specialize (H0 T H3).
    constructor; 
    unfold nrm_nrm, nrm_err;
    simpl;
    sets_unfold; [intros s0 b s2 | intros s]; split.
    - intros [d [s1 [Hc1 Hc2]]].
      specialize (H2 d T H3).
      apply H0 in Hc1; simpl in Hc1; sets_unfold in Hc1.
      apply H2 in Hc2; simpl in Hc2; sets_unfold in Hc2.
      destruct Hc1 as [i1 Hc1].
      destruct Hc2 as [i2 Hc2].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s1.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le; auto.
      + exists i1, d, s1.
        apply leb_complete_conv in Heq.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le; [lia| auto].
    - intros [i [d [s1 [Hc1 Hc2]]]].
      exists d, s1.
      split.
      apply H0.
      econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
    - intros [Hc1 | [d [s1 [Hc1 Hc2]]]].
      {
        apply H0 in Hc1.
        inversion Hc1.
        exists x; tauto.
      }
      apply H0 in Hc1.
      apply H2 in Hc2; auto.
      inversion Hc1.
      inversion Hc2; rename x0 into y.
      destruct (x <=? y) eqn:Heq.
      + apply leb_complete in Heq.
        exists y; right.
        exists d, s1.
        split; auto.
        apply H with (x:= T x); auto.
        apply increasing_program_le; auto.
      + apply leb_complete_conv in Heq.
        exists x; right.
        exists d, s1.
        split; auto.
        apply H1 with (x:= T y); auto.
        apply increasing_program_le; [lia | auto].
    - intros [i [Hc1 | [d [s1 [Hc1 Hc2]]]]].
      {
        left; apply H0.
        econstructor; eauto.
      }
      right; exists d, s1.
      split.
      apply H0; econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
  Qed.

  Lemma continuous_bind' {B C D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ C),
      mono c1 -> continuous c1 ->
      (forall d, mono (fun W => c2 W d)) -> (forall d, continuous (fun W => c2 W d)) -> 
      continuous (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono, continuous, seq_continuous, Proper, respectful.
    unfold_monad; intros.
    specialize (H0 T H3).
    constructor; 
    unfold nrm_nrm, nrm_err;
    simpl;
    sets_unfold; [intros s0 b s2 | intros s]; split.
    - intros [d [s1 [Hc1 Hc2]]].
      specialize (H2 d T H3).
      apply H0 in Hc1; simpl in Hc1; sets_unfold in Hc1.
      apply H2 in Hc2; simpl in Hc2; sets_unfold in Hc2.
      destruct Hc1 as [i1 Hc1].
      destruct Hc2 as [i2 Hc2].
      destruct (i1 <=? i2) eqn:Heq.
      + exists i2, d, s1.
        apply leb_complete in Heq.
        split; auto.
        apply H with (x:=(T i1)); auto.
        apply increasing_program_le'; auto.
      + exists i1, d, s1.
        apply leb_complete_conv in Heq.
        split; auto.
        apply H1 with (x:=(T i2)); eauto.
        apply increasing_program_le'; [lia| auto].
    - intros [i [d [s1 [Hc1 Hc2]]]].
      exists d, s1.
      split.
      apply H0.
      econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
    - intros [Hc1 | [d [s1 [Hc1 Hc2]]]].
      {
        apply H0 in Hc1.
        inversion Hc1.
        exists x; tauto.
      }
      apply H0 in Hc1.
      apply H2 in Hc2; auto.
      inversion Hc1.
      inversion Hc2; rename x0 into y.
      destruct (x <=? y) eqn:Heq.
      + apply leb_complete in Heq.
        exists y; right.
        exists d, s1.
        split; auto.
        apply H with (x:= T x); auto.
        apply increasing_program_le'; auto.
      + apply leb_complete_conv in Heq.
        exists x; right.
        exists d, s1.
        split; auto.
        apply H1 with (x:= T y); auto.
        apply increasing_program_le'; [lia | auto].
    - intros [i [Hc1 | [d [s1 [Hc1 Hc2]]]]].
      {
        left; apply H0.
        econstructor; eauto.
      }
      right; exists d, s1.
      split.
      apply H0; econstructor; eauto.
      apply H2; auto.
      econstructor; eauto.
  Qed.

  Lemma continuous_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, seq_continuous.
    unfold choice; intros.
    specialize (H T H1).
    specialize (H0 T H1).
    do 2 constructor; simpl; sets_unfold.
    - intros [? | ?].
      + apply H in H2.
        inversion H2.
        eexists; eauto.
      + apply H0 in H2.
        inversion H2.
        eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
    - intros [? | ?].
      apply H in H2.
      inversion H2.
      eexists; eauto.
      apply H0 in H2.
      inversion H2.
      eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
  Qed.

  Lemma continuous_choice' {B D: Type}:
    forall (c1 c2: program Σ B -> program Σ D),
      continuous c1 -> continuous c2 ->
      continuous (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold continuous, seq_continuous.
    unfold choice; intros.
    specialize (H T H1).
    specialize (H0 T H1).
    do 2 constructor; simpl; sets_unfold.
    - intros [? | ?].
      + apply H in H2.
        inversion H2.
        eexists; eauto.
      + apply H0 in H2.
        inversion H2.
        eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
    - intros [? | ?].
      apply H in H2.
      inversion H2.
      eexists; eauto.
      apply H0 in H2.
      inversion H2.
      eexists; eauto.
    - intros [i [? | ?]].
      left; apply H.
      econstructor; eauto.
      right; apply H0.
      econstructor; eauto.
  Qed.

  Lemma mono_cont_intro {A B: Type}:
    forall (f: (A -> program Σ B) -> A -> program Σ B),
      (forall a, mono_cont (fun W => f W a)) ->
      mono_cont f.
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_intro.
      intros; apply H.
    - apply continuous_intro.
      intros; apply H.
  Qed.

  Lemma mono_cont_const {A B C: Type}:
    forall (f: program Σ C),
      mono_cont (fun (W: A -> program Σ B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const.
  Qed.

  Lemma mono_cont_const' {B C: Type}:
    forall (f: program Σ C),
      mono_cont (fun (W:program Σ B) => f).
  Proof.
    intros.
    unfold mono_cont.
    split; try easy.
    apply continuous_const'.
  Qed.

  Lemma mono_cont_bind {A B C D: Type}:
    forall  (c1: (A -> program Σ B) -> program Σ D) (c2: (A -> program Σ B) -> D -> program Σ C),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: A -> program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind; try tauto.
      intros d; apply H0.
    - apply continuous_bind; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_bind' {B C D: Type}:
    forall  (c1: program Σ B -> program Σ D) (c2: program Σ B -> D -> program Σ C),
      mono_cont c1 ->
      (forall d, mono_cont (fun W => c2 W d)) ->
      mono_cont (fun (W: program Σ B) => bind (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_bind'; try tauto.
      intros d; apply H0.
    - apply continuous_bind'; try tauto;
      intros d; apply H0.
  Qed.

  Lemma mono_cont_choice {A B D: Type}:
    forall (c1 c2: (A -> program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice; tauto.
    - apply continuous_choice; tauto.
  Qed.

  Lemma increasing_mono_increasing:
  forall {A B: Type} {RA: Order A} {RB: Order B}
         (f: A -> B)
         (l: nat -> A),
    increasing l -> mono f -> increasing (fun n => f (l n)).
  Proof.
    intros.
    unfold increasing, seq_mono. intros.
    apply H0. apply H.
  Qed.

  Lemma mono_BW_fix {A B: Type} {RA: Order A} {RB: Order B} {EB: Equiv B}
    {oLubB: OmegaLub B} {BotB: Bot B}
    {equ: Equivalence equiv}
    {CPO: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono (f a)) ->
      (forall b, mono (fun W => f W b)) ->
      mono (fun W => (BW_fix (f W))).
  Proof.
    unfold mono in *.
    unfold Proper, respectful in *.
    intros.
    apply BourbakiWitt_fixpoint_monotonic.
    - intros b1 b2 Hb. apply (H x b1 b2 Hb).
    - intros b1 b2 Hb. apply (H y b1 b2 Hb).
    - intros.
      transitivity (f y a).
      + apply H0; auto.
      + apply (H y); auto.
  Qed.

  Lemma BW_fix_seq_cont_general {A B} {RA: Order A} 
    {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {CPOA: CompletePartialOrder_Setoid A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOB: CompletePartialOrder_Setoid B}:
  forall (f: A -> B -> B)
          (Hf_mono: Proper (order_rel ==> order_rel ==> order_rel) f)
          (Hfa_sseq: forall a, continuous (f a))
          (Hf_sseq: forall b, continuous (fun a => f a b)),
    continuous (fun a: A => BW_fix (f a)).
  Proof.
    intros. intros T HT.
    apply antisymmetricity_setoid.
    - unfold BW_fix at 1.
      apply limit_smaller_iff.
      + apply (@iter_bot_mono B _ _ _ _ CPOB (f (omega_lub T))).
        intros x y Hxy. apply Hf_mono. reflexivity. apply Hxy.
      + intros n.
        induction n.
        * simpl. apply CPO_least.
        * simpl.
          transitivity (f (omega_lub T) (omega_lub (fun n => BW_fix (f (T n))))).
          { apply Hf_mono. reflexivity. apply IHn. }
          transitivity (omega_lub (fun n => f (T n) (omega_lub (fun k => BW_fix (f (T k)))))).
          { apply PO_Reflexive_Setoid. apply Hf_sseq. apply HT. }
          apply limit_smaller_iff.
          { apply (@increasing_mono_increasing A B RA RB (fun a => f a (omega_lub (fun k => BW_fix (f (T k))))) T).
            - apply HT.
            - unfold mono, Proper, respectful. intros.
              apply Hf_mono. assumption. reflexivity. }
          intros k.
          transitivity (omega_lub (fun n => f (T k) (BW_fix (f (T n))))).
          { apply PO_Reflexive_Setoid. apply Hfa_sseq.
            apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
            - apply HT.
            - apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
          }
          apply limit_smaller_iff.
          { apply (@increasing_mono_increasing A B RA RB (fun a => f (T k) (BW_fix (f a))) T).
            - apply HT.
            - unfold mono, Proper, respectful. intros x y Hxy.
              apply Hf_mono. reflexivity.
              apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
              + assumption. }
          intros m.
          apply limit_greater.
          { apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
            - apply HT.
            - apply mono_BW_fix.
              + intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
              + intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity. }
          exists (max k m).
          assert (BW_fix (f (T (max k m))) == f (T (max k m)) (BW_fix (f (T (max k m))))).
          { apply BourbakiWitt_fixpoint; auto. apply Hf_mono. reflexivity. apply Hfa_sseq. }
          transitivity (f (T (max k m)) (BW_fix (f (T (max k m))))).
          2: { apply PO_Reflexive_Setoid. symmetry. apply H. }
          apply Hf_mono.
          { apply (@seq_mono_nat_le A RA _ _ T HT k (max k m)). apply Nat.le_max_l. }
          { apply mono_BW_fix.
            - intros a0. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
            - intros b0. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
            - apply (@seq_mono_nat_le A RA _ _ T HT m (max k m)). apply Nat.le_max_r. }
    - apply limit_smaller_iff.
      + apply (@increasing_mono_increasing A B RA RB (fun a => BW_fix (f a)) T).
        * apply HT.
        * apply mono_BW_fix.
          -- intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
          -- intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
      + intros n.
        apply mono_BW_fix.
        * intros a. unfold mono, Proper, respectful. intros. apply Hf_mono. reflexivity. assumption.
        * intros b. unfold mono, Proper, respectful. intros. apply Hf_mono. assumption. reflexivity.
        * eapply limit_greater.
          apply HT.
          exists n. reflexivity.
  Qed.

  Lemma mono_cont_BW_fix {A B} {RA: Order A} 
    {EA: Equiv A}
    {oLubA: OmegaLub A} {BotA: Bot A}
    {CPOA: CompletePartialOrder_Setoid A}
    {RB: Order B} {EB: Equiv B} {oLubB: OmegaLub B} {BotB: Bot B}
    {equA: Equivalence (@equiv A EA)}
    {equB: Equivalence (@equiv B EB)}
    {CPOB: CompletePartialOrder_Setoid B}:
    forall (f: A -> B -> B),
      (forall a, mono_cont (f a)) ->
      (forall b, mono_cont (fun W => f W b)) ->
      mono_cont (fun W => BW_fix (f W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_BW_fix; intros.
      + destruct (H a); auto.
      + destruct (H0 b); auto.
    - apply BW_fix_seq_cont_general; intros.
      + unfold Proper, respectful.
        intros.
        transitivity (f x y0).
        * destruct (H x) as [Hm _]. apply Hm; auto.
        * destruct (H0 y0) as [Hm _]. apply Hm; auto.
      + apply H.
      + apply H0.
  Qed.

  Lemma mono_cont_choice' {B D: Type}:
    forall (c1 c2: (program Σ B) -> program Σ D),
      mono_cont c1 -> mono_cont c2 ->
      mono_cont (fun W => choice (c1 W) (c2 W)).
  Proof.
    unfold mono_cont; intros.
    split.
    - apply mono_choice'; tauto.
    - apply continuous_choice'; tauto.
  Qed.

End mono_and_continuous_lemmas.

(* Ltac mono_cont_auto_aux :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => bind _ _) => apply mono_cont_bind; [try mono_cont_auto_aux | intros; try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => choice _ _) => apply mono_cont_choice; [try mono_cont_auto_aux | try mono_cont_auto_aux]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => _) => try apply mono_cont_const; try easy
  end.

Ltac mono_cont_auto_aux' :=
  match goal with
  | |- mono_cont (fun (W: program ?Σ ?B) => bind _ _) => apply mono_cont_bind'; [try mono_cont_auto_aux' | intros; try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?Σ ?B) => choice _ _) => apply mono_cont_choice'; [try mono_cont_auto_aux' | try mono_cont_auto_aux']
  | |- mono_cont (fun (W: program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto_aux'
  | |- mono_cont (fun (W: program ?Σ ?B) => _) => try apply mono_cont_const'; try easy
  end. *)

Ltac mono_cont_auto :=
  match goal with
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) (a: ?A) => _) => apply mono_cont_intro; intros; mono_cont_auto
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => bind _ _) => apply mono_cont_bind; [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => choice _ _) => apply mono_cont_choice; [try mono_cont_auto | try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => BW_fix _) => apply mono_cont_BW_fix; intros; try mono_cont_auto
  | |- mono_cont (bind _) => (apply mono_cont_bind || apply mono_cont_bind'); [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: ?A -> program ?Σ ?B) => _) => try apply mono_cont_const; try easy
  | |- mono_cont (fun (W: program ?Σ ?B) => bind _ _) => apply mono_cont_bind'; [try mono_cont_auto | intros; try mono_cont_auto]
  | |- mono_cont (fun (W: program ?Σ ?B) => choice _ _) => apply mono_cont_choice'; [try mono_cont_auto | try mono_cont_auto]
  | |- mono_cont (fun (W: program ?Σ ?B) => match ?a with _ => _ end) => destruct a; try mono_cont_auto
  | |- mono_cont (fun (W: program ?Σ ?B) => BW_fix _) => apply mono_cont_BW_fix; intros; try mono_cont_auto
  | |- mono_cont (fun (W: program ?Σ ?B) => _) => try apply mono_cont_const'; try easy
  end.

(*************************************************************************************************************)
(**********************************          while op for state monad        *********************************)
(**********************************                 program Σ A              *********************************)
(**********************************   1. while cond body :                   *********************************)
(**********************************            program Σ unit                *********************************)
(**********************************   2. whileret cond body :                *********************************)
(**********************************            A -> program Σ A              *********************************)
(**********************************   3. repeat_break body :                   *********************************)
(**********************************            A -> program Σ B              *********************************)
(*************************************************************************************************************)

Section  while_monad.

  Context {Σ: Type}.

  Definition while_f (cond: (program Σ bool))  (body : (program Σ unit)) 
                     (W : (program Σ unit)) 
                        : (program Σ unit) :=
  (x <- cond ;; (match x with 
  | true => body;; W
  | false => ret tt
  end)).

  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := BW_fix (while_f cond body).

  Definition whileP_f (cond: Σ -> Prop)  (body : (program Σ unit)) 
                     (W : program Σ unit) 
                        : program Σ unit :=
  choice (assume cond;; body;; W) 
         (assume (fun s => ~ cond s);; ret tt).
  
  Definition whileP (cond: Σ -> Prop) (body : program Σ unit)  := BW_fix (whileP_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => (ret a)
  end).

  Definition continue {A B: Type} (a: A): (program Σ (CntOrBrk A B)) := (ret (by_continue a)).
  Definition break {A B: Type} (b: B): (program Σ (CntOrBrk A B)) := (ret (by_break b)).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := BW_fix (whileret_f cond body).

  Definition repeat_break_f {A B: Type} (body: A -> program Σ (CntOrBrk A B)) (W: A -> program Σ B): A -> program Σ B :=
    fun a =>
      x <- body a;;
      match x with
      | by_continue a' => W a'
      | by_break b => ret b
      end.

  Definition repeat_break {A B: Type} (body: A -> program Σ (CntOrBrk A B)): A -> program Σ B :=
    BW_fix (repeat_break_f body).

  Definition repeat_break_f_noinput {B: Type} (body: program Σ (CntOrBrk unit B)) (W: program Σ B):  program Σ B :=
      x <- body ;;
      match x with
      | by_continue _ => W 
      | by_break b => ret b
      end.

  Definition repeat_break_noin {B: Type} (body: program Σ (CntOrBrk unit B)): program Σ B :=
    BW_fix (repeat_break_f_noinput body).

  Definition range_iter_f {A: Type} (hi: Z) (body: Z -> A -> program Σ A) (W: (Z * A) -> program Σ A): (Z * A) -> program Σ A :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         a1 <- body lo a0;;
         W ((lo + 1)%Z, a1))
        (assume!! (lo >= hi)%Z;;
         ret a0).

  Definition range_iter {A: Type} (lo hi: Z) (body: Z -> A -> program Σ A): A -> program Σ A :=
    fun a => BW_fix (range_iter_f hi body) (lo, a).

  Definition range_iter_break_f {A B: Type} (hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)) 
    (W: Z * A -> program Σ (CntOrBrk A B)): 
      Z * A -> program Σ (CntOrBrk A B) :=
    fun '(lo, a0) => 
      choice
        (assume!! (lo < hi)%Z;;
         ab <- body lo a0;;
         match ab with
         | by_continue a1 => W ((lo + 1)%Z, a1)
         | by_break b => break b
         end)
        (assume!! (lo >= hi)%Z;;
         continue a0).

  Definition range_iter_break {A B: Type} (lo hi: Z) 
    (body: Z -> A -> program Σ (CntOrBrk A B)): 
      A -> program Σ (CntOrBrk A B) :=
    fun a => BW_fix (range_iter_break_f hi body) (lo, a).

  Definition Repeat_f  (body : (program Σ unit)) 
                      (W : (program Σ unit)) 
                          : (program Σ unit) :=
    W ;; body.

  Definition Repeat (body : (program Σ unit))  := BW_fix (Repeat_f body).

  Definition ret_some {A: Type} (a: option A): program Σ bool :=
    match a with 
    | Some _ => ret true
    | None => ret false
    end.

  Lemma while_unfold: forall (cond: (program Σ bool)) (body : program Σ unit), 
  while cond body == (x <- cond ;;
                      match x with
                      | true => body ;; (while cond body)
                      | false => ret tt
                      end).
  Proof.
    intros.
    unfold while.
    apply (BW_fixpoint' (while_f cond body)).
    unfold while_f.
    mono_cont_auto.
  Qed.

  Lemma whileP_unfold: forall (cond: Σ -> Prop) (body : program Σ unit), 
    whileP cond body == choice 
                         (assume cond;; body;; whileP cond body)
                         (assume (fun s => ~ cond s);; ret tt).
  Proof.
    intros.
    unfold while.
    apply (BW_fixpoint' (whileP_f cond body)).
    unfold whileP_f.
    mono_cont_auto.
  Qed.
  
  Lemma whileret_unfold: forall {A: Type} (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  (a: A), 
    whileret cond body == fun a => (x <- (cond a);; 
                             match x with 
                             | true => y <- body a ;; whileret cond body y
                             | false => ret a
                             end).
  Proof.
    intros.
    unfold whileret.
    apply (BW_fixpoint' (whileret_f cond body)).
    unfold whileret_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_unfold {A B: Type}:
    forall (body: A -> program Σ (CntOrBrk A B)),
    repeat_break body == fun a =>
                        x <- body a;; 
                        match x with
                        | by_continue a0 => repeat_break body a0
                        | by_break b0 => ret b0
                        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (BW_fixpoint' (repeat_break_f body)).
    unfold repeat_break_f.
    mono_cont_auto.
  Qed.

  Lemma repeat_break_noin_unfold {B: Type}:
    forall (body: program Σ (CntOrBrk unit B)),
    repeat_break_noin body == 
                        x <- body;; 
                        match x with
                        | by_continue _ => repeat_break_noin body
                        | by_break b0 => ret b0
                        end.
  Proof.
    intros.
    unfold repeat_break.
    apply (BW_fixpoint' (repeat_break_f_noinput body)).
    unfold repeat_break_f_noinput.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold_aux:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A),
    (fun '(lo, a) => range_iter lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros. unfold range_iter.
    assert ((fun '(lo, a) => BW_fix (range_iter_f hi body) (lo, a))
      == BW_fix (range_iter_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_f hi body)).
    unfold range_iter_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_unfold:
    forall {A: Type} (hi: Z) (body: Z -> A -> program Σ A) lo a,
    range_iter lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      range_iter (lo + 1)%Z hi body b)
      (assume!! (lo >= hi)%Z;;
      ret a).
  Proof.
    intros.
    pose proof (range_iter_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
Qed.

  Lemma range_iter_break_unfold_aux:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)),
    (fun '(lo, a) => range_iter_break lo hi body a) ==
    fun '(lo, a) => choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue a' => range_iter_break (lo + 1)%Z hi body a'
      | by_break b' => break b'
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros. unfold range_iter_break.
    assert ((fun '(lo, a) => BW_fix (range_iter_break_f hi body) (lo, a))
      == BW_fix (range_iter_break_f hi body)).
    constructor; destruct a; easy.
    rewrite H.
    apply (BW_fixpoint' (range_iter_break_f hi body)).
    unfold range_iter_break_f.
    mono_cont_auto.
  Qed.

  Lemma range_iter_break_unfold:
    forall {A B: Type} (hi: Z) (body: Z -> A -> program Σ (CntOrBrk A B)) lo a,
    range_iter_break lo hi body a ==
    choice
      (assume!! (lo < hi)%Z;;
      b <- body lo a;;
      match b with
      | by_continue al => range_iter_break (lo + 1)%Z hi body al
      | by_break br => break br
      end)
      (assume!! (lo >= hi)%Z;;
      continue a).
  Proof.
    intros.
    pose proof (range_iter_break_unfold_aux hi body).
    unfold equiv in H; simpl in H.
    unfold Equiv_lift, LiftConstructors.lift_rel2 in H.
    specialize (H (lo, a)).
    auto.
  Qed.

End  while_monad.

Ltac unfold_loop H :=
  rewrite (while_unfold _ _ ) in H ||
  rewrite (repeat_break_unfold _ _) in H ||
  rewrite range_iter_unfold in H ||
  rewrite range_iter_break_unfold in H.
