(* Convertible row views retain the same label at each position and give
   convertible branch descriptions. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRowCoherence.
Import ListNotations.

Lemma reduction_choice : forall E D t, reduction (TIChoice E D) t ->
  exists E' D', t = TIChoice E' D' /\ reduces E E' /\ reduces D D'.
Proof.
  intros E D t H; inversion H; subst; cbn [root_step] in *;
    try discriminate; eauto 6 using reduces.
Qed.

Lemma reduces_choice : forall E D t, reduces (TIChoice E D) t ->
  exists E' D', t = TIChoice E' D' /\ reduces E E' /\ reduces D D'.
Proof.
  intros E D t H; remember (TIChoice E D) as src eqn:Heq.
  revert E D Heq; induction H; intros E D Heq; subst.
  - eauto using reduces.
  - destruct (reduction_choice _ _ _ H) as [E' [D' [-> [HE HD]]]].
    destruct (IHreduces _ _ eq_refl) as [E'' [D'' [-> [HE' HD']]]].
    exists E'',D''; repeat split; eauto using reduces_trans.
Qed.

Lemma conv_choice : forall E D E' D',
  conv (TIChoice E D) (TIChoice E' D') -> conv E E' /\ conv D D'.
Proof.
  intros E D E' D' HC.
  destruct (raw_conversion_joinability _ _ HC) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_choice _ _ _ Hw) as [F [G [-> [HF HG]]]].
  destruct (reduces_choice _ _ _ Hw') as [F' [G' [-> [HF' HG']]]].
  change (alpha_eqb F F' && alpha_eqb G G' = true) in Ha.
  apply Bool.andb_true_iff in Ha; destruct Ha as [HFF HGG].
  split; eapply joined_conv; eassumption.
Qed.

Lemma row_enum_position_transport : forall rs rt,
  conv (row_enum rs) (row_enum rt) -> forall n name D,
  nth_error rs n = Some (name,D) ->
  exists D', nth_error rt n = Some (name,D').
Proof.
  induction rs as [|[tag C] rs IH]; intros [|[tag' C'] rt] HC [|n] name D Hnth;
    cbn [nth_error] in Hnth; try discriminate.
  all: try solve [exfalso; pose proof (raw_head _ _ _ _ HC eq_refl eq_refl); discriminate].
  all: cbn [row_enum] in HC; apply conv_conse in HC; destruct HC as [Htag HE].
  - apply conv_tags in Htag; inversion Hnth; subst; eexists; reflexivity.
  - exact (IH rt HE n name D Hnth).
Qed.

Theorem row_code_position_transport : forall IT JT rs rt,
  conv (row_code IT rs) (row_code JT rt) -> forall n name D,
  nth_error rs n = Some (name,D) ->
  exists D', nth_error rt n = Some (name,D') /\ conv D D'.
Proof.
  intros IT JT rs rt HC n name D Hnth.
  destruct (conv_choice _ _ _ _ HC) as [HE HB].
  destruct (row_enum_position_transport _ _ HE _ _ _ Hnth) as [D' Hnth'].
  exists D'; split; [exact Hnth'|].
  eapply cv_trans; [exact (cv_sym (row_branches_position IT rs n name D Hnth))|].
  eapply cv_trans; [|exact (row_branches_position JT rt n name D' Hnth')].
  apply cv_compatible, cp_TApp; auto using cv_refl.
Qed.

Theorem row_view_position_transport : forall Gamma IT D rs rt,
  row_view Gamma IT D rs -> row_view Gamma IT D rt ->
  forall n name C, nth_error rs n = Some (name,C) ->
  exists C', nth_error rt n = Some (name,C') /\ conv C C'.
Proof.
  intros Gamma IT D rs rt Hrs Hrt.
  destruct Hrs as [rs Hrow HD HC], Hrt as [rt Hrow' HD' HC'].
  apply row_code_position_transport with (IT:=IT) (JT:=IT).
  eapply cv_trans; [apply cv_sym; exact HC|exact HC'].
Qed.

Print Assumptions row_code_position_transport.
Print Assumptions row_view_position_transport.
