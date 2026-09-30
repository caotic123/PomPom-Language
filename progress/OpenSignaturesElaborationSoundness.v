(* Simultaneous elaboration soundness. Weakening, dead-witness typing, and
   coercion typing are explicit premises, avoiding circular proof dependencies. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Export OpenSignaturesCaseTyping.
Import ListNotations.

Lemma subtyping_formations : forall Gamma A B c,
  sub Gamma A B c -> type_wf Gamma A /\ type_wf Gamma B.
Proof.
  intros Gamma A B c H. induction H; try tauto.
  - split; [exists 0; apply ty_enumt, ty_nile; eapply typing_context; exact H|eexists; eassumption].
  - destruct H0 as [HIT [HF [HG Hi]]]. destruct H1 as [_ [HH _]].
    split; exists 0; apply close_at_formation; assumption.
Qed.

Lemma row_input_cons : forall Gamma IT name D rs,
  row_input Gamma IT ((name,D) :: rs) ->
  row_input Gamma IT rs /\ typing Gamma D (TIDesc IT).
Proof.
  intros Gamma IT name D rs [HIT [Hnames Hrows]].
  cbn in Hnames, Hrows. inversion Hnames; inversion Hrows; subst.
  split; [repeat split; assumption|assumption].
Qed.

Scheme synth_induction := Induction for elab_synth Sort Prop
with check_induction := Induction for elab_check Sort Prop
with cases_induction := Induction for elab_cases Sort Prop.
Combined Scheme elaboration_induction from synth_induction, check_induction, cases_induction.

Section ElaborationSoundness.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable dead_typed : forall Gamma IT D X d,
  dead Gamma IT D X d -> typing Gamma d (arrow (TInterp IT D X) Bot).
Variable sub_typed : forall Gamma A B c,
  sub Gamma A B c -> typing Gamma c (arrow A B).

Lemma elaboration_from_rules :
  (forall Gamma e A t, elab_synth Gamma e A t -> typing Gamma t A) /\
  (forall Gamma e A t, elab_check Gamma e A t -> typing Gamma t A) /\
  (forall Gamma k IT X Q bs rs hs, elab_cases Gamma k IT X Q bs rs hs ->
    row_input Gamma IT rs -> typing Gamma X (Family IT) -> typing Gamma Q (TSort k) ->
    Forall2 (fun entry h => typing Gamma h (arrow (TInterp IT (snd entry) X) Q)) rs hs).
Proof.
  apply elaboration_induction; intros;
    repeat match goal with H : type_wf _ _ |- _ => destruct H as [? ?] end;
    try assumption;
    try solve [eauto using ty_var, ty_app, ty_close, ty_conv, ty_lam, ty_pair,
      signature_from_weakening].
  all: try solve [constructor].
  { eapply case_term_typing; [exact weaken|exact c|exact r|exact t|exact H|].
    destruct r as [rs Hrow HD Hconv].
    assert (HX : typing Gamma (carrier IT G) (Family IT)).
    { destruct c as [HIT [HF [HG Hi]]]. apply ty_close; assumption. }
    apply row_handlers_tuple; [exact weaken|exact Hrow|exact HX|exact t|].
    now apply H0. }
  { match goal with Hsub : sub ?Gamma ?A ?B ?co |- _ =>
      destruct (subtyping_formations Gamma A B co Hsub) as [[j HA] [k HB]]
    end.
    eapply arrow_app; [exact weaken|exact HA|exact HB|eapply sub_typed; eassumption|assumption]. }
  { match goal with Hview : row_view _ _ _ _ |- _ => destruct Hview as [rs Hrow HD Hconv] end.
    eapply close_row_constructor; eassumption. }
  all: match goal with Hrow : row_input ?Gamma ?IT ((?name, ?D) :: ?rs) |- _ =>
    pose proof (proj1 Hrow) as HIT;
    destruct (row_input_cons Gamma IT name D rs Hrow) as [Htail HD]
    end.
  all: constructor; [|eauto].
  - eapply arrow_intro; [exact weaken| |eassumption|eassumption|eassumption].
    apply ty_interp; assumption.
  - eapply dead_handler_typing; [exact weaken| |eassumption|].
    + apply ty_interp; assumption.
    + eapply dead_typed; eassumption.
Qed.

Theorem synthesis_from_rules : forall Gamma e A t,
  elab_synth Gamma e A t -> typing Gamma t A.
Proof. exact (proj1 elaboration_from_rules). Qed.

Theorem checking_from_rules : forall Gamma e A t,
  elab_check Gamma e A t -> typing Gamma t A.
Proof. exact (proj1 (proj2 elaboration_from_rules)). Qed.

Theorem case_handlers_from_rules : forall Gamma k IT X Q bs rs hs,
  row_input Gamma IT rs -> typing Gamma X (Family IT) -> typing Gamma Q (TSort k) ->
  elab_cases Gamma k IT X Q bs rs hs ->
  typing Gamma (tuple hs) (TEPi k (row_enum rs) (handler_motive IT rs X Q)).
Proof.
  intros Gamma k IT X Q bs rs hs Hrows HX HQ Hcases.
  apply row_handlers_tuple; [exact weaken|exact Hrows|exact HX|exact HQ|].
  exact (proj2 (proj2 elaboration_from_rules) Gamma k IT X Q bs rs hs Hcases Hrows HX HQ).
Qed.

End ElaborationSoundness.
