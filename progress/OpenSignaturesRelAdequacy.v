(* Adequacy: relatedness in the binary model implies observational
   equivalence, for closed terms and for open terms under every closing
   substitution. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelFundamental.
Import ListNotations.

Lemma inst_nil : forall t, instantiate [] t = t.
Proof. reflexivity. Qed.
Lemma inst_single : forall x u t, instantiate [(x, u)] t = subst u x t.
Proof. reflexivity. Qed.

Lemma closing_closing2 : forall Gamma g, closing Gamma g -> closing2 Gamma g g.
Proof.
  intros Gamma g H; induction H; [apply c2_nil|].
  apply c2_cons; try assumption.
  - eapply (extension_domain_formation named_weakening named_type_correctness named_beta_preservation);
      [eapply closing_context; exact H1|exact H|exact H0].
  - eapply typed_closed; eassumption.
  - eapply typed_closed; eassumption.
  - exact (rel_fundamental _ _ _ H2 [] [] c2_nil).
Qed.

Lemma observation_code : observation_type = TEnumT (code ["true"%string; "false"%string]).
Proof. reflexivity. Qed.

Theorem rel_adequacy : forall s1 s2, typing empty_ctx s1 observation_type ->
  typing empty_ctx s2 observation_type -> rel_at s1 s2 observation_type observation_type ->
  forall r, observation r -> (eval s1 r <-> eval s2 r).
Proof.
  intros s1 s2 H1 H2 Hr r Hobs.
  rewrite observation_code in Hr.
  destruct (rel_at_enum _ _ _ _ ["true"%string; "false"%string] Hr (cv_refl _)) as [m [_ [Hm1 Hm2]]].
  assert (Hs : conv s1 s2) by (eapply cv_trans; [exact Hm1|apply cv_sym; exact Hm2]).
  split; intro He.
  - exact (observation_evaluation_conversion _ _ _ H1 H2 Hs Hobs He).
  - exact (observation_evaluation_conversion _ _ _ H2 H1 (cv_sym Hs) Hobs He).
Qed.

Theorem rel_closed_observational : forall T u1 u2,
  typing empty_ctx u1 T -> typing empty_ctx u2 T -> rel_at u1 u2 T T ->
  closed_observational_eq T u1 u2.
Proof.
  intros T u1 u2 H1 H2 Hr. split; [exact H1|]. split; [exact H2|].
  intros x c r Hc Hobs.
  assert (HT : type_wf empty_ctx T) by (eapply named_type_correctness; exact H1).
  assert (HTc : closed T) by (destruct HT as [k Hk]; eapply typed_closed; exact Hk).
  assert (Hcl : closing2 (extend empty_ctx x T) [(x, u1)] [(x, u2)]).
  { apply c2_cons; [reflexivity|eapply typing_context; exact Hc|exact HT|apply c2_nil
      |eapply typed_closed; exact H1|eapply typed_closed; exact H2|exact Hr]. }
  pose proof (rel_fundamental _ _ _ Hc _ _ Hcl) as Hf.
  rewrite !inst_single in Hf.
  rewrite !(subst_not_free observation_type) in Hf by (cbn; tauto).
  assert (Ht1 : typing empty_ctx (subst u1 x c) observation_type).
  { change observation_type with (subst u1 x observation_type).
    eapply named_substitution; [reflexivity|exact Hc|exact H1]. }
  assert (Ht2 : typing empty_ctx (subst u2 x c) observation_type).
  { change observation_type with (subst u2 x observation_type).
    eapply named_substitution; [reflexivity|exact Hc|exact H2]. }
  exact (rel_adequacy _ _ Ht1 Ht2 Hf r Hobs).
Qed.

Theorem rel_observational : forall Gamma A t u, typing Gamma t A -> typing Gamma u A ->
  (forall g1 g2, closing2 Gamma g1 g2 ->
    rel_at (instantiate g1 t) (instantiate g2 u) (instantiate g1 A) (instantiate g2 A)) ->
  observational_eq Gamma A t u.
Proof.
  intros Gamma A t u Ht Hu H. split; [exact Ht|]. split; [exact Hu|].
  intros g Hg. apply rel_closed_observational.
  - eapply named_closing_substitution; eassumption.
  - eapply named_closing_substitution; eassumption.
  - apply H, closing_closing2, Hg.
Qed.

Print Assumptions rel_observational.
