(* Contextual equivalence laws used by coherence proofs. All dependencies
   are proved modules; the public coherence conjectures are not imported. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesObservations OpenSignaturesSubtypingSoundness.
Import ListNotations.

Lemma observation_formation : forall Gamma, wf Gamma ->
  typing Gamma observation_type (TSort 0).
Proof.
  intros; unfold observation_type; apply ty_enumt.
  repeat apply ty_conse; auto using ty_tag, ty_nile.
Qed.

Lemma closed_observational_refl : forall A t,
  typing empty_ctx t A -> closed_observational_eq A t t.
Proof. intros A t Ht; split; [exact Ht|]; split; [exact Ht|intros; reflexivity]. Qed.
Lemma closed_observational_sym : forall A t u,
  closed_observational_eq A t u -> closed_observational_eq A u t.
Proof. intros A t u [Ht [Hu HE]]; split; [exact Hu|]; split; [exact Ht|].
  intros x c r HC HR; symmetry; now apply HE. Qed.
Lemma closed_observational_trans : forall A t u v,
  closed_observational_eq A t u -> closed_observational_eq A u v -> closed_observational_eq A t v.
Proof.
  intros A t u v [Ht [Hu Htu]] [_ [Hv Huv]]; split; [exact Ht|]; split; [exact Hv|].
  intros x c r HC HR; etransitivity; [apply Htu|apply Huv]; assumption.
Qed.
Lemma observational_refl : forall Gamma A t,
  typing Gamma t A -> observational_eq Gamma A t t.
Proof.
  intros Gamma A t H; split; [exact H|]; split; [exact H|].
  intros env HE; apply closed_observational_refl; eapply named_closing_substitution; eassumption.
Qed.
Lemma observational_sym : forall Gamma A t u,
  observational_eq Gamma A t u -> observational_eq Gamma A u t.
Proof.
  intros Gamma A t u [Ht [Hu H]]; split; [exact Hu|]; split; [exact Ht|].
  intros env HE; now apply closed_observational_sym, H.
Qed.
Lemma observational_trans : forall Gamma A t u v,
  observational_eq Gamma A t u -> observational_eq Gamma A u v -> observational_eq Gamma A t v.
Proof.
  intros Gamma A t u v [Ht [Hu H]] [_ [Hv H']]; split; [exact Ht|]; split; [exact Hv|].
  intros env HE; eapply closed_observational_trans; [apply H|apply H']; exact HE.
Qed.

Lemma observation_conversion_iff : forall t u r,
  typing empty_ctx t observation_type -> typing empty_ctx u observation_type ->
  conv t u -> observation r -> (eval t r <-> eval u r).
Proof.
  intros t u r HT HU HC HR; split; intro HE.
  - exact (observation_evaluation_conversion _ _ _ HT HU HC HR HE).
  - exact (observation_evaluation_conversion _ _ _ HU HT (cv_sym HC) HR HE).
Qed.

Theorem closed_observational_function_tests : forall A t u,
  closed_observational_eq A t u <->
  typing empty_ctx t A /\ typing empty_ctx u A /\
  forall f r, typing empty_ctx f (arrow A observation_type) -> observation r ->
    (eval (TApp f t) r <-> eval (TApp f u) r).
Proof.
  intros A t u; split.
  - intros [Ht [Hu Hobs]]; split; [exact Ht|]; split; [exact Hu|].
    intros f r Hf Hr.
    destruct (named_type_correctness _ _ _ Ht) as [j HA].
    assert (Hctx : wf (extend empty_ctx 0 A)) by (eapply wf_cons; eauto using wf_nil; reflexivity).
    assert (Hf' : typing (extend empty_ctx 0 A) f (arrow A observation_type))
      by (eapply named_weakening; [reflexivity|exact Hf|exact HA]).
    assert (Hx : typing (extend empty_ctx 0 A) (TVar 0) A) by (apply ty_var; [exact Hctx|apply lookup_extend_same]).
    pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ Hf' Hx) as HC.
    specialize (Hobs 0 (TApp f (TVar 0)) r HC Hr).
    cbn [subst substitute] in Hobs.
    change (eval (TApp (subst t 0 f) t) r <-> eval (TApp (subst u 0 f) u) r) in Hobs.
    rewrite !subst_fresh in Hobs by (rewrite (typed_closed _ _ Hf); tauto).
    exact Hobs.
  - intros [Ht [Hu Htest]]; split; [exact Ht|]; split; [exact Hu|].
    intros x c r HC HR.
    destruct (named_type_correctness _ _ _ Ht) as [j HA].
    assert (Hf : typing empty_ctx (TLam x c) (arrow A observation_type)).
    { eapply arrow_intro; [exact named_weakening|exact HA|apply observation_formation, wf_nil|reflexivity|exact HC]. }
    assert (Htc : typing empty_ctx (subst t x c) observation_type).
    { change observation_type with (subst t x observation_type); eapply named_substitution; [reflexivity|exact HC|exact Ht]. }
    assert (Huc : typing empty_ctx (subst u x c) observation_type).
    { change observation_type with (subst u x observation_type); eapply named_substitution; [reflexivity|exact HC|exact Hu]. }
    pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ Hf Ht) as Hft.
    pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ Hf Hu) as Hfu.
    etransitivity; [apply (observation_conversion_iff _ _ _ Htc Hft); [apply cv_sym, cv_step, st_root; reflexivity|exact HR]|].
    etransitivity; [exact (Htest _ _ Hf HR)|].
    apply (observation_conversion_iff _ _ _ Hfu Huc); [apply cv_step, st_root; reflexivity|exact HR].
Qed.

Lemma compose_coercion_beta : forall c d a,
  conv (TApp (compose_coercion c d) a) (TApp d (TApp c a)).
Proof.
  intros c d a; unfold compose_coercion.
  eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  change (conv (TApp (subst a (fresh [c;d]) d)
    (TApp (subst a (fresh [c;d]) c)
      (if Nat.eqb (fresh [c;d]) (fresh [c;d]) then a else TVar (fresh [c;d]))))
    (TApp d (TApp c a))).
  rewrite Nat.eqb_refl, !subst_fresh by (apply fresh_not_free; cbn; auto).
  apply cv_refl.
Qed.

Theorem closed_observational_congruence : forall A B f t u,
  typing empty_ctx f (arrow A B) -> closed_observational_eq A t u ->
  closed_observational_eq B (TApp f t) (TApp f u).
Proof.
  intros A B f t u HF HE.
  destruct (proj1 (closed_observational_function_tests _ _ _) HE) as [HT [HU Htest]].
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HF HT) as HFT.
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HF HU) as HFU.
  apply (proj2 (closed_observational_function_tests _ _ _)); split; [exact HFT|]; split; [exact HFU|].
  intros g r HG HR.
  assert (HFG : typing empty_ctx (compose_coercion f g) (arrow A observation_type)).
  { eapply compose_coercion_typing; [exact named_weakening|exact named_type_correctness| | |exact HF|exact HG].
    - eapply named_type_correctness; exact HT.
    - exists 0; apply observation_formation, wf_nil. }
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HFG HT) as HFGT.
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HFG HU) as HFGU.
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HG HFT) as HGFT.
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HG HFU) as HGFU.
  etransitivity; [apply (observation_conversion_iff _ _ _ HGFT HFGT); [apply cv_sym, compose_coercion_beta|exact HR]|].
  etransitivity; [exact (Htest _ _ HFG HR)|].
  apply (observation_conversion_iff _ _ _ HFGU HGFU); [apply compose_coercion_beta|exact HR].
Qed.

Theorem closed_observational_context : forall A B x c t u k,
  typing empty_ctx B (TSort k) -> typing (extend empty_ctx x A) c B ->
  closed_observational_eq A t u ->
  closed_observational_eq B (subst t x c) (subst u x c).
Proof.
  intros A B x c t u k HB HC HE.
  destruct HE as [HT [HU Hobs]].
  destruct (named_type_correctness _ _ _ HT) as [j HA].
  assert (HF : typing empty_ctx (TLam x c) (arrow A B)).
  { eapply arrow_intro; [exact named_weakening|exact HA|exact HB|reflexivity|exact HC]. }
  assert (HTc : typing empty_ctx (subst t x c) B).
  { pose proof (named_substitution empty_ctx x A c B t eq_refl HC HT) as H.
    rewrite (subst_fresh B _ x) in H by (rewrite (typed_closed _ _ HB); tauto); exact H. }
  assert (HUc : typing empty_ctx (subst u x c) B).
  { pose proof (named_substitution empty_ctx x A c B u eq_refl HC HU) as H.
    rewrite (subst_fresh B _ x) in H by (rewrite (typed_closed _ _ HB); tauto); exact H. }
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HF HT) as HFT.
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ HF HU) as HFU.
  eapply closed_observational_trans; [eapply closed_observational_conversion; [exact HTc|exact HFT|apply cv_sym, cv_step, st_root; reflexivity]|].
  eapply closed_observational_trans; [eapply closed_observational_congruence; [exact HF|split; [exact HT|split; [exact HU|exact Hobs]]]|].
  eapply closed_observational_conversion; [exact HFU|exact HUc|apply cv_step, st_root; reflexivity].
Qed.

Print Assumptions closed_observational_function_tests.
Print Assumptions closed_observational_congruence.
Print Assumptions closed_observational_context.
