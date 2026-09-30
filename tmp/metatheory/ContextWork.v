From Stdlib Require Import List Arith Bool Lia FMapFacts.
Require Export OpenSignaturesTransport.
Module CtxFacts := FMapFacts.WFacts(VarMap).

Definition ctx_equal (Gamma Delta : ctx) := forall x, lookup Gamma x = lookup Delta x.
Lemma ctx_equal_extend : forall Gamma Delta x A,
  ctx_equal Gamma Delta -> ctx_equal (extend Gamma x A) (extend Delta x A).
Proof.
  intros Gamma Delta x A H y. destruct (Nat.eq_dec y x) as [->|Hne].
  - now rewrite !lookup_extend_same.
  - rewrite !lookup_extend_other by congruence. apply H.
Qed.
Lemma ctx_equal_fresh : forall Gamma Delta x,
  ctx_equal Gamma Delta -> fresh_in Gamma x -> fresh_in Delta x.
Proof. unfold ctx_equal, fresh_in; intros Gamma Delta x H Hx; now rewrite <- H. Qed.
Lemma ctx_equal_exchange : forall Gamma x y A B,
  x <> y -> ctx_equal (extend (extend Gamma x A) y B) (extend (extend Gamma y B) x A).
Proof.
  intros Gamma x y A B Hxy z. destruct (Nat.eq_dec z x) as [Hx|Hx];
    destruct (Nat.eq_dec z y) as [Hy|Hy]; subst; try congruence.
  - rewrite !lookup_extend_same. rewrite lookup_extend_other by congruence. now rewrite lookup_extend_same.
  - rewrite !lookup_extend_same. rewrite lookup_extend_other by congruence. now rewrite lookup_extend_same.
  - now rewrite !lookup_extend_other by congruence.
Qed.

Theorem typing_ctx_equal : forall Gamma t A, typing Gamma t A ->
  forall Delta, wf Delta -> ctx_equal Gamma Delta -> typing Delta t A.
Proof.
  intros Gamma t A H; induction H; intros Delta Hwf HE.
  all: try solve [econstructor; eauto].
  - apply ty_var; [assumption|now rewrite <- HE].
  - assert (Hx : fresh_in Delta x) by (eapply ctx_equal_fresh; eassumption).
    assert (HA : typing Delta A (TSort j)) by auto.
    eapply ty_pi; [exact Hx|exact HA|].
    apply IHtyping2; [eapply wf_cons; eassumption|now apply ctx_equal_extend].
  - assert (Hx : fresh_in Delta x) by (eapply ctx_equal_fresh; eassumption).
    assert (HA : typing Delta A (TSort j)) by auto.
    eapply ty_sigma; [exact Hx|exact HA|].
    apply IHtyping2; [eapply wf_cons; eassumption|now apply ctx_equal_extend].
  - assert (Hx : fresh_in Delta x) by (eapply ctx_equal_fresh; eassumption).
    assert (HPi : typing Delta (TPi x A B) (TSort k)) by auto.
    destruct (pi_domain_formation _ _ _ _ _ HPi) as [j HA].
    eapply ty_lam; [exact Hx|exact HPi|].
    apply IHtyping2; [eapply wf_cons; eassumption|now apply ctx_equal_extend].
Qed.
