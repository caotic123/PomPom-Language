From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesContexts.

Definition ctx_included (Gamma Delta : ctx) := forall x A,
  lookup Gamma x = Some A -> lookup Delta x = Some A.
Lemma ctx_included_refl : forall Gamma, ctx_included Gamma Gamma.
Proof. firstorder. Qed.
Lemma ctx_included_trans : forall Gamma Delta Theta,
  ctx_included Gamma Delta -> ctx_included Delta Theta -> ctx_included Gamma Theta.
Proof. firstorder. Qed.
Lemma ctx_included_extend : forall Gamma x A,
  fresh_in Gamma x -> ctx_included Gamma (extend Gamma x A).
Proof.
  intros Gamma x A Hx y B HB. destruct (Nat.eq_dec y x) as [->|Hne].
  - unfold fresh_in in Hx; congruence.
  - now rewrite lookup_extend_other by congruence.
Qed.

Lemma wf_lookup_origin : forall Delta, wf Delta -> forall x A,
  lookup Delta x = Some A -> exists Gamma k,
  wf Gamma /\ fresh_in Gamma x /\ typing Gamma A (TSort k) /\ ctx_included Gamma Delta.
Proof.
  intros Delta Hwf; induction Hwf; intros y B HB; [discriminate|].
  destruct (Nat.eq_dec y x) as [->|Hne].
  - rewrite lookup_extend_same in HB; inversion HB; subst.
    exists Gamma,k; repeat split; auto using ctx_included_extend.
  - rewrite lookup_extend_other in HB by congruence.
    destruct (IHHwf _ _ HB) as [Theta [j [HT [Hy [HA Hin]]]]].
    exists Theta,j; repeat split; try assumption.
    eapply ctx_included_trans; [exact Hin|now apply ctx_included_extend].
Qed.

Section ContextInclusion.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable regular : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Variable preserve : forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A.

Lemma typing_from_empty : forall Gamma, wf Gamma -> forall t A,
  typing empty_ctx t A -> typing Gamma t A.
Proof. intros Gamma Hwf; induction Hwf; intros; eauto. Qed.

Lemma typing_ctx_included : forall Gamma, wf Gamma -> forall Delta t A,
  wf Delta -> ctx_included Gamma Delta -> typing Gamma t A -> typing Delta t A.
Proof.
  intros Gamma Hwf; induction Hwf; intros Delta t T HD Hin Ht.
  - now apply typing_from_empty.
  - destruct (regular _ _ _ Ht) as [j HT].
    assert (HPi : typing Gamma (TPi x A T) (TSort (Nat.max k j))) by (eapply ty_pi; eassumption).
    assert (Hlam : typing Gamma (TLam x t) (TPi x A T)) by (eapply ty_lam; eassumption).
    assert (Hin' : ctx_included Gamma Delta) by
      (eapply ctx_included_trans; [apply ctx_included_extend; eassumption|exact Hin]).
    assert (HPi' : typing Delta (TPi x A T) (TSort (Nat.max k j))) by (eapply IHHwf; eassumption).
    assert (Hlam' : typing Delta (TLam x t) (TPi x A T)) by (eapply IHHwf; eassumption).
    assert (Hx : typing Delta (TVar x) A) by
      (apply ty_var; [exact HD|apply Hin, lookup_extend_same]).
    pose proof (@ty_app Delta x A T (TLam x t) (TVar x) _ HPi' Hlam' Hx) as Happly.
    rewrite subst_variable_identity in Happly.
    eapply preserve; [exact Happly|]. apply red_root. cbn [root_step].
    now rewrite subst_variable_identity.
Qed.

Lemma extension_domain_formation : forall Gamma x A,
  wf Gamma -> fresh_in Gamma x -> wf (extend Gamma x A) -> type_wf Gamma A.
Proof.
  intros Gamma x A Hctx Hx Hext.
  destruct (wf_lookup_origin _ Hext x A (lookup_extend_same Gamma x A))
    as [Delta [k [HD [Hxd [HA Hin]]]]].
  exists k. eapply typing_ctx_included; [exact HD|exact Hctx| |exact HA].
  intros y B Hy. destruct (Nat.eq_dec y x) as [->|Hne].
  - unfold fresh_in in Hxd; congruence.
  - specialize (Hin _ _ Hy). now rewrite lookup_extend_other in Hin by congruence.
Qed.
End ContextInclusion.
