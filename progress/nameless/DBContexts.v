From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDerivedTyping.
Import ListNotations.

Lemma context_conversion : forall Gamma A B t T j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) -> conv A B ->
  typing (A::Gamma) t T -> typing (B::Gamma) t T.
Proof.
  intros Gamma A B t T j k HA HB HC Ht.
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (HBctx : wf (B::Gamma)) by (eapply wf_cons;eassumption).
  pose proof (weakening _ _ _ _ _ HA HB) as HA'.
  assert (Habctx : wf (lift 1 0 A::B::Gamma)) by (eapply wf_cons;eassumption).
  assert (Hlift : typing (lift 1 0 A::B::Gamma) (lift 1 1 t) (lift 1 1 T)).
  { eapply typing_lift; [exact Ht|exact Habctx|].
    apply environment_lift_cons, environment_lift_head. }
  assert (Hv : typing (B::Gamma) (TVar 0) (lift 1 0 A)).
  { eapply ty_conv with (A:=lift 1 0 B).
    - apply smart_var; [exact HBctx|reflexivity].
    - exact HA'.
    - apply conversion_lift, cv_sym;exact HC. }
  pose proof (substitution _ _ _ _ _ Hlift Hv) as Hnew.
  rewrite !subst_eta_beta_cancel_gen in Hnew. exact Hnew.
Qed.

Lemma context_narrowing : forall Gamma A B t T j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) -> universe_le B A ->
  typing (A::Gamma) t T -> typing (B::Gamma) t T.
Proof.
  intros Gamma A B t T j k HA HB HU Ht.
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (HBctx : wf (B::Gamma)) by (eapply wf_cons;eassumption).
  pose proof (weakening _ _ _ _ _ HA HB) as HA'.
  assert (Habctx : wf (lift 1 0 A::B::Gamma)) by (eapply wf_cons;eassumption).
  assert (Hlift : typing (lift 1 0 A::B::Gamma) (lift 1 1 t) (lift 1 1 T)).
  { eapply typing_lift; [exact Ht|exact Habctx|].
    apply environment_lift_cons, environment_lift_head. }
  assert (Hv : typing (B::Gamma) (TVar 0) (lift 1 0 A)).
  { eapply universe_le_typing with (A:=lift 1 0 B).
    - apply smart_var; [exact HBctx|reflexivity].
    - now apply universe_le_lift.
    - eexists; exact HA'. }
  pose proof (substitution _ _ _ _ _ Hlift Hv) as Hnew.
  rewrite !subst_eta_beta_cancel_gen in Hnew. exact Hnew.
Qed.
