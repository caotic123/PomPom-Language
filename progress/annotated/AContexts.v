(* Context conversion for annotated terms, derived from substitution. *)
From Stdlib Require Import List Arith.
Require Export annotated.AComparison.
Import ListNotations.

Theorem context_conversion : forall Gamma A B t T j k,
  RT.typing Gamma A (Raw.TSort j) -> RT.typing Gamma B (Raw.TSort k) ->
  nameless.DBCore.conv A B -> typing (A :: Gamma) t T -> typing (B :: Gamma) t T.
Proof.
  intros Gamma A B t T j k HA HB HC Ht.
  pose proof (RW.typing_context _ _ _ HA) as HW.
  assert (HBctx : RT.wf (B :: Gamma)) by (eapply RT.wf_cons; eassumption).
  pose proof (RW.weakening _ _ _ _ _ HA HB) as HA'.
  assert (HABctx : RT.wf (Raw.lift 1 0 A :: B :: Gamma)) by
    (eapply RT.wf_cons; eassumption).
  assert (Ht' : typing (Raw.lift 1 0 A :: B :: Gamma)
    (lift 1 1 t) (Raw.lift 1 1 T)).
  { eapply typing_lift; [exact Ht|exact HABctx|].
    apply RW.environment_lift_cons, RW.environment_lift_head. }
  assert (Hv : typing (B :: Gamma) (TVar 0) (Raw.lift 1 0 A)).
  { eapply ty_conv with (A := Raw.lift 1 0 B).
    - eapply ty_var; [exact HBctx|reflexivity].
    - exact HA'.
    - apply RW.conversion_lift, nameless.DBCore.cv_sym; exact HC. }
  pose proof (substitution _ _ _ _ _ Ht' Hv) as HR.
  cbn [erase] in HR.
  rewrite subst_eta_beta_cancel_gen, RB.subst_eta_beta_cancel_gen in HR.
  exact HR.
Qed.

Print Assumptions context_conversion.
