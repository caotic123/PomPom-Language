(* Weakening preserves every explicit annotation and its binding depth. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.ATyping.
Require nameless.DBWeakening.
Import ListNotations.
Module RW := nameless.DBWeakening.

Local Ltac lift_macros := repeat first
  [rewrite RW.lift_arrow in * | rewrite RW.lift_Def in * |
   rewrite RW.lift_Family in * | rewrite RW.lift_motive in * |
   rewrite RW.lift_recursive_method in * |
   rewrite RW.lift_close_case_method in * |
   rewrite RW.lift_close_motive in * |
   rewrite RW.lift_mu_ind_method in * |
   rewrite RW.lift_close_ind_method in *].

Theorem typing_lift : forall Gamma t A, typing Gamma t A ->
  forall c Delta, RT.wf Delta -> RW.environment_lift c Gamma Delta ->
  typing Delta (lift 1 c t) (Raw.lift 1 c A).
Proof.
  intros Gamma t A H; induction H; intros c Delta Hctx Henv.
  all: repeat match goal with
    IH : forall (n : nat) (Theta : Raw.ctx), RT.wf Theta ->
      RW.environment_lift n ?G Theta -> _,
    HE : RW.environment_lift ?c ?G ?Delta, HW : RT.wf ?Delta |- _ =>
      specialize (IH c Delta HW HE)
  end.
  all: lift_macros; cbn [lift Raw.lift Raw.MuAt Raw.CloseAt Raw.payload Raw.carrier] in *;
    repeat rewrite erase_lift in *.
  all: repeat rewrite nameless.DBParallelBase.lift_subst_zero_comm in *;
    cbn [Raw.lift] in *; repeat rewrite <- erase_lift in *.
  all: try solve [econstructor; eauto using RW.conversion_lift,
    RW.universe_le_lift, RW.typing_lift].
  all: try solve [destruct (Henv _ _ H0) as [U [HU HE]];
    unfold RW.shift_index in *; destruct (n <? c); rewrite HE;
      eapply ty_var; eassumption].
  all: try solve [
    econstructor; try eassumption;
    repeat rewrite erase_lift;
    match goal with
    | IH : forall (c : nat) (Delta : Raw.ctx), RT.wf Delta ->
        RW.environment_lift c _ Delta -> typing Delta (lift 1 c ?t) _
      |- typing _ (lift 1 (S ?c) ?t) _ =>
        eapply IH; [eapply RT.wf_cons; [exact Hctx|
          rewrite <- erase_lift; apply typing_erasure; eassumption]|
          apply RW.environment_lift_cons; exact Henv]
    end].
  - eapply ty_conv; [exact IHtyping| |].
    + exact (RW.typing_lift _ _ _ H0 c Delta Hctx Henv).
    + now apply RW.conversion_lift.
  - eapply ty_cumul_fun; [exact IHtyping| | | |].
    + exact (RW.typing_lift _ _ _ H0 c Delta Hctx Henv).
    + exact (RW.typing_lift _ _ _ H1 c Delta Hctx Henv).
    + now apply RW.universe_le_lift.
    + now apply RW.universe_le_lift.

Qed.

Theorem weakening : forall Gamma t A B k,
  typing Gamma t A -> RT.typing Gamma B (Raw.TSort k) ->
  typing (B :: Gamma) (lift 1 0 t) (Raw.lift 1 0 A).
Proof.
  intros Gamma t A B k Ht HB; eapply typing_lift; [exact Ht| |].
  - eapply RT.wf_cons; [exact (typing_context _ _ _ Ht)|exact HB].
  - apply RW.environment_lift_head.
Qed.

Print Assumptions typing_lift.
