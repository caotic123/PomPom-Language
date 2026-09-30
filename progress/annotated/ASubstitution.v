(* Substitution simultaneously updates executable terms and annotations. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AWeakening.
Require nameless.DBSubstitution.
Import ListNotations.
Module RS := nameless.DBSubstitution.
Module RB := nameless.DBParallelBase.

Definition environment_subst c u (Gamma Delta : Raw.ctx) := forall n A,
  nth_error Gamma n = Some A ->
  typing Delta (subst u c (TVar n))
    (Raw.subst (erase u) c (Raw.lift (S n) 0 A)).

Lemma environment_subst_erasure : forall c u Gamma Delta,
  environment_subst c u Gamma Delta ->
  RS.environment_subst c (erase u) Gamma Delta.
Proof.
  intros c u Gamma Delta H n A Hn.
  pose proof (typing_erasure _ _ _ (H n A Hn)) as HT.
  now rewrite erase_subst in HT.
Qed.

Lemma environment_subst_cons : forall c u Gamma Delta A k,
  environment_subst c u Gamma Delta ->
  RT.typing Delta (Raw.subst (erase u) c A) (Raw.TSort k) ->
  environment_subst (S c) u (A :: Gamma) ((Raw.subst (erase u) c A) :: Delta).
Proof.
  intros c u Gamma Delta A k Henv HA [|n] B HB; cbn [nth_error] in HB.
  - inversion HB; subst B; rewrite RB.subst_lift_one_zero.
    change (typing (Raw.subst (erase u) c A :: Delta) (TVar 0)
      (Raw.lift 1 0 (Raw.subst (erase u) c A))).
    eapply ty_var; [eapply RT.wf_cons; eauto using RW.typing_context|reflexivity].
  - replace (TVar (S n)) with (lift 1 0 (TVar n)) by reflexivity.
    replace (Raw.lift (S (S n)) 0 B) with (Raw.lift 1 0 (Raw.lift (S n) 0 B))
      by (rewrite RB.lift_fuse_zero by lia; reflexivity).
    rewrite subst_lift_one_zero, RB.subst_lift_one_zero.
    eapply weakening; [exact (Henv n B HB)|exact HA].
Qed.

Local Ltac subst_macros := repeat first
  [rewrite RS.subst_arrow in * | rewrite RS.subst_Def in * |
   rewrite RS.subst_Family in * | rewrite RS.subst_motive in * |
   rewrite RS.subst_recursive_method in * |
   rewrite RS.subst_close_case_method in * |
   rewrite RS.subst_close_motive in * |
   rewrite RS.subst_mu_ind_method in * |
   rewrite RS.subst_close_ind_method in *].

Theorem typing_subst : forall Gamma t A, typing Gamma t A ->
  forall c u Delta, RT.wf Delta -> environment_subst c u Gamma Delta ->
  typing Delta (subst u c t) (Raw.subst (erase u) c A).
Proof.
  intros Gamma t A H; induction H; intros c u Delta Hctx Henv.
  all: repeat match goal with
    IH : forall (n : nat) (v : term) (Theta : Raw.ctx), RT.wf Theta ->
      environment_subst n v ?G Theta -> _,
    HE : environment_subst ?c ?u ?G ?Delta, HW : RT.wf ?Delta |- _ =>
      specialize (IH c u Delta HW HE)
  end.
  all: subst_macros;
    cbn [subst Raw.subst Raw.MuAt Raw.CloseAt Raw.payload Raw.carrier] in *;
    repeat rewrite erase_subst in *;
    repeat rewrite RB.subst_subst_zero_comm in *;
    cbn [Raw.subst] in *;
    repeat rewrite <- (erase_subst _ u c) in *;
    repeat rewrite <- (erase_subst _ u (S c)) in *.
  all: try solve [econstructor; eauto].
  all: try solve [exact (Henv _ _ H0)].
  all: try solve [
    econstructor; try eassumption;
    repeat rewrite erase_subst;
    match goal with
    | IH : forall (c : nat) (u : term) (Delta : Raw.ctx), RT.wf Delta ->
        environment_subst c u _ Delta -> typing Delta (subst u c ?t) _
      |- typing _ (subst ?u (S ?c) ?t) _ =>
        eapply IH;
        [eapply RT.wf_cons; [exact Hctx|
          rewrite <- erase_subst; apply typing_erasure; eassumption]|
         eapply environment_subst_cons; [exact Henv|
          rewrite <- erase_subst; apply typing_erasure; eassumption]]
    end].
  - eapply ty_conv; [exact IHtyping| |].
    + exact (RS.typing_subst _ _ _ H0 c (erase u) Delta Hctx
        (environment_subst_erasure _ _ _ _ Henv)).
    + now apply RS.conversion_subst.
  - eapply ty_cumul_fun; [exact IHtyping| | | |].
    + exact (RS.typing_subst _ _ _ H0 c (erase u) Delta Hctx
        (environment_subst_erasure _ _ _ _ Henv)).
    + exact (RS.typing_subst _ _ _ H1 c (erase u) Delta Hctx
        (environment_subst_erasure _ _ _ _ Henv)).
    + now apply RS.universe_le_subst.
    + now apply RS.universe_le_subst.
Qed.

Lemma environment_subst_head : forall Gamma A u,
  typing Gamma u A -> environment_subst 0 u (A :: Gamma) Gamma.
Proof.
  intros Gamma A u Hu [|n] B HB; cbn [nth_error] in HB.
  - inversion HB; subst B; rewrite RB.subst_lift_zero.
    cbn [subst]; now rewrite lift_zero_id.
  - replace (Raw.lift (S (S n)) 0 B) with (Raw.lift 1 0 (Raw.lift (S n) 0 B))
      by (rewrite RB.lift_fuse_zero by lia; reflexivity).
    rewrite RB.subst_lift_zero; cbn [subst].
    eapply ty_var; [exact (typing_context _ _ _ Hu)|exact HB].
Qed.

Theorem substitution : forall Gamma A b B a,
  typing (A :: Gamma) b B -> typing Gamma a A ->
  typing Gamma (subst a 0 b) (Raw.subst (erase a) 0 B).
Proof.
  intros Gamma A b B a Hb Ha; eapply typing_subst;
    [exact Hb|exact (typing_context _ _ _ Ha)|now apply environment_subst_head].
Qed.

Print Assumptions typing_subst.
Print Assumptions substitution.
