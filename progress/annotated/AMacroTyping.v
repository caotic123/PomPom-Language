(* Typing lemmas for the annotated macros: every constructor of a root
   reduct is shown well-typed from typings of its components.  These are the
   annotated analogues of DBDerivedTyping/DBOperatorFormations. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AGenAll annotated.AEta annotated.AProjections.
Require nameless.DBGeneration nameless.DBConstructorGeneration
  nameless.DBMuBeta nameless.DBClosePayload nameless.DBEnumBeta
  nameless.DBInductionBeta.
Import ListNotations.
Module RW := nameless.DBWeakening.
Module RS := nameless.DBSubstitution.
Module RB := nameless.DBParallelBase.
Module RO := nameless.DBOperatorFormations.
Module DT := nameless.DBDerivedTyping.
Module RG := nameless.DBGeneration.
Module RCG := nameless.DBConstructorGeneration.
Module RM := nameless.DBMuBeta.
Module RCL := nameless.DBClosePayload.
Module RE := nameless.DBEnumBeta.
Module RI := nameless.DBInductionBeta.


(* annotated subst-through-lift: subst u c (lift (S n) 0 t) = lift n 0 t *)
Lemma asubst_lift_prefix : forall t u n c, c <= n ->
  subst u c (lift (S n) 0 t) = lift n 0 t.
Proof.
  intros t u n c Hcn.
  replace (lift (S n) 0 t) with (lift 1 c (lift n 0 t))
    by (apply lift_fuse_zero; exact Hcn).
  apply subst_lift_cancel.
Qed.

(* ---- normalization for lift/subst/erase in types ---- *)
Ltac anorm_ty :=
  repeat first
    [ rewrite erase_lift in * | rewrite erase_subst in * |
      rewrite erase_afamily_app in * | rewrite erase_adef_app in * |
      rewrite erase_aCloseAt in * | rewrite erase_aMuAt in * |
      rewrite erase_apayload in * | rewrite erase_atotal in * |
      rewrite erase_amotive in * | rewrite erase_arecursive_method in * |
      rewrite erase_arec_codomain in * | rewrite erase_arec_pair in * |
      rewrite erase_atail_motive in * | rewrite erase_adiagonal_motive in * |
      rewrite RB.lift_fuse_zero in * by lia |
      rewrite RB.lift_lift_one_zero in * |
      rewrite RB.lift_lift_two_zero in * |
      rewrite RW.lift_lift_three_zero in * |
      rewrite RW.lift_lift_four_zero in * |
      rewrite RB.lift_zero_id in * |
      rewrite RB.subst_lift_zero in * |
      rewrite RB.subst_lift_one_zero in * |
      rewrite RB.subst_lift_two_zero in * |
      rewrite RS.subst_lift_three_zero in * |
      rewrite RS.subst_lift_four_zero in * |
      rewrite DT.subst_lift_prefix in * by lia |
      rewrite RW.lift_arrow in * | rewrite RW.lift_Def in * |
      rewrite RW.lift_Family in * | rewrite RW.lift_motive in * |
      rewrite RW.lift_total in * | rewrite RW.lift_recursive_method in * |
      rewrite RW.lift_close_case_method in * | rewrite RW.lift_close_motive in * |
      rewrite RW.lift_mu_ind_method in * | rewrite RW.lift_close_ind_method in * |
      rewrite RW.lift_diagonal_motive in * |
      rewrite RS.subst_arrow in * | rewrite RS.subst_Def in * |
      rewrite RS.subst_Family in * | rewrite RS.subst_total in * |
      rewrite RS.subst_motive in * | rewrite RS.subst_recursive_method in * |
      rewrite RS.subst_close_case_method in * | rewrite RS.subst_close_motive in * |
      rewrite RS.subst_diagonal_motive in * |
      rewrite RS.subst_mu_ind_method in * | rewrite RS.subst_close_ind_method in * |
      progress (unfold Raw.total, Raw.motive, Raw.Family, Raw.Def,
        Raw.arrow, Raw.MuAt, Raw.CloseAt, Raw.payload, Raw.carrier,
        Raw.product, Raw.recursive_method, Raw.diagonal_motive,
        Raw.close_motive, Raw.close_case_method, Raw.mu_ind_method,
        Raw.close_ind_method,
        afamily_app, adef_app, aCloseAt, aMuAt, acarrier, apayload, aDef,
        atotal, amotive, arec_pair, arec_codomain, arecursive_method,
        atail_motive, aproduct, aarrow, abot, adesc_app_binder,
        adesc_app_binder_enum, ainterp_binder, ainterp_binder_enum,
        aapp_binder, aiall_binder, ahyps_binder, ahyps_prod_pair,
        aepi_head, ainstantiate, ainstantiate_enum, amu_payload, amu_iall,
        amu_result, amu_ind_codomain, amu_ind_method, amethod_app,
        acim_payload, acim_iall, acim_result, acim_rest, acim_method,
        acmethod_app, aclose_case_codomain, atotal_pair, amotive_app,
        arec_app, ahyps_mu, amu_ind_reduct, ahyps_close, aclose_ind_reduct,
        amu_rec_body, amu_rec_lam, adiagonal_motive, aclose_rec_body,
        aclose_rec_lam in *) |
      progress (cbn [erase Raw.lift Raw.subst map app length
                     Nat.ltb Nat.leb Nat.eqb] in *) |
      rewrite ABinding.lift_fuse_zero in * by lia |
      rewrite ABinding.lift_zero_id in * |
      rewrite ABinding.lift_lift_one_zero in * |
      rewrite ABinding.lift_lift_two_zero in * |
      rewrite ABinding.subst_lift_zero in * |
      rewrite ABinding.subst_lift_one_zero in * |
      rewrite ABinding.subst_lift_two_zero in * |
      rewrite ABinding.subst_lift_offset in * by lia |
      rewrite asubst_lift_prefix in * by lia ].


(* ---- context operations ---- *)

Lemma aweaken : forall Gamma t T A k,
  typing Gamma t T -> typing Gamma A (Raw.TSort k) ->
  typing (erase A :: Gamma) (lift 1 0 t) (Raw.lift 1 0 T).
Proof.
  intros; eapply weakening; [eassumption|apply typing_erasure; eassumption].
Qed.

(* weakening through a prefix of annotated binders *)
Lemma aweaken_by : forall Delta Gamma t T,
  typing Gamma t T -> RT.wf (map erase Delta ++ Gamma) ->
  typing (map erase Delta ++ Gamma) (lift (length Delta) 0 t)
    (Raw.lift (length Delta) 0 T).
Proof.
  induction Delta as [|A Delta IH]; intros Gamma t T Ht HW; cbn [map length app] in *.
  - now rewrite lift_zero_id, RB.lift_zero_id.
  - cbn [lift Raw.lift] in *. inversion HW as [|? ? ? HW' HA']; subst.
    pose proof (IH _ _ _ Ht HW') as H'.
    pose proof (weakening _ _ _ _ _ H' HA') as H''.
    now rewrite !lift_fuse_zero, !RB.lift_fuse_zero in H'' by lia.
Qed.

Lemma awf_cons : forall Gamma A k,
  RT.wf Gamma -> RT.typing Gamma A (Raw.TSort k) -> RT.wf (A :: Gamma).
Proof. intros; eapply RT.wf_cons; eassumption. Qed.

Ltac awf :=
  repeat (eapply RT.wf_cons);
  eauto using typing_context, typing_erasure.

Lemma avar0 : forall Gamma A k,
  typing Gamma A (Raw.TSort k) ->
  typing (erase A :: Gamma) (TVar 0) (Raw.lift 1 0 (erase A)).
Proof.
  intros Gamma A k HA.
  eapply ty_var; [eapply RT.wf_cons;
    [exact (typing_context _ _ _ HA)|apply typing_erasure; exact HA]|reflexivity].
Qed.

Lemma avar_nth : forall Gamma n A,
  RT.wf Gamma -> nth_error Gamma n = Some A ->
  typing Gamma (TVar n) (Raw.lift (S n) 0 A).
Proof. intros; eapply ty_var; eassumption. Qed.

(* var with the type given by an equation — the stored entry keeps a
   stuck [erase (lift ..)] that never unifies with the normalized goal *)
Lemma avar_typed : forall Gamma n A T,
  RT.wf Gamma -> nth_error Gamma n = Some A ->
  Raw.lift (S n) 0 A = T ->
  typing Gamma (TVar n) T.
Proof. intros; subst T; eapply ty_var; eassumption. Qed.

(* raw-side typing of an erased annotated term: conversion pushes erase
   through the head constructor, so no rewriting is needed *)
Ltac rty H := exact (typing_erasure _ _ _ H).

Lemma asort_under : forall Gamma A k j,
  typing Gamma A (Raw.TSort j) ->
  typing (erase A :: Gamma) (TSort k) (Raw.TSort (S k)).
Proof.
  intros; apply ty_sort; eapply RT.wf_cons;
    [eapply typing_context; eassumption|apply typing_erasure; eassumption].
Qed.

(* ---- application helpers ---- *)

(* generic annotated application with the result type given by an equation *)
Lemma aapp_conv : forall Gamma A B f a T j k,
  typing Gamma A (Raw.TSort j) -> typing (erase A :: Gamma) B (Raw.TSort k) ->
  typing Gamma f (Raw.TPi (erase A) (erase B)) -> typing Gamma a (erase A) ->
  Raw.subst (erase a) 0 (erase B) = T ->
  typing Gamma (TApp A B f a) T.
Proof.
  intros Gamma A B f a T j k HA HB Hf Ha HT; subst T.
  apply ty_app with (j:=j) (k:=k); assumption.
Qed.

(* generic annotated pair with the result type given by an equation *)
Lemma apair_conv : forall Gamma A B a b T j k,
  typing Gamma A (Raw.TSort j) -> typing (erase A :: Gamma) B (Raw.TSort k) ->
  typing Gamma a (erase A) ->
  typing Gamma b (Raw.subst (erase a) 0 (erase B)) ->
  Raw.TSigma (erase A) (erase B) = T ->
  typing Gamma (TPair A B a b) T.
Proof.
  intros Gamma A B a b T j k HA HB Ha Hb HT; subst T.
  apply ty_pair with (j:=j) (k:=k); assumption.
Qed.

Lemma afamily_app_typing : forall Gamma IT X i,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma i (erase IT) ->
  typing Gamma (afamily_app IT X i) (Raw.TSort 0).
Proof.
  intros Gamma IT X i HI HX Hi; unfold afamily_app.
  apply ty_app with (j:=0) (k:=1);
    [exact HI|exact (asort_under _ _ _ _ HI)|exact HX|exact Hi].
Qed.

Lemma adef_app_typing : forall Gamma IT D i,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma i (erase IT) ->
  typing Gamma (adef_app IT D i) (Raw.TIDesc (erase IT)).
Proof.
  intros Gamma IT D i HI HD Hi; unfold adef_app.
  apply aapp_conv with (j:=0) (k:=1);
    [exact HI| | |exact Hi|].
  - apply ty_idesc. exact (weakening _ _ _ _ _ HI (typing_erasure _ _ _ HI)).
  - cbn [erase]. rewrite erase_lift. exact HD.
  - cbn [erase]. rewrite erase_lift. cbn [Raw.subst].
    rewrite RB.subst_lift_zero. reflexivity.
Qed.

Lemma aMuAt_typing : forall Gamma IT D i,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma i (erase IT) ->
  typing Gamma (aMuAt IT D i) (Raw.TSort 0).
Proof.
  intros Gamma IT D i HI HD Hi; unfold aMuAt.
  apply ty_app with (j:=0) (k:=1);
    [exact HI|exact (asort_under _ _ _ _ HI)|
     apply ty_mui; eassumption|exact Hi].
Qed.

Lemma aCloseAt_typing : forall Gamma IT F G i,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma F (Raw.Def (erase IT)) ->
  typing Gamma G (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma (aCloseAt IT F G i) (Raw.TSort 0).
Proof.
  intros Gamma IT F G i HI HF HG Hi; unfold aCloseAt.
  apply ty_app with (j:=0) (k:=1);
    [exact HI|exact (asort_under _ _ _ _ HI)|
     apply ty_close; eassumption|exact Hi].
Qed.

Lemma aDef_formation : forall Gamma IT,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma (aDef IT) (Raw.TSort 1).
Proof.
  intros Gamma IT HI; unfold aDef.
  change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
  apply ty_pi; [exact HI|apply ty_idesc;
    exact (aweaken _ _ _ _ _ HI HI)].
Qed.

Lemma aFamily_formation : forall Gamma IT,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma (TPi IT (TSort 0)) (Raw.TSort 1).
Proof.
  intros Gamma IT HI.
  change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
  eapply ty_pi; [exact HI|exact (asort_under _ _ _ _ HI)].
Qed.

Lemma acarrier_typing : forall Gamma IT G,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma (acarrier IT G) (Raw.Family (erase IT)).
Proof. intros; apply ty_close; assumption. Qed.

Lemma apayload_formation : forall Gamma IT F G i,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma F (Raw.Def (erase IT)) ->
  typing Gamma G (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma (apayload IT F G i) (Raw.TSort 0).
Proof.
  intros; unfold apayload; apply ty_interp;
    eauto using adef_app_typing, acarrier_typing.
Qed.

Lemma atotal_formation : forall Gamma IT X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma (atotal IT X) (Raw.TSort 0).
Proof.
  intros Gamma IT X HI HX; unfold atotal.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply ty_sigma; [exact HI|].
  eapply afamily_app_typing;
    [exact (aweaken _ _ _ _ _ HI HI)| |
     rewrite erase_lift; exact (avar0 _ _ _ HI)].
  pose proof (weakening _ _ _ _ _ HX (typing_erasure _ _ _ HI)) as H'.
  cbn [Raw.lift Raw.Family] in H'. anorm_ty. exact H'.
Qed.

Lemma amotive_formation : forall Gamma IT X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma (amotive IT X) (Raw.TSort 1).
Proof.
  intros Gamma IT X HI HX; unfold amotive.
  change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
  apply ty_pi; [eapply atotal_formation; eassumption|].
  apply ty_sort; eapply RT.wf_cons;
    [eapply typing_context; eapply atotal_formation; eassumption|
     apply typing_erasure, atotal_formation; eassumption].
Qed.

(* ---- binders over [i : eIT] ---- *)

Lemma afam_binder_typing : forall Gamma IT X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing (erase IT :: Gamma)
    (afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0)) (Raw.TSort 0).
Proof.
  intros Gamma IT X HI HX; eapply afamily_app_typing;
    [exact (aweaken _ _ _ _ _ HI HI)| |].
  - pose proof (weakening _ _ _ _ _ HX (typing_erasure _ _ _ HI)) as H'.
    cbn [Raw.lift Raw.Family] in H'. anorm_ty. exact H'.
  - rewrite erase_lift. exact (avar0 _ _ _ HI).
Qed.

(* wf of the two-binder context used by every Π x:(X i). ... codomain *)
Lemma afam_ctx_wf : forall Gamma IT X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  RT.wf (map erase
    [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT] ++ Gamma).
Proof.
  intros; cbn [map app]; eapply awf_cons;
    [eapply awf_cons; [eapply typing_context; eassumption|
      apply typing_erasure; eassumption]|].
  apply typing_erasure; eapply afam_binder_typing; eassumption.
Qed.

(* The recursive codomain  Π x:(X i). P (i,x)  sits under the outer
   i-binder of a recursive_method, i.e. in context [eIT :: Γ]. *)
Lemma arec_codomain_formation : forall Gamma IT X P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing (erase IT :: Gamma) (arec_codomain IT X P) (Raw.TSort 0).
Proof.
  intros Gamma IT X P HI HX HP.
  pose proof (afam_binder_typing _ _ _ HI HX) as Hdom.
  pose proof (afam_ctx_wf _ _ _ HI HX) as HW2.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply ty_pi; [exact Hdom|].
  assert (Htot : typing (map erase
      [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT] ++ Gamma)
      (atotal (lift 2 0 IT) (lift 2 0 X)) (Raw.TSort 0)).
  { eapply atotal_formation.
    - exact (aweaken_by [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
        _ _ _ HI HW2).
    - pose proof (aweaken_by [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
        _ _ _ HX HW2) as HX2. anorm_ty. exact HX2. }
  apply aapp_conv with (j:=0) (k:=1).
  - exact Htot.
  - apply ty_sort. eapply awf_cons; [exact HW2|].
    apply typing_erasure. exact Htot.
  - pose proof (aweaken_by [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
      _ _ _ HP HW2) as HP2. anorm_ty. exact HP2.
  - unfold arec_pair. apply apair_conv with (j:=0) (k:=0).
    + exact (aweaken_by [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
        _ _ _ HI HW2).
    + assert (HW3 : RT.wf (map erase
        [lift 2 0 IT; afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
        ++ Gamma)).
      { cbn [map app]. eapply awf_cons; [exact HW2|].
        apply typing_erasure.
        exact (aweaken_by [afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
          _ _ _ HI HW2). }
      eapply afamily_app_typing.
      * pose proof (aweaken_by
          [lift 2 0 IT; afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
          _ _ _ HI HW3) as HI3. anorm_ty. exact HI3.
      * pose proof (aweaken_by
          [lift 2 0 IT; afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0); IT]
          _ _ _ HX HW3) as HX3. anorm_ty. exact HX3.
      * eapply avar_typed; [exact HW3|reflexivity|].
        anorm_ty. reflexivity.
    + anorm_ty. eapply avar_typed; [exact HW2|reflexivity|].
      anorm_ty. reflexivity.
    + anorm_ty.
      pose proof (avar_nth _ 0 _ HW2 eq_refl) as Hv. anorm_ty. exact Hv.
    + anorm_ty. reflexivity.
  - reflexivity.
Qed.

Lemma arecursive_method_formation : forall Gamma IT X P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing Gamma (arecursive_method IT X P) (Raw.TSort 0).
Proof.
  intros Gamma IT X P HI HX HP; unfold arecursive_method.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply ty_pi; [exact HI|eapply arec_codomain_formation; eassumption].
Qed.

(* ---- pair / motive application at base context ---- *)

Lemma atotal_pair_typing : forall Gamma IT X i x,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma i (erase IT) ->
  typing Gamma x (Raw.TApp (erase X) (erase i)) ->
  typing Gamma (atotal_pair IT X i x) (erase (atotal IT X)).
Proof.
  intros Gamma IT X i x HI HX Hi Hx; unfold atotal_pair.
  apply apair_conv with (j:=0) (k:=0); try assumption.
  - eapply afam_binder_typing; eassumption.
  - anorm_ty. exact Hx.
  - anorm_ty. reflexivity.
Qed.

Lemma amotive_app_typing : forall Gamma IT X P p,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing Gamma p (erase (atotal IT X)) ->
  typing Gamma (amotive_app IT X P p) (Raw.TSort 0).
Proof.
  intros Gamma IT X P p HI HX HP Hp; unfold amotive_app.
  apply aapp_conv with (j:=0) (k:=1);
    [eapply atotal_formation; eassumption| | |exact Hp|reflexivity].
  - apply ty_sort. eapply awf_cons.
    + eapply typing_context; eapply atotal_formation; eassumption.
    + apply typing_erasure. eapply atotal_formation; eassumption.
  - rewrite erase_atotal. exact HP.
Qed.

(* (h i) x for h : recursive_method *)
Lemma arec_app_typing : forall Gamma IT X P h i x,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing Gamma h (erase (arecursive_method IT X P)) ->
  typing Gamma i (erase IT) ->
  typing Gamma x (Raw.TApp (erase X) (erase i)) ->
  typing Gamma (arec_app IT X P h i x)
    (Raw.TApp (erase P) (Raw.TPair (erase i) (erase x))).
Proof.
  intros Gamma IT X P h i x HI HX HP Hh Hi Hx; unfold arec_app.
  pose proof (afamily_app_typing _ _ _ _ HI HX Hi) as Hfam.
  assert (HW1 : RT.wf (erase (afamily_app IT X i) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; eassumption|
      apply typing_erasure; exact Hfam]. }
  apply aapp_conv with (j:=0) (k:=0).
  - exact Hfam.
  - (* codomain ann: P (i,x) under binder x : (X i) *)
    apply aapp_conv with (j:=0) (k:=1).
    + eapply atotal_formation.
      * exact (aweaken _ _ _ _ _ HI Hfam).
      * pose proof (aweaken _ _ _ _ _ HX Hfam) as HX1.
        anorm_ty. exact HX1.
    + apply ty_sort. eapply awf_cons; [exact HW1|].
      apply typing_erasure. eapply atotal_formation.
      * exact (aweaken _ _ _ _ _ HI Hfam).
      * pose proof (aweaken _ _ _ _ _ HX Hfam) as HX1.
        anorm_ty. exact HX1.
    + pose proof (aweaken _ _ _ _ _ HP Hfam) as HP1. anorm_ty. exact HP1.
    + (* pair (↑i, v0) *)
      apply apair_conv with (j:=0) (k:=0).
      * exact (aweaken _ _ _ _ _ HI Hfam).
      * (* ↑(X·v0) ann under the Sigma binder *)
        assert (HW2 : RT.wf
            (map erase [lift 1 0 IT; afamily_app IT X i] ++ Gamma)).
        { cbn [map app]. eapply awf_cons; [exact HW1|].
          apply typing_erasure. exact (aweaken _ _ _ _ _ HI Hfam). }
        eapply afamily_app_typing.
        -- pose proof (aweaken_by [lift 1 0 IT; afamily_app IT X i]
             _ _ _ HI HW2) as HI2'. anorm_ty. exact HI2'.
        -- pose proof (aweaken_by [lift 1 0 IT; afamily_app IT X i]
             _ _ _ HX HW2) as HX2. anorm_ty. exact HX2.
        -- eapply avar_typed; [exact HW2|reflexivity|].
           anorm_ty. reflexivity.
      * (* ↑i : X-part *)
        anorm_ty.
        pose proof (aweaken _ _ _ _ _ Hi Hfam) as Hi1.
        anorm_ty. exact Hi1.
      * (* v0 : subst (↑ei) 0 (ann) = ↑(X i) *)
        anorm_ty.
        pose proof (avar_nth _ 0 _ HW1 eq_refl) as Hv.
        anorm_ty. exact Hv.
      * anorm_ty. reflexivity.
    + reflexivity.
  - (* inner: h i *)
    apply aapp_conv with (j:=0) (k:=0).
    + exact HI.
    + eapply arec_codomain_formation; eassumption.
    + exact Hh.
    + exact Hi.
    + anorm_ty. reflexivity.
  - anorm_ty. exact Hx.
  - anorm_ty. reflexivity.
Qed.

(* ---- enum machinery ---- *)

Lemma atail_motive_typing : forall Gamma k tag E P,
  typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
  typing Gamma P (Raw.TPi (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
    (Raw.TSort k)) ->
  typing Gamma (atail_motive k tag E P)
    (Raw.TPi (Raw.TEnumT (erase E)) (Raw.TSort k)).
Proof.
  intros Gamma k tag E P Htag HE HP; unfold atail_motive.
  pose proof (ty_enumt _ _ HE) as HA.
  assert (HW : RT.wf (Raw.TEnumT (erase E) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HA|rty HA]. }
  apply ty_lam with (j:=0) (k:=S k).
  - exact HA.
  - pose proof (ty_sort _ k HW) as Hs. anorm_ty. exact Hs.
  - (* body: P (succ v0) *)
    apply aapp_conv with (j:=0) (k:=S k).
    + apply ty_enumt. apply ty_conse;
        exact (aweaken _ _ _ _ _ Htag HA) || exact (aweaken _ _ _ _ _ HE HA).
    + apply ty_sort. eapply awf_cons; [exact HW|].
      rty (ty_enumt _ _ (ty_conse _ _ _
        (aweaken _ _ _ _ _ Htag HA) (aweaken _ _ _ _ _ HE HA))).
    + pose proof (aweaken _ _ _ _ _ HP HA) as HP1. anorm_ty. exact HP1.
    + apply ty_succ.
      * exact (aweaken _ _ _ _ _ Htag HA).
      * exact (aweaken _ _ _ _ _ HE HA).
      * pose proof (avar_nth _ 0 _ HW eq_refl) as Hv. anorm_ty. exact Hv.
    + reflexivity.
Qed.

Lemma aepi_head_typing : forall Gamma k tag E P,
  typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
  typing Gamma P (Raw.TPi (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
    (Raw.TSort k)) ->
  typing Gamma (aepi_head k tag E P) (Raw.TSort k).
Proof.
  intros Gamma k tag E P Htag HE HP; unfold aepi_head.
  apply aapp_conv with (j:=0) (k:=S k).
  - apply ty_enumt. apply ty_conse; eassumption.
  - apply ty_sort. eapply awf_cons;
      [eapply typing_context; eapply ty_enumt; apply ty_conse; eassumption|].
    rty (ty_enumt _ _ (ty_conse _ _ _ Htag HE)).
  - exact HP.
  - apply ty_zero; eassumption.
  - reflexivity.
Qed.

Lemma aproduct_formation : forall Gamma A B j k,
  typing Gamma A (Raw.TSort j) -> typing Gamma B (Raw.TSort k) ->
  typing Gamma (aproduct A B) (Raw.TSort (Nat.max j k)).
Proof.
  intros Gamma A B j k HA HB; unfold aproduct.
  apply ty_sigma; [exact HA|].
  pose proof (aweaken _ _ _ _ _ HB HA) as HB'. anorm_ty. exact HB'.
Qed.

Lemma aepi_cons_reduct_typing : forall Gamma k tag E P,
  typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
  typing Gamma P (Raw.TPi (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
    (Raw.TSort k)) ->
  typing Gamma
    (aproduct (aepi_head k tag E P) (TEPi k E (atail_motive k tag E P)))
    (Raw.TSort k).
Proof.
  intros Gamma k tag E P Htag HE HP.
  replace (Raw.TSort k) with (Raw.TSort (Nat.max k k))
    by (rewrite Nat.max_id; reflexivity).
  apply aproduct_formation.
  - eapply aepi_head_typing; eassumption.
  - apply ty_epi; [exact HE|eapply atail_motive_typing; eassumption].
Qed.

(* ---- description binders ---- *)

Lemma adesc_app_binder_typing : forall Gamma IT A D,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing (erase A :: Gamma) (adesc_app_binder IT A D)
    (Raw.TIDesc (Raw.lift 1 0 (erase IT))).
Proof.
  intros Gamma IT A D HI HA HD; unfold adesc_app_binder.
  assert (HW : RT.wf (erase A :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HA|
      apply typing_erasure; exact HA]. }
  assert (HW2 : RT.wf (map erase [lift 1 0 A; A] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW|].
    apply typing_erasure. exact (aweaken _ _ _ _ _ HA HA). }
  apply aapp_conv with (j:=0) (k:=1).
  - exact (aweaken _ _ _ _ _ HA HA).
  - apply ty_idesc. exact (aweaken_by [lift 1 0 A; A] _ _ _ HI HW2).
  - pose proof (aweaken _ _ _ _ _ HD HA) as HD1. anorm_ty. exact HD1.
  - pose proof (avar_nth _ 0 _ HW eq_refl) as Hv. anorm_ty. exact Hv.
  - anorm_ty. reflexivity.
Qed.

Lemma adesc_app_binder_enum_typing : forall Gamma IT E D,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma E Raw.TEnumU ->
  typing Gamma D (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT))) ->
  typing (Raw.TEnumT (erase E) :: Gamma) (adesc_app_binder_enum IT E D)
    (Raw.TIDesc (Raw.lift 1 0 (erase IT))).
Proof.
  intros Gamma IT E D HI HE HD; unfold adesc_app_binder_enum.
  pose proof (ty_enumt _ _ HE) as HEt.
  assert (HW : RT.wf (Raw.TEnumT (erase E) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HEt|rty HEt]. }
  assert (HW2 : RT.wf
      (map erase [TEnumT (lift 1 0 E); TEnumT E] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW|].
    rty (ty_enumt _ _ (aweaken _ _ _ _ _ HE HEt)). }
  apply aapp_conv with (j:=0) (k:=1).
  - apply ty_enumt. exact (aweaken _ _ _ _ _ HE HEt).
  - apply ty_idesc.
    exact (aweaken_by [TEnumT (lift 1 0 E); TEnumT E] _ _ _ HI HW2).
  - pose proof (aweaken _ _ _ _ _ HD HEt) as HD1. anorm_ty. exact HD1.
  - pose proof (avar_nth _ 0 _ HW eq_refl) as Hv. anorm_ty. exact Hv.
  - anorm_ty. reflexivity.
Qed.

Lemma ainterp_binder_typing : forall Gamma IT A D X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing (erase A :: Gamma) (ainterp_binder IT A D X) (Raw.TSort 0).
Proof.
  intros Gamma IT A D X HI HA HD HX; unfold ainterp_binder.
  apply ty_interp.
  - exact (aweaken _ _ _ _ _ HI HA).
  - pose proof (adesc_app_binder_typing _ _ _ _ HI HA HD) as H. anorm_ty.
    exact H.
  - pose proof (aweaken _ _ _ _ _ HX HA) as HX1. anorm_ty. exact HX1.
Qed.

Lemma ainterp_binder_enum_typing : forall Gamma IT E D X,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma E Raw.TEnumU ->
  typing Gamma D (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT))) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing (Raw.TEnumT (erase E) :: Gamma) (ainterp_binder_enum IT E D X)
    (Raw.TSort 0).
Proof.
  intros Gamma IT E D X HI HE HD HX; unfold ainterp_binder_enum.
  apply ty_interp.
  - pose proof (ty_enumt _ _ HE) as HEt. exact (aweaken _ _ _ _ _ HI HEt).
  - pose proof (adesc_app_binder_enum_typing _ _ _ _ HI HE HD) as H.
    anorm_ty. exact H.
  - pose proof (ty_enumt _ _ HE) as HEt.
    pose proof (aweaken _ _ _ _ _ HX HEt) as HX1. anorm_ty. exact HX1.
Qed.

(* f #0 under one binder *)
Lemma aapp_binder_typing : forall Gamma IT A D X f,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma f
    (Raw.TPi (erase A)
      (Raw.TInterp (Raw.lift 1 0 (erase IT))
        (Raw.TApp (Raw.lift 1 0 (erase D)) (Raw.TVar 0))
        (Raw.lift 1 0 (erase X)))) ->
  typing (erase A :: Gamma) (aapp_binder IT A D X f)
    (Raw.TInterp (Raw.lift 1 0 (erase IT))
      (Raw.TApp (Raw.lift 1 0 (erase D)) (Raw.TVar 0))
      (Raw.lift 1 0 (erase X))).
Proof.
  intros Gamma IT A D X f HI HA HD HX Hf; unfold aapp_binder.
  assert (HW : RT.wf (erase A :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HA|
      apply typing_erasure; exact HA]. }
  assert (HW2 : RT.wf (map erase [lift 1 0 A; A] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW|].
    apply typing_erasure. exact (aweaken _ _ _ _ _ HA HA). }
  apply aapp_conv with (j:=0) (k:=0).
  - exact (aweaken _ _ _ _ _ HA HA).
  - (* codomain: Interp ↑²IT ((↑²D) #0) ↑²X *)
    apply ty_interp.
    + exact (aweaken_by [lift 1 0 A; A] _ _ _ HI HW2).
    + (* (↑²D) #0 : IDesc ↑²IT *)
      assert (HW3 : RT.wf
          (map erase [lift 2 0 A; lift 1 0 A; A] ++ Gamma)).
      { cbn [map app]. eapply awf_cons; [exact HW2|].
        rty (aweaken_by [lift 1 0 A; A] _ _ _ HA HW2). }
      apply aapp_conv with (j:=0) (k:=1).
      * exact (aweaken_by [lift 1 0 A; A] _ _ _ HA HW2).
      * apply ty_idesc.
        exact (aweaken_by [lift 2 0 A; lift 1 0 A; A] _ _ _ HI HW3).
      * pose proof (aweaken_by [lift 1 0 A; A] _ _ _ HD HW2) as HD2.
        anorm_ty. exact HD2.
      * pose proof (avar_nth _ 0 _ HW2 eq_refl) as Hv.
        cbn [map app] in Hv. anorm_ty. exact Hv.
      * anorm_ty. reflexivity.
    + pose proof (aweaken_by [lift 1 0 A; A] _ _ _ HX HW2) as HX2.
      anorm_ty. exact HX2.
  - pose proof (aweaken _ _ _ _ _ Hf HA) as Hf1. anorm_ty. exact Hf1.
  - pose proof (avar_nth _ 0 _ HW eq_refl) as Hv. anorm_ty. exact Hv.
  - anorm_ty. reflexivity.
Qed.

(* context transport on the head entry *)
Lemma actx_head : forall Gamma U V t T,
  U = V -> typing (U :: Gamma) t T -> typing (V :: Gamma) t T.
Proof. intros; subst; assumption. Qed.

(* sort-typed substitution at cutoff 0/1/2/3 for subst-instance annotations *)
Lemma asubst0 : forall Gamma u S B k,
  typing (erase S :: Gamma) B (Raw.TSort k) -> typing Gamma u (erase S) ->
  typing Gamma (subst u 0 B) (Raw.TSort k).
Proof.
  intros Gamma u S B k HB Hu.
  pose proof (substitution _ _ _ _ _ HB Hu) as H.
  cbn [Raw.subst] in H. exact H.
Qed.

Lemma asubst1 : forall Gamma u S B ann j k,
  typing (erase S :: Gamma) B (Raw.TSort j) ->
  typing (erase B :: erase S :: Gamma) ann (Raw.TSort k) ->
  typing Gamma u (erase S) ->
  typing (erase (subst u 0 B) :: Gamma) (subst u 1 ann) (Raw.TSort k).
Proof.
  intros Gamma u S B ann j k HB Hann Hu.
  pose proof (asubst0 _ _ _ _ _ HB Hu) as HB0.
  assert (HW : RT.wf (Raw.subst (erase u) 0 (erase B) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact Hu|].
    pose proof (typing_erasure _ _ _ HB0) as HBe.
    rewrite !erase_subst in HBe. exact HBe. }
  assert (HE : environment_subst 1 u (erase B :: erase S :: Gamma)
      (Raw.subst (erase u) 0 (erase B) :: Gamma)).
  { eapply environment_subst_cons.
    - apply environment_subst_head. exact Hu.
    - pose proof (typing_erasure _ _ _ HB0) as HBe.
      rewrite !erase_subst in HBe. exact HBe. }
  pose proof (typing_subst _ _ _ Hann 1 u
      (Raw.subst (erase u) 0 (erase B) :: Gamma) HW HE) as H.
  cbn [Raw.subst] in H.
  eapply actx_head; [|exact H].
  symmetry. apply erase_subst.
Qed.

Lemma asubst2 : forall Gamma u S B1 B2 ann j1 j2 k,
  typing (erase S :: Gamma) B1 (Raw.TSort j1) ->
  typing (erase B1 :: erase S :: Gamma) B2 (Raw.TSort j2) ->
  typing (erase B2 :: erase B1 :: erase S :: Gamma) ann (Raw.TSort k) ->
  typing Gamma u (erase S) ->
  typing (erase (subst u 1 B2) :: erase (subst u 0 B1) :: Gamma)
    (subst u 2 ann) (Raw.TSort k).
Proof.
  intros Gamma u S B1 B2 ann j1 j2 k HB1 HB2 Hann Hu.
  pose proof (asubst0 _ _ _ _ _ HB1 Hu) as HB10.
  pose proof (asubst1 _ _ _ _ _ _ _ HB1 HB2 Hu) as HB21.
  assert (HW : RT.wf (Raw.subst (erase u) 1 (erase B2)
      :: Raw.subst (erase u) 0 (erase B1) :: Gamma)).
  { eapply awf_cons.
    - eapply awf_cons; [eapply typing_context; exact Hu|].
      pose proof (typing_erasure _ _ _ HB10) as HBe.
      rewrite !erase_subst in HBe. exact HBe.
    - pose proof (typing_erasure _ _ _ HB21) as HBe.
      rewrite !erase_subst in HBe. exact HBe. }
  assert (HE : environment_subst 2 u
      (erase B2 :: erase B1 :: erase S :: Gamma)
      (Raw.subst (erase u) 1 (erase B2)
        :: Raw.subst (erase u) 0 (erase B1) :: Gamma)).
  { eapply environment_subst_cons.
    - eapply environment_subst_cons.
      + apply environment_subst_head. exact Hu.
      + pose proof (typing_erasure _ _ _ HB10) as HBe.
        rewrite !erase_subst in HBe. exact HBe.
    - pose proof (typing_erasure _ _ _ HB21) as HBe.
      rewrite !erase_subst in HBe. exact HBe. }
  pose proof (typing_subst _ _ _ Hann 2 u _ HW HE) as H.
  cbn [Raw.subst] in H. rewrite !erase_subst. exact H.
Qed.

Lemma asubst3 : forall Gamma u S B1 B2 B3 ann j1 j2 j3 k,
  typing (erase S :: Gamma) B1 (Raw.TSort j1) ->
  typing (erase B1 :: erase S :: Gamma) B2 (Raw.TSort j2) ->
  typing (erase B2 :: erase B1 :: erase S :: Gamma) B3 (Raw.TSort j3) ->
  typing (erase B3 :: erase B2 :: erase B1 :: erase S :: Gamma) ann
    (Raw.TSort k) ->
  typing Gamma u (erase S) ->
  typing (erase (subst u 2 B3) :: erase (subst u 1 B2)
    :: erase (subst u 0 B1) :: Gamma) (subst u 3 ann) (Raw.TSort k).
Proof.
  intros Gamma u S B1 B2 B3 ann j1 j2 j3 k HB1 HB2 HB3 Hann Hu.
  pose proof (asubst0 _ _ _ _ _ HB1 Hu) as HB10.
  pose proof (asubst1 _ _ _ _ _ _ _ HB1 HB2 Hu) as HB21.
  pose proof (asubst2 _ _ _ _ _ _ _ _ _ HB1 HB2 HB3 Hu) as HB32.
  assert (HW : RT.wf (Raw.subst (erase u) 2 (erase B3)
      :: Raw.subst (erase u) 1 (erase B2)
      :: Raw.subst (erase u) 0 (erase B1) :: Gamma)).
  { eapply awf_cons.
    - eapply awf_cons.
      + eapply awf_cons; [eapply typing_context; exact Hu|].
        pose proof (typing_erasure _ _ _ HB10) as HBe.
        rewrite !erase_subst in HBe. exact HBe.
      + pose proof (typing_erasure _ _ _ HB21) as HBe.
        rewrite !erase_subst in HBe. exact HBe.
    - pose proof (typing_erasure _ _ _ HB32) as HBe.
      rewrite !erase_subst in HBe. exact HBe. }
  assert (HE : environment_subst 3 u
      (erase B3 :: erase B2 :: erase B1 :: erase S :: Gamma)
      (Raw.subst (erase u) 2 (erase B3) :: Raw.subst (erase u) 1 (erase B2)
        :: Raw.subst (erase u) 0 (erase B1) :: Gamma)).
  { eapply environment_subst_cons.
    - eapply environment_subst_cons.
      + eapply environment_subst_cons.
        * apply environment_subst_head. exact Hu.
        * pose proof (typing_erasure _ _ _ HB10) as HBe.
          rewrite !erase_subst in HBe. exact HBe.
      + pose proof (typing_erasure _ _ _ HB21) as HBe.
        rewrite !erase_subst in HBe. exact HBe.
    - pose proof (typing_erasure _ _ _ HB32) as HBe.
      rewrite !erase_subst in HBe. exact HBe. }
  pose proof (typing_subst _ _ _ Hann 3 u _ HW HE) as H.
  cbn [Raw.subst] in H. rewrite !erase_subst. exact H.
Qed.

(* ---- mu induction pieces ---- *)

(* payload binder: Interp ↑IT ((↑D) #0) (μ ↑IT ↑D) at ctx [i:eIT]::Γ *)
Lemma amu_payload_formation : forall Gamma IT D,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing (erase IT :: Gamma) (amu_payload IT D) (Raw.TSort 0).
Proof.
  intros Gamma IT D HI HD; unfold amu_payload.
  assert (HW : RT.wf (erase IT :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|rty HI]. }
  apply ty_interp.
  - exact (aweaken _ _ _ _ _ HI HI).
  - eapply adef_app_typing.
    + exact (aweaken _ _ _ _ _ HI HI).
    + pose proof (aweaken _ _ _ _ _ HD HI) as HD1. anorm_ty. exact HD1.
    + pose proof (avar_nth _ 0 _ HW eq_refl) as Hv. anorm_ty. exact Hv.
  - apply ty_mui.
    + exact (aweaken _ _ _ _ _ HI HI).
    + pose proof (aweaken _ _ _ _ _ HD HI) as HD1. anorm_ty. exact HD1.
Qed.

(* iall binder at ctx [xs:payload, i:eIT] *)
Lemma amu_iall_formation : forall Gamma IT D P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing (map erase [amu_payload IT D; IT] ++ Gamma)
    (amu_iall IT D P) (Raw.TSort 0).
Proof.
  intros Gamma IT D P HI HD HP.
  pose proof (amu_payload_formation _ _ _ HI HD) as Hpl.
  assert (HW1 : RT.wf (erase IT :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|rty HI]. }
  assert (HW2 : RT.wf (map erase [amu_payload IT D; IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|rty Hpl]. }
  unfold amu_iall. apply ty_iall.
  - exact (aweaken_by [amu_payload IT D; IT] _ _ _ HI HW2).
  - eapply adef_app_typing.
    + exact (aweaken_by [amu_payload IT D; IT] _ _ _ HI HW2).
    + pose proof (aweaken_by [amu_payload IT D; IT] _ _ _ HD HW2) as HD2.
      anorm_ty. exact HD2.
    + eapply avar_typed; [exact HW2|reflexivity|]. anorm_ty. reflexivity.
  - apply ty_mui.
    + exact (aweaken_by [amu_payload IT D; IT] _ _ _ HI HW2).
    + pose proof (aweaken_by [amu_payload IT D; IT] _ _ _ HD HW2) as HD2.
      anorm_ty. exact HD2.
  - eapply avar_typed; [exact HW2|reflexivity|]. anorm_ty. reflexivity.
  - pose proof (aweaken_by [amu_payload IT D; IT] _ _ _ HP HW2) as HP2.
    anorm_ty. exact HP2.
Qed.

(* result at ctx [h:iall, x:payload, i:eIT]: (↑³P) (v2, in v1) *)
Lemma amu_result_formation : forall Gamma IT D P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing (map erase [amu_iall IT D P; amu_payload IT D; IT] ++ Gamma)
    (amu_result IT D P) (Raw.TSort 0).
Proof.
  intros Gamma IT D P HI HD HP.
  pose proof (amu_payload_formation _ _ _ HI HD) as Hpl.
  pose proof (amu_iall_formation _ _ _ _ HI HD HP) as Hil.
  assert (HW1 : RT.wf (erase IT :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|rty HI]. }
  assert (HW2 : RT.wf (map erase [amu_payload IT D; IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|rty Hpl]. }
  assert (HW3 : RT.wf
      (map erase [amu_iall IT D P; amu_payload IT D; IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW2|rty Hil]. }
  assert (HW4 : RT.wf (map erase
      [lift 3 0 IT; amu_iall IT D P; amu_payload IT D; IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW3|].
    rty (aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW3). }
  unfold amu_result.
  (* TApp (atotal ↑³IT ↑³μ) (Sort 0) ↑³P (pair) : Sort 0 *)
  apply aapp_conv with (j:=0) (k:=1).
  - (* atotal ↑³IT ↑³μ *)
    eapply atotal_formation.
    + exact (aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW3).
    + apply ty_mui.
      * exact (aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW3).
      * pose proof (aweaken_by [amu_iall IT D P; amu_payload IT D; IT]
          _ _ _ HD HW3) as HD3. anorm_ty. exact HD3.
  - apply ty_sort. eapply awf_cons; [exact HW3|].
    rty (atotal_formation _ _ _
      (aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW3)
      (ty_mui _ _ _
        (aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW3)
        (let h := aweaken_by [amu_iall IT D P; amu_payload IT D; IT] _ _ _ HD HW3 in
         ltac:(anorm_ty; exact h)))).
  - pose proof (aweaken_by [amu_iall IT D P; amu_payload IT D; IT]
      _ _ _ HP HW3) as HP3. anorm_ty. exact HP3.
  - (* pair (v2, in v1) *)
    apply apair_conv with (j:=0) (k:=0).
    + pose proof (aweaken_by [amu_iall IT D P; amu_payload IT D; IT]
        _ _ _ HI HW3) as HI3. anorm_ty. exact HI3.
    + (* ↑(X·v0) binder: afamily_app ↑(↑³IT) ↑(↑³μ) v0 *)
      eapply afamily_app_typing.
      * pose proof (aweaken_by
          [lift 3 0 IT; amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW4)
          as HI4. anorm_ty. exact HI4.
      * apply ty_mui.
        -- pose proof (aweaken_by
             [lift 3 0 IT; amu_iall IT D P; amu_payload IT D; IT] _ _ _ HI HW4)
             as HI4'. anorm_ty. exact HI4'.
        -- pose proof (aweaken_by
             [lift 3 0 IT; amu_iall IT D P; amu_payload IT D; IT] _ _ _ HD HW4)
             as HD4. anorm_ty. exact HD4.
      * eapply avar_typed; [exact HW4|reflexivity|]. anorm_ty. reflexivity.
    + (* v2 : e↑³IT *)
      eapply avar_typed; [exact HW3|reflexivity|]. anorm_ty. reflexivity.
    + (* in v1 : subst v2 0 (afamily-ann) = (↑³μ) v2 *)
      replace (Raw.subst (erase (TVar 2)) 0
          (erase (afamily_app (lift 1 0 (lift 3 0 IT))
            (lift 1 0 (TMuI (lift 3 0 IT) (lift 3 0 D))) (TVar 0))))
        with (Raw.MuAt (erase (lift 3 0 IT)) (erase (lift 3 0 D)) (Raw.TVar 2))
        by (unfold Raw.MuAt; anorm_ty; reflexivity).
      apply ty_in_mui.
      * pose proof (aweaken_by [amu_iall IT D P; amu_payload IT D; IT]
          _ _ _ HI HW3) as HI3'. anorm_ty. exact HI3'.
      * pose proof (aweaken_by [amu_iall IT D P; amu_payload IT D; IT]
          _ _ _ HD HW3) as HD3. anorm_ty. exact HD3.
      * eapply avar_typed; [exact HW3|reflexivity|]. anorm_ty. reflexivity.
      * (* v1 : Interp ↑³IT (↑³D·v2) μ↑³ *)
        eapply avar_typed; [exact HW3|reflexivity|]. anorm_ty. reflexivity.
    + anorm_ty. reflexivity.
  - anorm_ty. reflexivity.
Qed.

Lemma amu_ind_codomain_formation : forall Gamma IT D P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing (erase IT :: Gamma) (amu_ind_codomain IT D P) (Raw.TSort 0).
Proof.
  intros Gamma IT D P HI HD HP; unfold amu_ind_codomain.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 (Nat.max 0 0))).
  apply ty_pi.
  - eapply amu_payload_formation; eassumption.
  - change (Nat.max 0 0) with (Nat.max 0 0 : nat).
    apply ty_pi.
    + eapply amu_iall_formation; eassumption.
    + eapply amu_result_formation; eassumption.
Qed.

Lemma amu_ind_method_formation : forall Gamma IT D P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma (amu_ind_method IT D P) (Raw.TSort 0).
Proof.
  intros Gamma IT D P HI HD HP; unfold amu_ind_method.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply ty_pi; [exact HI|eapply amu_ind_codomain_formation; eassumption].
Qed.

(* ---- comparison inversion on rigid-headed types ---- *)

Ltac cmp_contra :=
  exfalso;
  lazymatch goal with
  | HC : RCore.conv ?X (Raw.TSort _) |- _ =>
    pose proof (RG.conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate
  | HC : RCore.conv ?X (Raw.TPi _ _) |- _ =>
    pose proof (RG.conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate
  end.

Lemma acmp_idesc : forall a b,
  RC.type_comparison (Raw.TIDesc a) (Raw.TIDesc b) -> RCore.conv a b.
Proof.
  intros a b H; inversion H; subst;
    [apply RCG.conversion_idesc; assumption|cmp_contra|cmp_contra].
Qed.

Lemma acmp_sigma : forall A B C D,
  RC.type_comparison (Raw.TSigma A B) (Raw.TSigma C D) ->
  RC.type_comparison A C /\ RC.type_comparison B D.
Proof.
  intros A B C D H; inversion H; subst.
  - destruct (RG.conversion_sigma _ _ _ _ H0) as [HAC HBD].
    split; apply RC.cmp_conversion; assumption.
  - cmp_contra.
  - cmp_contra.
Qed.

Lemma acmp_muat : forall IT D i JT E j,
  RC.type_comparison (Raw.MuAt IT D i) (Raw.MuAt JT E j) ->
  RCore.conv IT JT /\ RCore.conv D E /\ RCore.conv i j.
Proof.
  intros IT D i JT E j H; inversion H; subst;
    [apply RM.conversion_mu_at; assumption|cmp_contra|cmp_contra].
Qed.

Lemma acmp_closeat : forall IT F G i JT H K j,
  RC.type_comparison (Raw.CloseAt IT F G i) (Raw.CloseAt JT H K j) ->
  RCore.conv IT JT /\ RCore.conv F H /\ RCore.conv G K /\ RCore.conv i j.
Proof.
  intros IT F G i JT H K j HC; inversion HC; subst;
    [apply RCL.conversion_close_at; assumption|cmp_contra|cmp_contra].
Qed.

Lemma acmp_enumt : forall a b,
  RC.type_comparison (Raw.TEnumT a) (Raw.TEnumT b) -> RCore.conv a b.
Proof.
  intros a b HC; inversion HC; subst;
    [apply RCG.conversion_enumt; assumption|cmp_contra|cmp_contra].
Qed.

(* from a pair typed at an interpretable description, extract component
   typings at the Sigma reduct's annotations *)
Lemma ainterpreted_pair : forall Gamma IT D X S0 S1 C D0 a b k,
  typing Gamma (TPair C D0 a b) (Raw.TInterp (erase IT) (erase D) (erase X)) ->
  structural_root (TInterp IT D X) (TSigma S0 S1) ->
  RT.typing Gamma (Raw.TSigma (erase S0) (erase S1)) (Raw.TSort k) ->
  typing Gamma a (erase S0) /\
  typing Gamma b (Raw.subst (erase a) 0 (erase S1)).
Proof.
  intros Gamma IT D X S0 S1 C D0 a b k Hp Hr HSg.
  assert (Hp' : typing Gamma (TPair C D0 a b)
      (Raw.TSigma (erase S0) (erase S1))).
  { eapply ty_conv; [exact Hp|exact HSg|].
    apply RW.reduction_conversion.
    exact (structural_root_erasure _ _ Hr). }
  destruct (pair_generation _ _ _ Hp' _ _ _ _ eq_refl)
    as [j [l [HC [HD0 [Ha [Hb Hcmp]]]]]].
  destruct (acmp_sigma _ _ _ _ Hcmp) as [Hc1 Hc2].
  destruct (DT.sigma_components _ _ _ HSg _ _ eq_refl) as [j' [l' [HS0 HS1]]].
  split.
  - eapply comparison_typing; [exact Ha|exact Hc1|exists j'; exact HS0].
  - eapply comparison_typing; [exact Hb| |].
    + exact (RC.comparison_subst _ _ Hc2 (erase a) 0).
    + exists l'.
      pose proof (comparison_typing _ _ _ _ Ha Hc1 (ex_intro _ j' HS0)) as Ha'.
      pose proof (typing_erasure _ _ _ Ha') as Hae.
      pose proof (RS.substitution _ _ _ _ _ HS1 Hae) as Hsub.
      exact Hsub.
Qed.

(* the isig/ichoice instantiation D a : IDesc IT *)
Lemma ainstantiate_typing : forall Gamma IT A D a,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing Gamma a (erase A) ->
  typing Gamma (ainstantiate IT A D a) (Raw.TIDesc (erase IT)).
Proof.
  intros Gamma IT A D a HI HA HD Ha; unfold ainstantiate.
  apply aapp_conv with (j:=0) (k:=1).
  - exact HA.
  - apply ty_idesc. exact (aweaken _ _ _ _ _ HI HA).
  - pose proof HD as HD'. anorm_ty. exact HD'.
  - exact Ha.
  - anorm_ty. reflexivity.
Qed.

Lemma ainstantiate_enum_typing : forall Gamma IT E D e,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma E Raw.TEnumU ->
  typing Gamma D (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT))) ->
  typing Gamma e (Raw.TEnumT (erase E)) ->
  typing Gamma (ainstantiate_enum IT E D e) (Raw.TIDesc (erase IT)).
Proof.
  intros Gamma IT E D e HI HE HD He; unfold ainstantiate_enum.
  apply aapp_conv with (j:=0) (k:=1).
  - apply ty_enumt; exact HE.
  - apply ty_idesc.
    exact (aweaken _ _ _ _ _ HI (ty_enumt _ _ HE)).
  - pose proof HD as HD'. anorm_ty. exact HD'.
  - exact He.
  - anorm_ty. reflexivity.
Qed.

(* dependent-iall under one binder: IAll ↑IT ((↑D)#0) ↑X ((↑f)#0) ↑P *)
Lemma aiall_binder_typing : forall Gamma IT A D X f P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma f (Raw.TPi (erase A)
    (Raw.TInterp (Raw.lift 1 0 (erase IT))
      (Raw.TApp (Raw.lift 1 0 (erase D)) (Raw.TVar 0))
      (Raw.lift 1 0 (erase X)))) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing (erase A :: Gamma) (aiall_binder IT A D X f P) (Raw.TSort 0).
Proof.
  intros Gamma IT A D X f P HI HA HD HX Hf HP; unfold aiall_binder.
  apply ty_iall.
  - exact (aweaken _ _ _ _ _ HI HA).
  - pose proof (adesc_app_binder_typing _ _ _ _ HI HA HD) as HB1.
    anorm_ty. exact HB1.
  - pose proof (aweaken _ _ _ _ _ HX HA) as HX1. anorm_ty. exact HX1.
  - pose proof (aapp_binder_typing _ _ _ _ _ _ HI HA HD HX Hf) as Hf1.
    anorm_ty. exact Hf1.
  - pose proof (aweaken _ _ _ _ _ HP HA) as HP1. anorm_ty. exact HP1.
Qed.

(* the body of the ipi hyps step: its type is the iall binder *)
Lemma ahyps_binder_typing : forall Gamma IT A D X P h f,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma f (Raw.TPi (erase A)
    (Raw.TInterp (Raw.lift 1 0 (erase IT))
      (Raw.TApp (Raw.lift 1 0 (erase D)) (Raw.TVar 0))
      (Raw.lift 1 0 (erase X)))) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing Gamma h (Raw.recursive_method (erase IT) (erase X) (erase P)) ->
  typing (erase A :: Gamma) (ahyps_binder IT A D X P h f)
    (erase (aiall_binder IT A D X f P)).
Proof.
  intros Gamma IT A D X P h f HI HA HD HX Hf HP Hh; unfold ahyps_binder.
  apply ty_hyps.
  - exact (aweaken _ _ _ _ _ HI HA).
  - pose proof (adesc_app_binder_typing _ _ _ _ HI HA HD) as H.
    anorm_ty. exact H.
  - pose proof (aweaken _ _ _ _ _ HX HA) as HX1. anorm_ty. exact HX1.
  - pose proof (aweaken _ _ _ _ _ HP HA) as HP1. anorm_ty. exact HP1.
  - pose proof (aweaken _ _ _ _ _ Hh HA) as Hh1. anorm_ty. exact Hh1.
  - pose proof (aapp_binder_typing _ _ _ _ _ _ HI HA HD HX Hf) as H.
    anorm_ty. exact H.
Qed.

(* conversion of the IDesc argument inside an interpretation type *)
Lemma ainterp_desc_conv : forall Gamma IT D D' X x,
  typing Gamma x (Raw.TInterp (erase IT) (erase D') (erase X)) ->
  RT.typing Gamma (Raw.TInterp (erase IT) (erase D) (erase X)) (Raw.TSort 0) ->
  RCore.conv (erase D') (erase D) ->
  typing Gamma x (Raw.TInterp (erase IT) (erase D) (erase X)).
Proof.
  intros Gamma IT D D' X x Hx HF HC; eapply ty_conv; [exact Hx|exact HF|].
  apply RCore.cv_compatible, Raw.cp_TInterp;
    [apply RCore.cv_refl|exact HC|apply RCore.cv_refl].
Qed.

(* the pair of recursive calls in the iprod hyps step *)
Lemma ahyps_prod_pair_typing : forall Gamma IT A B X P h a b,
  typing Gamma IT (Raw.TSort 0) ->
  typing Gamma A (Raw.TIDesc (erase IT)) ->
  typing Gamma B (Raw.TIDesc (erase IT)) ->
  typing Gamma X (Raw.Family (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (erase X)) ->
  typing Gamma h (Raw.recursive_method (erase IT) (erase X) (erase P)) ->
  typing Gamma a (Raw.TInterp (erase IT) (erase A) (erase X)) ->
  typing Gamma b (Raw.TInterp (erase IT) (erase B) (erase X)) ->
  typing Gamma (ahyps_prod_pair IT A B X P h a b)
    (Raw.TIAll (erase IT) (Raw.TIProd (erase A) (erase B)) (erase X)
      (Raw.TPair (erase a) (erase b)) (erase P)).
Proof.
  intros Gamma IT A B X P h a b HI HA HB HX HP Hh Ha Hb.
  assert (HIa : typing Gamma (TIAll IT A X a P) (Raw.TSort 0))
    by (apply ty_iall; assumption).
  assert (HIb : typing Gamma (TIAll IT B X b P) (Raw.TSort 0))
    by (apply ty_iall; assumption).
  pose proof (ty_interp _ _ _ _ HI HA HX) as HTa.
  pose proof (ty_interp _ _ _ _ HI HB HX) as HTb.
  eapply ty_conv.
  - unfold ahyps_prod_pair.
    apply apair_conv with (j:=0) (k:=0).
    + exact HIa.
    + exact (aweaken _ _ _ _ _ HIb HIa).
    + apply ty_hyps; assumption.
    + anorm_ty. apply ty_hyps; assumption.
    + reflexivity.
  - apply RT.ty_iall.
    + rty HI.
    + apply RT.ty_iprod with (formation_level:=1);
        [rty HI|rty HA|rty HB|].
      apply RT.ty_idesc. rty HI.
    + rty HX.
    + (* the pair at the product interpretation *)
      eapply RT.ty_conv.
      * apply RT.ty_pair with (k:=0).
        -- rty (ty_sigma _ _ _ _ _ HTa (aweaken _ _ _ _ _ HTb HTa)).
        -- rty Ha.
        -- eapply RT.ty_conv; [rty Hb| |].
           ++ pose proof (aweaken _ _ _ _ _ HTb HTa) as Hw.
              pose proof (typing_erasure _ _ _ Hw) as H1.
              pose proof (typing_erasure _ _ _ Ha) as H2.
              pose proof (RS.substitution _ _ _ _ _ H1 H2) as H3.
              anorm_ty. exact H3.
           ++ anorm_ty. apply RCore.cv_refl.
      * (* target formation: TInterp eIT (TIProd eA eB) eX *)
        rty (ty_interp _ _ _ _ HI (ty_iprod _ _ _ _ HI HA HB) HX).
      * anorm_ty.
        apply RCore.cv_sym, RCore.cv_step, RCore.st_root. reflexivity.
    + rty HP.
  - rewrite erase_lift.
    apply RCore.cv_sym, RCore.cv_step, RCore.st_root. reflexivity.
Qed.





(* ---- mu induction spine ---- *)

(* the recursive lambda λi.λx. Ind (↑²IT)(↑²D)(↑²P)(↑²st) i x *)
Lemma amu_rec_lam_typing : forall Gamma IT D P st,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) ->
  typing Gamma (amu_rec_lam IT D P st)
    (Raw.recursive_method (erase IT) (Raw.TMuI (erase IT) (erase D)) (erase P)).
Proof.
  intros Gamma IT D P st HI HD HP HS;
  unfold amu_rec_lam, amu_rec_body.
  replace (Raw.recursive_method (erase IT) (Raw.TMuI (erase IT) (erase D))
      (erase P))
    with (erase (arecursive_method IT (TMuI IT D) P))
    by (rewrite erase_arecursive_method; reflexivity).
  unfold arecursive_method; cbn [erase].
  pose proof (ty_mui _ _ _ HI HD) as HX.
  pose proof (afam_binder_typing _ _ _ HI HX) as Hdom.
  pose proof (awf_cons _ _ _ (typing_context _ _ _ HI)
    (typing_erasure _ _ _ HI)) as HW1.
  pose proof (awf_cons _ _ _ HW1 (typing_erasure _ _ _ Hdom)) as HW2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0); IT] _ _ _ HI HW2) as HI2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0); IT] _ _ _ HD HW2) as HD2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0); IT] _ _ _ HP HW2) as HP2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0); IT] _ _ _ HS HW2) as HS2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0); IT] _ _ _ HX HW2) as HX2.
  pose proof (avar_nth _ 1 _ HW2 eq_refl) as Hi2.
  pose proof (avar_nth _ 0 _ HW2 eq_refl) as Hx2.
  apply ty_lam with (j:=0) (k:=0).
  - exact HI.
  - apply arec_codomain_formation; [exact HI|exact HX|exact HP].
  - apply ty_lam with (j:=0) (k:=0); [exact Hdom| |].
    + (* codomain annotation (↑²P)(v1,v0) : Sort 0 *)
      apply aapp_conv with (j:=0) (k:=1).
      * apply atotal_formation;
          [exact HI2|].
        pose proof HX2 as H'. anorm_ty. exact H'.
      * apply ty_sort. eapply awf_cons; [exact HW2|].
        apply typing_erasure. apply atotal_formation;
          [exact HI2|].
        pose proof HX2 as H'. anorm_ty. exact H'.
      * pose proof HP2 as H'. anorm_ty. exact H'.
      * (* pair (v1, v0) : e(atotal ↑²IT ↑²μ) *)
        apply atotal_pair_typing.
        -- exact HI2.
        -- pose proof HX2 as H'. anorm_ty. exact H'.
        -- pose proof Hi2 as H'. anorm_ty. exact H'.
        -- pose proof Hx2 as H'. anorm_ty. exact H'.
      * anorm_ty. reflexivity.
    + (* body TInd ↑²IT ↑²D ↑²P ↑²st v1 v0 *)
      apply ty_ind.
      * exact HI2.
      * pose proof HD2 as H'. anorm_ty. exact H'.
      * pose proof HP2 as H'. anorm_ty. exact H'.
      * pose proof HS2 as H'. anorm_ty. exact H'.
      * pose proof Hi2 as H'. anorm_ty. exact H'.
      * pose proof Hx2 as H'. anorm_ty. exact H'.
Qed.

(* st i xs hs : P (i, in xs) — three applications with subst-instance
   annotations *)
Lemma amethod_app_typing : forall Gamma IT D P st i xs hs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) ->
  typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma hs (Raw.TIAll (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D)) (erase xs) (erase P)) ->
  typing Gamma (amethod_app IT D P st i xs hs)
    (Raw.TApp (erase P) (Raw.TPair (erase i) (Raw.TIn (erase xs)))).
Proof.
  intros Gamma IT D P st i xs hs HI HD HP HS Hi Hxs Hhs.
  pose proof (amu_payload_formation _ _ _ HI HD) as Hpay.
  pose proof (amu_iall_formation _ _ _ _ HI HD HP) as Hiall.
  pose proof (amu_result_formation _ _ _ _ HI HD HP) as Hres.
  pose proof (amu_ind_codomain_formation _ _ _ _ HI HD HP) as Hcod.
  (* annotation typings *)
  pose proof (ty_pi _ _ _ _ _ Hiall Hres) as Hpi2.
  pose proof (asubst1 _ _ _ _ _ _ _ Hpay Hpi2 Hi) as HB2.
  pose proof (asubst1 _ _ _ _ _ _ _ Hpay Hiall Hi) as HAiall.
  assert (Hxsn : typing Gamma xs (erase (subst i 0 (amu_payload IT D)))).
  { anorm_ty. exact Hxs. }
  assert (Hhsn : typing Gamma hs
      (erase (subst xs 0 (subst i 1 (amu_iall IT D P))))).
  { anorm_ty. exact Hhs. }
  pose proof (asubst0 _ _ _ _ _ HAiall Hxsn) as HA3.
  pose proof (asubst2 _ _ _ _ _ _ _ _ _ Hpay Hiall Hres Hi) as HB3sub.
  pose proof (asubst1 _ _ _ _ _ _ _ HAiall HB3sub Hxsn) as HB3.
  pose proof (asubst0 _ _ _ _ _ Hpay Hi) as HA2.
  (* st i *)
  assert (Hst1 : typing Gamma (TApp IT (amu_ind_codomain IT D P) st i)
      (Raw.TPi (erase (subst i 0 (amu_payload IT D)))
        (erase (subst i 1 (TPi (amu_iall IT D P) (amu_result IT D P)))))).
  { apply aapp_conv with (j:=0) (k:=0).
    - exact HI.
    - exact Hcod.
    - pose proof HS as H'. anorm_ty. exact H'.
    - exact Hi.
    - anorm_ty. reflexivity. }
  (* st i xs *)
  assert (Hst2 : typing Gamma
      (TApp (subst i 0 (amu_payload IT D))
        (subst i 1 (TPi (amu_iall IT D P) (amu_result IT D P)))
        (TApp IT (amu_ind_codomain IT D P) st i) xs)
      (Raw.TPi (erase (subst xs 0 (subst i 1 (amu_iall IT D P))))
        (erase (subst xs 1 (subst i 2 (amu_result IT D P)))))).
  { apply aapp_conv with (j:=0) (k:=0).
    - exact HA2.
    - exact HB2.
    - exact Hst1.
    - exact Hxsn.
    - anorm_ty. reflexivity. }
  (* st i xs hs *)
  unfold amethod_app.
  apply aapp_conv with (j:=0) (k:=0).
  - exact HA3.
  - exact HB3.
  - exact Hst2.
  - exact Hhsn.
  - anorm_ty. reflexivity.
Qed.

(* the hyps argument THyps IT (D i) μ P (rec-lam) xs *)
Lemma ahyps_mu_typing : forall Gamma IT D P st i xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) ->
  typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma (ahyps_mu IT D P st i xs)
    (Raw.TIAll (erase IT) (Raw.TApp (erase D) (erase i))
      (Raw.TMuI (erase IT) (erase D)) (erase xs) (erase P)).
Proof.
  intros Gamma IT D P st i xs HI HD HP HS Hi Hxs; unfold ahyps_mu.
  apply ty_hyps.
  - exact HI.
  - apply adef_app_typing; assumption.
  - apply ty_mui; assumption.
  - exact HP.
  - pose proof (amu_rec_lam_typing _ _ _ _ _ HI HD HP HS) as H.
    anorm_ty. exact H.
  - exact Hxs.
Qed.

(* the full mu-induction reduct *)
Lemma amu_ind_reduct_typing : forall Gamma IT D P st i xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) ->
  typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D))) ->
  typing Gamma (amu_ind_reduct IT D P st i xs)
    (Raw.TApp (erase P) (Raw.TPair (erase i) (Raw.TIn (erase xs)))).
Proof.
  intros; unfold amu_ind_reduct; eapply amethod_app_typing;
    try eassumption.
  eapply ahyps_mu_typing; eassumption.
Qed.

