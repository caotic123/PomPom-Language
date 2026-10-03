(* Preservation of every primitive annotated root computation.  Each lemma
   mirrors the corresponding raw beta theorem in DBEnumBeta /
   DBDescriptionBeta / DBMuBeta / DBInductionBeta: generation on the source
   typing supplies the components, the annotated macro layer types the
   reduct, and [comparison_typing] transports to the original target. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AMacroTyping annotated.ACloseTyping.
Import ListNotations.

(* components of a pair stored in an enum-pi telescope *)
Lemma aepi_pair_components : forall Gamma k tag E P A B p ps,
  typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
  typing Gamma P (Raw.TPi (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
    (Raw.TSort k)) ->
  typing Gamma (TPair A B p ps)
    (Raw.TEPi k (Raw.TConsE (erase tag) (erase E)) (erase P)) ->
  typing Gamma p (erase (aepi_head k tag E P)) /\
  typing Gamma ps
    (Raw.subst (erase p) 0 (erase (lift 1 0 (TEPi k E (atail_motive k tag E P))))).
Proof.
  intros Gamma k tag E P A B p ps Htag HE HP Hp.
  pose proof (aepi_cons_reduct_typing _ _ _ _ _ Htag HE HP) as HR.
  assert (Hp' : typing Gamma (TPair A B p ps)
      (erase (aproduct (aepi_head k tag E P) (TEPi k E (atail_motive k tag E P))))).
  { eapply ty_conv; [exact Hp| |].
    - rty HR.
    - apply RCore.cv_step, RCore.st_root.
      aroot_norm. cbn [RCore.root_step Raw.product]. reflexivity. }
  destruct (pair_generation _ _ _ Hp' _ _ _ _ eq_refl)
    as [j [l [HA [HB [Hp0 [Hps Hcmp]]]]]].
  destruct (acmp_sigma _ _ _ _ Hcmp) as [Hc1 Hc2].
  pose proof (typing_erasure _ _ _ HR) as HRt.
  destruct (DT.sigma_components _ _ _ HRt _ _ eq_refl)
    as [j' [l' [HS0 HS1]]].
  split.
  - eapply comparison_typing; [exact Hp0|exact Hc1|exists j'; exact HS0].
  - eapply comparison_typing; [exact Hps| |].
    + exact (RC.comparison_subst _ _ Hc2 (erase p) 0).
    + exists l'.
      pose proof (comparison_typing _ _ _ _ Hp0 Hc1 (ex_intro _ j' HS0)) as Hp1.
      pose proof (typing_erasure _ _ _ Hp1) as Hpe.
      pose proof (RS.substitution _ _ _ _ _ HS1 Hpe) as Hsub.
      exact Hsub.
Qed.

(* ---- enum roots ---- *)

Theorem aepi_beta : forall Gamma k E P u T,
  typing Gamma (TEPi k E P) T -> structural_root (TEPi k E P) u ->
  typing Gamma u T.
Proof.
  intros Gamma k E P u T HT HR.
  destruct (epi_generation _ _ _ HT I) as [k' [E' [P' [Heq [HE [HP Hcmp]]]]]].
  inversion Heq; subst k' E' P'; clear Heq.
  inversion HR; subst.
  - eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    eapply ty_cumul; [apply ty_unitT; eapply typing_context; exact HT|lia].
  - destruct (conse_generation _ _ _ HE I) as [tag' [E'' [Heq2 [Htag [HE0 _]]]]].
    inversion Heq2; subst tag' E''.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    exact (aepi_cons_reduct_typing _ _ _ _ _ Htag HE0 HP).
Qed.

Theorem aswitch_beta : forall Gamma k E P p e u T,
  typing Gamma (TSwitch k E P p e) T -> structural_root (TSwitch k E P p e) u ->
  typing Gamma u T.
Proof.
  intros Gamma k E P p e u T HT HR.
  destruct (switch_generation _ _ _ HT I)
    as [k' [E' [P' [p' [e' [Heq [HE [HP [Hp [He Hcmp]]]]]]]]]].
  inversion Heq; subst k' E' P' p' e'; clear Heq.
  inversion HR; subst.
  - (* switch on zero: reduct is the head component p *)
    destruct (conse_generation _ _ _ HE I) as [tag' [E'' [Heq2 [Htag [HE0 _]]]]].
    inversion Heq2; subst tag' E''.
    destruct (zero_generation _ _ _ He I) as [t0 [e0 [Heq3 [Ht0 [He0 Hcmp0]]]]].
    inversion Heq3; subst t0 e0.
    destruct (aepi_pair_components _ _ _ _ _ _ _ _ _ Htag HE0 HP Hp) as [Hhead _].
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    (* p : TApp eP TEZero; target comparison is TApp eP e(TEZero) *)
    exact Hhead.
  - (* switch on succ: reduct recurses on the tail *)
    destruct (conse_generation _ _ _ HE I) as [tag' [E'' [Heq2 [Htag [HE0 _]]]]].
    inversion Heq2; subst tag' E''.
    destruct (succ_generation _ _ _ He I)
      as [t0 [e0 [n0 [Heq3 [Ht0 [He0 [Hn Hcmp0]]]]]]].
    inversion Heq3; subst t0 e0 n0.
    destruct (aepi_pair_components _ _ _ _ _ _ _ _ _ Htag HE0 HP Hp)
      as [_ Htail].
    (* n : TEnumT eE — the succ's own annotation E' compares to the tail E *)
    destruct (nameless.DBEnumBeta.conversion_conse _ _ _ _
      (acmp_enumt _ _ Hcmp0)) as [_ HCtail].
    assert (HnE : typing Gamma n (Raw.TEnumT (erase E0))).
    { eapply ty_conv; [exact Hn| |].
      - rty (ty_enumt _ _ HE0).
      - apply RCore.cv_compatible, Raw.cp_TEnumT. exact HCtail. }
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    (* goal: TSwitch k E (atail_motive..) ps n : TApp eP (e (TESucc t' E' n)) *)
    eapply ty_conv.
    + apply ty_switch.
      * exact HE0.
      * eapply atail_motive_typing; eassumption.
      * rewrite erase_atail_motive.
        pose proof Htail as Ht. anorm_ty. exact Ht.
      * exact HnE.
    + (* formation: TApp eP (e (TESucc t' E' n)) : Sort k *)
      pose proof (acmp_enumt _ _ Hcmp0) as HCcons.
      assert (Hs : typing Gamma (TESucc t' E' n)
          (Raw.TEnumT (Raw.TConsE (erase tag) (erase E0)))).
      { eapply ty_conv; [exact (ty_succ _ _ _ _ Ht0 He0 Hn)| |].
        - rty (ty_enumt _ _ (ty_conse _ _ _ Htag HE0)).
        - apply RCore.cv_compatible, Raw.cp_TEnumT. exact HCcons. }
      rty (aapp_conv _ _ _ _ _ _ _ _
        (ty_enumt _ _ (ty_conse _ _ _ Htag HE0))
        (asort_under _ _ _ _ (ty_enumt _ _ (ty_conse _ _ _ Htag HE0)))
        HP Hs eq_refl).
    + (* conv: TApp (e tailmotive) en ~ TApp eP (TESucc en) — one beta *)
      eapply RCore.cv_trans.
      * apply RCore.cv_step, RCore.st_root.
        rewrite erase_atail_motive. reflexivity.
      * cbn [Raw.subst]. rewrite RB.subst_lift_zero, RB.lift_zero_id.
        apply RCore.cv_refl.
Qed.

(* ---- description component index conversion ---- *)

(* D : IDesc IT' transports to IDesc IT when the indices compare *)
(* erasure-typing with the result normalized *)
Ltac rtyn H := let Hr := fresh "Hr" in
  pose proof (typing_erasure _ _ _ H) as Hr; anorm_ty; exact Hr.

Lemma adesc_conv : forall Gamma IT IT' D,
  typing Gamma IT (Raw.TSort 0) ->
  typing Gamma D (Raw.TIDesc (erase IT')) ->
  RC.type_comparison (Raw.TIDesc (erase IT')) (Raw.TIDesc (erase IT)) ->
  typing Gamma D (Raw.TIDesc (erase IT)).
Proof.
  intros Gamma IT IT' D HI HD HC.
  eapply ty_conv; [exact HD| |].
  - rty (ty_idesc _ _ HI).
  - apply RCore.cv_compatible, Raw.cp_TIDesc, acmp_idesc. exact HC.
Qed.

(* D : A -> IDesc IT' transports to A -> IDesc IT *)
Lemma aarrow_conv : forall Gamma IT IT' A D,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT'))) ->
  RC.type_comparison (Raw.TIDesc (erase IT')) (Raw.TIDesc (erase IT)) ->
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))).
Proof.
  intros Gamma IT IT' A D HI HA HD HC.
  eapply ty_conv; [exact HD| |].
  - pose proof (ty_pi _ _ _ _ _ HA
      (aweaken _ _ _ _ _ (ty_idesc _ _ HI) HA)) as H'.
    rtyn H'.
  - unfold Raw.arrow. apply RCore.cv_compatible, Raw.cp_TPi.
    + apply RCore.cv_refl.
    + apply RW.conversion_lift, RCore.cv_compatible, Raw.cp_TIDesc,
        acmp_idesc. exact HC.
Qed.

(* payload transport across the interpretation root computation *)
Lemma ainterp_compute : forall Gamma IT D X x S,
  typing Gamma x (Raw.TInterp (erase IT) (erase D) (erase X)) ->
  RT.typing Gamma S (Raw.TSort 0) ->
  RCore.root_step (Raw.TInterp (erase IT) (erase D) (erase X)) = Some S ->
  typing Gamma x S.
Proof.
  intros Gamma IT D X x S Hx HF Hr.
  eapply ty_conv; [exact Hx|exact HF|].
  apply RCore.cv_step, RCore.st_root. exact Hr.
Qed.

(* ---- interpretation roots ---- *)

Theorem ainterp_beta : forall Gamma IT D X u T,
  typing Gamma (TInterp IT D X) T -> structural_root (TInterp IT D X) u ->
  typing Gamma u T.
Proof.
  intros Gamma IT D X u T HT HR.
  destruct (interp_generation _ _ _ HT I)
    as [IT' [D' [X' [Heq [HI [HD [HX Hcmp]]]]]]].
  inversion Heq; subst IT' D' X'; clear Heq.
  inversion HR; subst.
  - (* IVar i -> X i *)
    destruct (ivar_generation _ _ _ HD I)
      as [IT0 [i0 [Heq2 [HI0 [Hi HcmpD]]]]].
    inversion Heq2; subst IT0 i0.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply afamily_app_typing; try assumption.
    eapply ty_conv; [exact Hi| |].
    + rty HI.
    + apply acmp_idesc. exact HcmpD.
  - (* I1 -> Unit *)
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_unitT. eapply typing_context; exact HT.
  - (* IBot -> TEnumT TNilE *)
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_enumt, ty_nile. eapply typing_context; exact HT.
  - (* IProd -> Sigma *)
    destruct (iprod_generation _ _ _ HD I)
      as [IT0 [A0 [B0 [Heq2 [HI0 [HA [HB HcmpD]]]]]]].
    inversion Heq2; subst IT0 A0 B0.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply aproduct_formation; apply ty_interp; try eassumption;
      eapply adesc_conv; eassumption.
  - (* IPi -> Pi *)
    destruct (ipi_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg. clear Heq2.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply ty_pi; [exact HA|].
    eapply ainterp_binder_typing; try eassumption.
    eapply aarrow_conv; eassumption.
  - (* ISig -> Sigma *)
    destruct (isig_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg. clear Heq2.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply ty_sigma; [exact HA|].
    eapply ainterp_binder_typing; try eassumption.
    eapply aarrow_conv; eassumption.
  - (* IChoice -> Sigma (TEnumT E) .. *)
    destruct (ichoice_generation _ _ _ HD I)
      as [ITg [Eg [Dg [Heq2 [HIg [HE [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Eg Dg. clear Heq2.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply ty_sigma; [apply ty_enumt; exact HE|].
    eapply ainterp_binder_enum_typing; try eassumption.
    (* D' : arrow (TEnumT eE) (TIDesc eIT') -> (TIDesc eIT) *)
    eapply ty_conv; [exact HDg| |].
    + pose proof (ty_pi _ _ _ _ _ (ty_enumt _ _ HE)
        (aweaken _ _ _ _ _ (ty_idesc _ _ HI) (ty_enumt _ _ HE))) as H'.
      rtyn H'.
    + unfold Raw.arrow. apply RCore.cv_compatible, Raw.cp_TPi.
      * apply RCore.cv_refl.
      * apply RW.conversion_lift, RCore.cv_compatible, Raw.cp_TIDesc,
          acmp_idesc. exact HcmpD.
Qed.

(* Sigma formation in the erased-lift form [ainterpreted_pair] expects *)
Lemma ainterp_sigma0 : forall Gamma A B,
  typing Gamma A (Raw.TSort 0) ->
  typing (erase A :: Gamma) B (Raw.TSort 0) ->
  RT.typing Gamma (Raw.TSigma (erase A) (erase B)) (Raw.TSort 0).
Proof.
  intros Gamma A B HA HB.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply RT.ty_sigma.
  - exact (typing_erasure _ _ _ HA).
  - exact (typing_erasure _ _ _ HB).
Qed.

Lemma ainterp_pi0 : forall Gamma A B,
  typing Gamma A (Raw.TSort 0) ->
  typing (erase A :: Gamma) B (Raw.TSort 0) ->
  RT.typing Gamma (Raw.TPi (erase A) (erase B)) (Raw.TSort 0).
Proof.
  intros Gamma A B HA HB.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
  apply RT.ty_pi.
  - exact (typing_erasure _ _ _ HA).
  - exact (typing_erasure _ _ _ HB).
Qed.

(* conversion from the reduct's computed type to the source's iall type *)
Ltac aiall_conv Hcmp :=
  eapply RC.comparison_left_conversion;
  [exact Hcmp|
   apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity].

Theorem aiall_beta : forall Gamma IT D X x P u T,
  typing Gamma (TIAll IT D X x P) T ->
  structural_root (TIAll IT D X x P) u -> typing Gamma u T.
Proof.
  intros Gamma IT D X x P u T HT HR.
  destruct (iall_generation _ _ _ HT I)
    as [IT' [D' [X' [x' [P' [Heq [HI [HD [HX [Hx [HP Hcmp]]]]]]]]]]].
  inversion Heq; subst IT' D' X' x' P'; clear Heq.
  inversion HR; subst.
  - (* IVar i -> P (i, x) *)
    destruct (ivar_generation _ _ _ HD I)
      as [IT0 [i0 [Heq2 [HI0 [Hi HcmpD]]]]].
    inversion Heq2; subst IT0 i0.
    pose proof (ty_conv _ _ _ _ _ Hi (typing_erasure _ _ _ HI)
      (acmp_idesc _ _ HcmpD)) as Hi'.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply amotive_app_typing; try assumption.
    apply atotal_pair_typing; try assumption.
    eapply ainterp_compute; [exact Hx| |reflexivity].
    rtyn (afamily_app_typing _ _ _ _ HI HX Hi').
  - (* I1 -> UnitT *)
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_unitT. eapply typing_context; exact HT.
  - (* IBot -> UnitT *)
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_unitT. eapply typing_context; exact HT.
  - (* IProd -> product of ialls *)
    destruct (iprod_generation _ _ _ HD I)
      as [IT0 [A0 [B0 [Heq2 [HI0 [HA [HB HcmpD]]]]]]].
    inversion Heq2; subst IT0 A0 B0; clear Heq2.
    pose proof (adesc_conv _ _ _ _ HI HA HcmpD) as HA'.
    pose proof (adesc_conv _ _ _ _ HI HB HcmpD) as HB'.
    pose proof (ainterp_sigma0 _ _ _
      (ty_interp _ _ _ _ HI HA' HX)
      (aweaken _ _ _ _ _ (ty_interp _ _ _ _ HI HB' HX)
        (ty_interp _ _ _ _ HI HA' HX))) as HSigR.
    destruct (ainterpreted_pair _ _ (TIProd IT' A B) _ _ _ _ _ _ _ _ Hx
      (root_interp_prod _ _ _ _ _) HSigR) as [Ha Hb].
    pose proof Ha as Ha'; anorm_ty.
    pose proof Hb as Hb'; anorm_ty.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply aproduct_formation; apply ty_iall; eassumption.
  - (* IPi -> Pi of iall binder *)
    destruct (ipi_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg; clear Heq2.
    pose proof (aarrow_conv _ _ _ _ _ HI HA HDg HcmpD) as HD'.
    pose proof (ainterp_pi0 _ _ _ HA
      (ainterp_binder_typing _ _ _ _ _ HI HA HD' HX)) as HpibR.
    anorm_ty.
    pose proof (ainterp_compute _ _ (TIPi IT' A D0) _ _ _ Hx HpibR
      ltac:(reflexivity)) as Hf'.
    anorm_ty.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 0)).
    apply ty_pi; [exact HA|].
    eapply aiall_binder_typing; eassumption.
  - (* ISig -> iall on the instantiated description *)
    destruct (isig_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg; clear Heq2.
    pose proof (aarrow_conv _ _ _ _ _ HI HA HDg HcmpD) as HD'.
    pose proof (ainterp_sigma0 _ _ _ HA
      (ainterp_binder_typing _ _ _ _ _ HI HA HD' HX)) as HsigR.
    destruct (ainterpreted_pair _ _ (TISig IT' A D0) _ _ _ _ _ _ _ _ Hx
      (root_interp_sig _ _ _ _ _) HsigR) as [Ha Hx0].
    pose proof Ha as Ha'; anorm_ty.
    pose proof Hx0 as Hx0'; anorm_ty.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_iall; try eassumption.
    eapply ainstantiate_typing; eassumption.
  - (* IChoice -> iall on the instantiated description *)
    destruct (ichoice_generation _ _ _ HD I)
      as [ITg [Eg [Dg [Heq2 [HIg [HE [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Eg Dg; clear Heq2.
    pose proof (ty_enumt _ _ HE) as HEt.
    assert (HD' : typing Gamma D0
        (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT)))).
    { eapply ty_conv; [exact HDg| |].
      - pose proof (ty_pi _ _ _ _ _ HEt
          (aweaken _ _ _ _ _ (ty_idesc _ _ HI) HEt)) as H'.
        rtyn H'.
      - unfold Raw.arrow. apply RCore.cv_compatible, Raw.cp_TPi.
        + apply RCore.cv_refl.
        + apply RW.conversion_lift, RCore.cv_compatible, Raw.cp_TIDesc,
            acmp_idesc. exact HcmpD. }
    pose proof (ainterp_sigma0 _ _ _ HEt
      (ainterp_binder_enum_typing _ _ _ _ _ HI HE HD' HX)) as HsigR.
    destruct (ainterpreted_pair _ _ (TIChoice IT' E D0) _ _ _ _ _ _ _ _ Hx
      (root_interp_choice _ _ _ _ _) HsigR) as [He Hx0].
    pose proof He as He'; anorm_ty.
    pose proof Hx0 as Hx0'; anorm_ty.
    eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
    apply ty_iall; try eassumption.
    eapply ainstantiate_enum_typing; eassumption.
Qed.

(* ---- hyps roots ---- *)

Theorem ahyps_beta : forall Gamma IT D X P h x u T,
  typing Gamma (THyps IT D X P h x) T ->
  structural_root (THyps IT D X P h x) u -> typing Gamma u T.
Proof.
  intros Gamma IT D X P h x u T HT HR.
  destruct (hyps_generation _ _ _ HT I)
    as [IT' [D' [X' [P' [h' [x' [Heq [HI [HD [HX [HP [Hh [Hx Hcmp]]]]]]]]]]]]].
  inversion Heq; subst IT' D' X' P' h' x'; clear Heq.
  inversion HR; subst.
  - (* IVar: h i x *)
    destruct (ivar_generation _ _ _ HD I)
      as [IT0 [i0 [Heq2 [HI0 [Hi HcmpD]]]]].
    inversion Heq2; subst IT0 i0.
    pose proof (ty_conv _ _ _ _ _ Hi (typing_erasure _ _ _ HI)
      (acmp_idesc _ _ HcmpD)) as Hi'.
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply arec_app_typing; try assumption.
      * pose proof Hh as Hh'. anorm_ty. exact Hh'.
      * eapply ainterp_compute; [exact Hx| |reflexivity].
        rtyn (afamily_app_typing _ _ _ _ HI HX Hi').
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
  - (* I1 -> TUnit *)
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply ty_unit. eapply typing_context; exact HT.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
  - (* IBot -> TUnit *)
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply ty_unit. eapply typing_context; exact HT.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
  - (* IProd -> pair of hyps calls *)
    destruct (iprod_generation _ _ _ HD I)
      as [IT0 [A0 [B0 [Heq2 [HI0 [HA [HB HcmpD]]]]]]].
    inversion Heq2; subst IT0 A0 B0; clear Heq2.
    pose proof (adesc_conv _ _ _ _ HI HA HcmpD) as HA'.
    pose proof (adesc_conv _ _ _ _ HI HB HcmpD) as HB'.
    pose proof (ainterp_sigma0 _ _ _
      (ty_interp _ _ _ _ HI HA' HX)
      (aweaken _ _ _ _ _ (ty_interp _ _ _ _ HI HB' HX)
        (ty_interp _ _ _ _ HI HA' HX))) as HSigR.
    destruct (ainterpreted_pair _ _ (TIProd IT' A B) _ _ _ _ _ _ _ _ Hx
      (root_interp_prod _ _ _ _ _) HSigR) as [Ha Hb].
    pose proof Ha as Ha'; anorm_ty.
    pose proof Hb as Hb'; anorm_ty.
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + eapply ahyps_prod_pair_typing; eassumption.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_refl.
  - (* IPi -> lambda *)
    destruct (ipi_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg; clear Heq2.
    pose proof (aarrow_conv _ _ _ _ _ HI HA HDg HcmpD) as HD'.
    pose proof (ainterp_pi0 _ _ _ HA
      (ainterp_binder_typing _ _ _ _ _ HI HA HD' HX)) as HpibR.
    anorm_ty.
    pose proof (ainterp_compute _ _ (TIPi IT' A D0) _ _ _ Hx HpibR
      ltac:(reflexivity)) as Hf'.
    anorm_ty.
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply ty_lam with (j:=0) (k:=0).
      * exact HA.
      * pose proof (aiall_binder_typing _ _ _ _ _ _ _ HI HA HD' HX Hf' HP)
          as H0. anorm_ty. exact H0.
      * eapply ahyps_binder_typing; eassumption.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
  - (* ISig -> hyps on instantiated desc *)
    destruct (isig_generation _ _ _ HD I)
      as [ITg [Ag [Dg [Heq2 [HIg [HA [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Ag Dg; clear Heq2.
    pose proof (aarrow_conv _ _ _ _ _ HI HA HDg HcmpD) as HD'.
    pose proof (ainterp_sigma0 _ _ _ HA
      (ainterp_binder_typing _ _ _ _ _ HI HA HD' HX)) as HsigR.
    destruct (ainterpreted_pair _ _ (TISig IT' A D0) _ _ _ _ _ _ _ _ Hx
      (root_interp_sig _ _ _ _ _) HsigR) as [Ha Hx0].
    pose proof Ha as Ha'; anorm_ty.
    pose proof Hx0 as Hx0'; anorm_ty.
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply ty_hyps; try eassumption.
      eapply ainstantiate_typing; eassumption.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
  - (* IChoice -> hyps on instantiated desc *)
    destruct (ichoice_generation _ _ _ HD I)
      as [ITg [Eg [Dg [Heq2 [HIg [HE [HDg HcmpD]]]]]]].
    inversion Heq2; subst ITg Eg Dg; clear Heq2.
    pose proof (ty_enumt _ _ HE) as HEt.
    assert (HD' : typing Gamma D0
        (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT)))).
    { eapply ty_conv; [exact HDg| |].
      - pose proof (ty_pi _ _ _ _ _ HEt
          (aweaken _ _ _ _ _ (ty_idesc _ _ HI) HEt)) as H'.
        rtyn H'.
      - unfold Raw.arrow. apply RCore.cv_compatible, Raw.cp_TPi.
        + apply RCore.cv_refl.
        + apply RW.conversion_lift, RCore.cv_compatible, Raw.cp_TIDesc,
            acmp_idesc. exact HcmpD. }
    pose proof (ainterp_sigma0 _ _ _ HEt
      (ainterp_binder_enum_typing _ _ _ _ _ HI HE HD' HX)) as HsigR.
    destruct (ainterpreted_pair _ _ (TIChoice IT' E D0) _ _ _ _ _ _ _ _ Hx
      (root_interp_choice _ _ _ _ _) HsigR) as [He Hx0].
    pose proof He as He'; anorm_ty.
    pose proof Hx0 as Hx0'; anorm_ty.
    eapply comparison_typing; [| |exact (type_correctness _ _ _ HT)].
    + apply ty_hyps; try eassumption.
      eapply ainstantiate_enum_typing; eassumption.
    + eapply RC.comparison_left_conversion; [exact Hcmp|].
      apply RCore.cv_sym, RCore.cv_step, RCore.st_root; anorm_ty; reflexivity.
Qed.

(* ---- induction / close roots ---- *)

(* xs transported across the MuAt comparison *)
Lemma amu_payload_transport : forall Gamma IT D i IT' D' i' xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
  typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.TInterp (erase IT') (Raw.TApp (erase D') (erase i'))
    (Raw.TMuI (erase IT') (erase D'))) ->
  RC.type_comparison (Raw.MuAt (erase IT') (erase D') (erase i'))
    (Raw.MuAt (erase IT) (erase D) (erase i)) ->
  typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D))).
Proof.
  intros Gamma IT D i IT' D' i' xs HI HD Hi Hxs HC.
  destruct (acmp_muat _ _ _ _ _ _ HC) as [HcIT [HcD Hci]].
  eapply ty_conv; [exact Hxs| |].
  - apply RT.ty_interp.
    + exact (typing_erasure _ _ _ HI).
    + pose proof (typing_erasure _ _ _ (adef_app_typing _ _ _ _ HI HD Hi))
        as Hr. rewrite erase_adef_app in Hr. exact Hr.
    + exact (typing_erasure _ _ _ (ty_mui _ _ _ HI HD)).
  - apply RCore.cv_compatible, Raw.cp_TInterp.
    + exact HcIT.
    + apply RCore.cv_compatible, Raw.cp_TApp; [exact HcD|exact Hci].
    + apply RCore.cv_compatible, Raw.cp_TMuI; [exact HcIT|exact HcD].
Qed.

(* xs transported across the CloseAt comparison *)
Lemma aclose_payload_transport : forall Gamma IT F G i IT' F' G' i' xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma F (Raw.Def (erase IT)) ->
  typing Gamma G (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.payload (erase IT') (erase F') (erase G')
    (erase i')) ->
  RC.type_comparison (Raw.CloseAt (erase IT') (erase F') (erase G')
    (erase i')) (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) ->
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)).
Proof.
  intros Gamma IT F G i IT' F' G' i' xs HI HF HG Hi Hxs HC.
  destruct (acmp_closeat _ _ _ _ _ _ _ _ HC) as [HcIT [HcF [HcG Hci]]].
  eapply ty_conv; [exact Hxs| |].
  - pose proof (typing_erasure _ _ _
      (apayload_formation _ _ _ _ _ HI HF HG Hi)) as Hr.
    rewrite erase_apayload in Hr. exact Hr.
  - unfold Raw.payload, Raw.carrier.
    apply RCore.cv_compatible, Raw.cp_TInterp.
    + exact HcIT.
    + apply RCore.cv_compatible, Raw.cp_TApp; [exact HcF|exact Hci].
    + apply RCore.cv_compatible, Raw.cp_TClose;
        [exact HcIT|exact HcG|exact HcG].
Qed.

Theorem aind_beta : forall Gamma IT D P st i x u T,
  typing Gamma (TInd IT D P st i x) T ->
  structural_root (TInd IT D P st i x) u -> typing Gamma u T.
Proof.
  intros Gamma IT D P st i x u T HT HR.
  destruct (ind_generation _ _ _ HT I)
    as [IT' [D' [P' [st' [i' [x' [Heq [HI [HD [HP [Hst [Hi [Hx Hcmp]]]]]]]]]]]]].
  inversion Heq; subst IT' D' P' st' i' x'; clear Heq.
  inversion HR; subst.
  destruct (in_mui_generation _ _ _ Hx I)
    as [IT0 [D0 [i0 [xs0 [Heq2 [HI2 [HD2 [Hi2 [Hxs Hcmp2]]]]]]]]].
  inversion Heq2; subst IT0 D0 i0 xs0; clear Heq2.
  pose proof (amu_payload_transport _ _ _ _ _ _ _ _ HI HD Hi Hxs Hcmp2)
    as HxsN.
  eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
  apply amu_ind_reduct_typing; eassumption.
Qed.

Theorem aclose_case_beta : forall Gamma k IT F G i Q b x u T,
  typing Gamma (TCloseCase k IT F G i Q b x) T ->
  structural_root (TCloseCase k IT F G i Q b x) u -> typing Gamma u T.
Proof.
  intros Gamma k IT F G i Q b x u T HT HR.
  destruct (close_case_generation _ _ _ HT I)
    as [k' [IT' [F' [G' [i' [Q' [b' [x' [Heq
      [HI [HF [HG [Hi [HQ [Hb [Hx Hcmp]]]]]]]]]]]]]]]].
  inversion Heq; subst k' IT' F' G' i' Q' b' x'; clear Heq.
  inversion HR; subst.
  destruct (in_close_generation _ _ _ Hx I)
    as [IT0 [F0 [G0 [i0 [xs0 [Heq2 [HI2 [HF2 [HG2 [Hi2 [Hxs Hcmp2]]]]]]]]]]].
  inversion Heq2; subst IT0 F0 G0 i0 xs0; clear Heq2.
  pose proof (aclose_payload_transport _ _ _ _ _ _ _ _ _ _ HI HF HG Hi
    Hxs Hcmp2) as HxsN.
  eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
  apply aclose_case_reduct_typing; eassumption.
Qed.

Theorem aclose_ind_beta : forall Gamma IT G P st F i x u T,
  typing Gamma (TCloseInd IT G P st F i x) T ->
  structural_root (TCloseInd IT G P st F i x) u -> typing Gamma u T.
Proof.
  intros Gamma IT G P st F i x u T HT HR.
  destruct (close_ind_generation _ _ _ HT I)
    as [IT' [G' [P' [st' [F' [i' [x' [Heq
      [HI [HG [HP [Hst [HF [Hi [Hx Hcmp]]]]]]]]]]]]]]].
  inversion Heq; subst IT' G' P' st' F' i' x'; clear Heq.
  inversion HR; subst.
  destruct (in_close_generation _ _ _ Hx I)
    as [IT0 [F0 [G0 [i0 [xs0 [Heq2 [HI2 [HF2 [HG2 [Hi2 [Hxs Hcmp2]]]]]]]]]]].
  inversion Heq2; subst IT0 F0 G0 i0 xs0; clear Heq2.
  pose proof (aclose_payload_transport _ _ _ _ _ _ _ _ _ _ HI HF HG Hi
    Hxs Hcmp2) as HxsN.
  eapply comparison_typing; [|exact Hcmp|exact (type_correctness _ _ _ HT)].
  apply aclose_ind_reduct_typing; eassumption.
Qed.

Print Assumptions aind_beta.
Print Assumptions aclose_case_beta.
Print Assumptions aclose_ind_beta.
