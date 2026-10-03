(* Typing lemmas for the close-side macros: diagonal motive, recursive
   method, close-induction method spine, and the close reducts. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AMacroTyping.
Import ListNotations.

(* anorm_ty rewrites in * — pathologically slow once hypotheses with
   subst-instance types accumulate. These variants restrict it to a
   single hypothesis or to the goal. *)
Ltac anorm_in H :=
  repeat first
    [ rewrite erase_lift in H | rewrite erase_subst in H |
      rewrite erase_afamily_app in H | rewrite erase_adef_app in H |
      rewrite erase_aCloseAt in H | rewrite erase_aMuAt in H |
      rewrite erase_apayload in H | rewrite erase_atotal in H |
      rewrite erase_amotive in H | rewrite erase_arecursive_method in H |
      rewrite erase_arec_codomain in H | rewrite erase_arec_pair in H |
      rewrite erase_atail_motive in H | rewrite erase_adiagonal_motive in H |
      rewrite RB.lift_fuse_zero in H by lia |
      rewrite RB.lift_lift_one_zero in H |
      rewrite RB.lift_lift_two_zero in H |
      rewrite RW.lift_lift_three_zero in H |
      rewrite RW.lift_lift_four_zero in H |
      rewrite RB.lift_zero_id in H |
      rewrite RB.subst_lift_zero in H |
      rewrite RB.subst_lift_one_zero in H |
      rewrite RB.subst_lift_two_zero in H |
      rewrite RS.subst_lift_three_zero in H |
      rewrite RS.subst_lift_four_zero in H |
      rewrite DT.subst_lift_prefix in H by lia |
      rewrite RW.lift_arrow in H | rewrite RW.lift_Def in H |
      rewrite RW.lift_Family in H | rewrite RW.lift_motive in H |
      rewrite RW.lift_total in H | rewrite RW.lift_recursive_method in H |
      rewrite RW.lift_close_case_method in H | rewrite RW.lift_close_motive in H |
      rewrite RW.lift_mu_ind_method in H | rewrite RW.lift_close_ind_method in H |
      rewrite RW.lift_diagonal_motive in H |
      rewrite RS.subst_arrow in H | rewrite RS.subst_Def in H |
      rewrite RS.subst_Family in H | rewrite RS.subst_total in H |
      rewrite RS.subst_motive in H | rewrite RS.subst_recursive_method in H |
      rewrite RS.subst_close_case_method in H | rewrite RS.subst_close_motive in H |
      rewrite RS.subst_diagonal_motive in H |
      rewrite RS.subst_mu_ind_method in H | rewrite RS.subst_close_ind_method in H |
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
        aclose_rec_lam in H) |
      progress (cbn [erase lift subst Raw.lift Raw.subst map app length
                     Nat.ltb Nat.leb Nat.eqb Nat.add] in H) |
      rewrite ABinding.lift_fuse_zero in H by lia |
      rewrite ABinding.lift_zero_id in H |
      rewrite ABinding.lift_lift_one_zero in H |
      rewrite ABinding.lift_lift_two_zero in H |
      rewrite ABinding.subst_lift_zero in H |
      rewrite ABinding.subst_lift_one_zero in H |
      rewrite ABinding.subst_lift_two_zero in H |
      rewrite ABinding.subst_lift_offset in H by lia |
      rewrite asubst_lift_prefix in H by lia ].

Ltac anorm_goal :=
  match goal with
  | |- context [erase ?X] => is_evar X
  | _ => repeat first
    [ rewrite erase_lift | rewrite erase_subst |
      rewrite erase_afamily_app | rewrite erase_adef_app |
      rewrite erase_aCloseAt | rewrite erase_aMuAt |
      rewrite erase_apayload | rewrite erase_atotal |
      rewrite erase_amotive | rewrite erase_arecursive_method |
      rewrite erase_arec_codomain | rewrite erase_arec_pair |
      rewrite erase_atail_motive | rewrite erase_adiagonal_motive |
      rewrite RB.lift_fuse_zero by lia |
      rewrite RB.lift_lift_one_zero |
      rewrite RB.lift_lift_two_zero |
      rewrite RW.lift_lift_three_zero |
      rewrite RW.lift_lift_four_zero |
      rewrite RB.lift_zero_id |
      rewrite RB.subst_lift_zero |
      rewrite RB.subst_lift_one_zero |
      rewrite RB.subst_lift_two_zero |
      rewrite RS.subst_lift_three_zero |
      rewrite RS.subst_lift_four_zero |
      rewrite DT.subst_lift_prefix by lia |
      rewrite RW.lift_arrow | rewrite RW.lift_Def |
      rewrite RW.lift_Family | rewrite RW.lift_motive |
      rewrite RW.lift_total | rewrite RW.lift_recursive_method |
      rewrite RW.lift_close_case_method | rewrite RW.lift_close_motive |
      rewrite RW.lift_mu_ind_method | rewrite RW.lift_close_ind_method |
      rewrite RW.lift_diagonal_motive |
      rewrite RS.subst_arrow | rewrite RS.subst_Def |
      rewrite RS.subst_Family | rewrite RS.subst_total |
      rewrite RS.subst_motive | rewrite RS.subst_recursive_method |
      rewrite RS.subst_close_case_method | rewrite RS.subst_close_motive |
      rewrite RS.subst_diagonal_motive |
      rewrite RS.subst_mu_ind_method | rewrite RS.subst_close_ind_method |
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
        aclose_rec_lam) |
      progress (cbn [erase lift subst Raw.lift Raw.subst map app length
                     Nat.ltb Nat.leb Nat.eqb Nat.add]) |
      rewrite ABinding.lift_fuse_zero by lia |
      rewrite ABinding.lift_zero_id |
      rewrite ABinding.lift_lift_one_zero |
      rewrite ABinding.lift_lift_two_zero |
      rewrite ABinding.subst_lift_zero |
      rewrite ABinding.subst_lift_one_zero |
      rewrite ABinding.subst_lift_two_zero |
      rewrite ABinding.subst_lift_offset by lia |
      rewrite asubst_lift_prefix by lia ]
  end.

(* ---- close induction pieces ---- *)

(* diagonal motive: λ p:total IT (carrier). (↑P)(↑G)(fst p)(snd p)
   The spine annotations are literal subst-instances of close_motive's Pi
   parts, so erasure lands on the raw computed types. *)
Lemma adiagonal_motive_typing : forall Gamma IT G P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma (adiagonal_motive IT G P)
    (Raw.motive (erase IT) (Raw.carrier (erase IT) (erase G))).
Proof.
  intros Gamma IT G P HI HG HP; unfold adiagonal_motive.
  pose proof (acarrier_typing _ _ _ HI HG) as HX.
  pose proof (atotal_formation _ _ _ HI HX) as HT.
  assert (HW1 : RT.wf (erase (atotal IT (acarrier IT G)) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|rty HT]. }
  assert (HW2 : RT.wf (map erase
      [aDef (lift 1 0 IT); atotal IT (acarrier IT G)] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|].
    rty (aDef_formation _ _ (aweaken _ _ _ _ _ HI HT)). }
  assert (HW3 : RT.wf (map erase
      [lift 2 0 IT; aDef (lift 1 0 IT); atotal IT (acarrier IT G)]
      ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW2|].
    rty (aweaken_by [aDef (lift 1 0 IT); atotal IT (acarrier IT G)]
      _ _ _ HI HW2). }
  pose proof (aweaken _ _ _ _ _ HI HT) as HI1.
  pose proof (aweaken _ _ _ _ _ HG HT) as HG1.
  pose proof (aweaken _ _ _ _ _ HP HT) as HP1.
  pose proof (avar0 _ _ _ HT) as Hv.
  (* inner CloseAt formation at [i;F;p] *)
  assert (Hac : typing (map erase
      [lift 2 0 IT; aDef (lift 1 0 IT); atotal IT (acarrier IT G)] ++ Gamma)
      (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0)) (Raw.TSort 0)).
  { apply aCloseAt_typing.
    - pose proof (aweaken_by [lift 2 0 IT; aDef (lift 1 0 IT);
          atotal IT (acarrier IT G)] _ _ _ HI HW3) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW3|reflexivity|]. anorm_goal. reflexivity.
    - pose proof (aweaken_by [lift 2 0 IT; aDef (lift 1 0 IT);
          atotal IT (acarrier IT G)] _ _ _ HG HW3) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW3|reflexivity|]. anorm_goal. reflexivity. }
  (* the F-elimination spine at [p] *)
  assert (HA2 : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (subst (lift 1 0 G) 0 (lift 2 0 IT)) (Raw.TSort 0)).
  { eapply asubst0.
    - pose proof (aweaken_by [aDef (lift 1 0 IT); atotal IT (acarrier IT G)]
        _ _ _ HI HW2) as H. first [exact H | anorm_in H; anorm_goal; exact H].
    - pose proof HG1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H']. }
  assert (HB2 : typing (erase (subst (lift 1 0 G) 0 (lift 2 0 IT))
      :: erase (atotal IT (acarrier IT G)) :: Gamma)
      (subst (lift 1 0 G) 1
        (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
          (TSort 0)))
      (Raw.TSort 1)).
  { eapply asubst1.
    - pose proof (aweaken_by [aDef (lift 1 0 IT); atotal IT (acarrier IT G)]
        _ _ _ HI HW2) as H. first [exact H | anorm_in H; anorm_goal; exact H].
    - change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
      apply ty_pi; [exact Hac|].
      apply ty_sort. cbn [map app].
      eapply awf_cons; [exact HW3|rty Hac].
    - pose proof HG1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H']. }
  (* fst / snd of the total pair *)
  assert (Hfst : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (TFst (lift 1 0 IT)
        (afamily_app (lift 1 0 (lift 1 0 IT))
          (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
          (TVar 0)) (TVar 0))
      (erase (lift 1 0 IT))).
  { apply ty_fst with (j:=0) (k:=0); [exact HI1| |].
    - assert (HWx : RT.wf (map erase
          [lift 1 0 IT; atotal IT (acarrier IT G)] ++ Gamma)).
      { cbn [map app]. eapply awf_cons; [exact HW1|].
        rty (aweaken _ _ _ _ _ HI HT). }
      eapply afamily_app_typing.
      + pose proof (aweaken_by [lift 1 0 IT; atotal IT (acarrier IT G)]
          _ _ _ HI HWx) as H. first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken_by [lift 1 0 IT; atotal IT (acarrier IT G)]
          _ _ _ HX HWx) as H. first [exact H | anorm_in H; anorm_goal; exact H].
      + eapply avar_typed; [exact HWx|reflexivity|]. anorm_goal. reflexivity.
    - pose proof Hv as H'. first [exact H' | anorm_in H'; anorm_goal; exact H']. }
  assert (Hsnd : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (TSnd (lift 1 0 IT)
        (afamily_app (lift 1 0 (lift 1 0 IT))
          (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
          (TVar 0)) (TVar 0))
      (Raw.subst (Raw.TFst (Raw.TVar 0))
        0 (erase (afamily_app (lift 1 0 (lift 1 0 IT))
          (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
          (TVar 0))))).
  { apply ty_snd with (j:=0) (k:=0); [exact HI1| |].
    - assert (HWx : RT.wf (map erase
          [lift 1 0 IT; atotal IT (acarrier IT G)] ++ Gamma)).
      { cbn [map app]. eapply awf_cons; [exact HW1|].
        rty (aweaken _ _ _ _ _ HI HT). }
      eapply afamily_app_typing.
      + pose proof (aweaken_by [lift 1 0 IT; atotal IT (acarrier IT G)]
          _ _ _ HI HWx) as H. first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken_by [lift 1 0 IT; atotal IT (acarrier IT G)]
          _ _ _ HX HWx) as H. first [exact H | anorm_in H; anorm_goal; exact H].
      + eapply avar_typed; [exact HWx|reflexivity|]. anorm_goal. reflexivity.
    - pose proof Hv as H'. first [exact H' | anorm_in H'; anorm_goal; exact H']. }
  (* (↑P)(↑G) : the F-application *)
  assert (Hf1 : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (TApp (aDef (lift 1 0 IT))
        (TPi (lift 2 0 IT)
          (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
            (TSort 0)))
        (lift 1 0 P) (lift 1 0 G))
      (Raw.TPi (erase (subst (lift 1 0 G) 0 (lift 2 0 IT)))
        (erase (subst (lift 1 0 G) 1
          (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
            (TSort 0)))))).
  { apply aapp_conv with (j:=1) (k:=1).
    - apply aDef_formation. exact HI1.
    - change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 (Nat.max 0 1))).
      apply ty_pi.
      + pose proof (aweaken_by [aDef (lift 1 0 IT); atotal IT (acarrier IT G)]
          _ _ _ HI HW2) as H. first [exact H | anorm_in H; anorm_goal; exact H].
      + apply ty_pi; [exact Hac|].
        apply ty_sort. cbn [map app].
        eapply awf_cons; [exact HW3|rty Hac].
    - pose proof HP1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - pose proof HG1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - anorm_goal. reflexivity. }
  (* ((↑P)(↑G)) (fst p) *)
  assert (Hf2 : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (TApp (subst (lift 1 0 G) 0 (lift 2 0 IT))
        (subst (lift 1 0 G) 1
          (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
            (TSort 0)))
        (TApp (aDef (lift 1 0 IT))
          (TPi (lift 2 0 IT)
            (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
              (TSort 0)))
          (lift 1 0 P) (lift 1 0 G))
        (TFst (lift 1 0 IT)
          (afamily_app (lift 1 0 (lift 1 0 IT))
            (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
            (TVar 0)) (TVar 0)))
      (Raw.TPi
        (erase (subst
          (TFst (lift 1 0 IT)
            (afamily_app (lift 1 0 (lift 1 0 IT))
              (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
              (TVar 0)) (TVar 0))
          0 (subst (lift 1 0 G) 1
            (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0)))))
        (Raw.TSort 0))).
  { apply aapp_conv with (j:=0) (k:=1).
    - exact HA2.
    - exact HB2.
    - pose proof Hf1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - pose proof Hfst as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - anorm_goal. reflexivity. }
  (* the x-domain subst-instance A3 : Sort 0 *)
  assert (HA3 : typing (erase (atotal IT (acarrier IT G)) :: Gamma)
      (subst (TFst (lift 1 0 IT)
        (afamily_app (lift 1 0 (lift 1 0 IT))
          (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
          (TVar 0)) (TVar 0))
        0 (subst (lift 1 0 G) 1
          (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))))
      (Raw.TSort 0)).
  { eapply asubst0.
    - eapply asubst1.
      + pose proof (aweaken_by [aDef (lift 1 0 IT);
          atotal IT (acarrier IT G)] _ _ _ HI HW2) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + exact Hac.
      + pose proof HG1 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - pose proof Hfst as H'. first [exact H' | anorm_in H'; anorm_goal; exact H']. }
  (* final application to (snd p) *)
  assert (Hm : Raw.motive (erase IT) (Raw.carrier (erase IT) (erase G))
             = Raw.TPi (erase (atotal IT (acarrier IT G))) (Raw.TSort 0)).
  { anorm_goal. reflexivity. }
  rewrite Hm.
  apply ty_lam with (j:=0) (k:=1).
  - exact HT.
  - apply ty_sort. exact HW1.
  - apply aapp_conv with (j:=0) (k:=1).
    + exact HA3.
    + apply ty_sort. eapply awf_cons; [exact HW1|rty HA3].
    + pose proof Hf2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    + pose proof Hsnd as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    + anorm_goal. reflexivity.
Qed.

(* payload binder at ctx [i:↑IT; F:aDef IT] *)
Lemma acim_payload_formation : forall Gamma IT G,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing (map erase [lift 1 0 IT; aDef IT] ++ Gamma)
    (acim_payload IT G) (Raw.TSort 0).
Proof.
  intros Gamma IT G HI HG; unfold acim_payload.
  assert (HW1 : RT.wf (erase (aDef IT) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|
      rty (aDef_formation _ _ HI)]. }
  assert (HW2 : RT.wf (map erase [lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|].
    rty (aweaken _ _ _ _ _ HI (aDef_formation _ _ HI)). }
  eapply apayload_formation.
  - exact (aweaken_by [lift 1 0 IT; aDef IT] _ _ _ HI HW2).
  - eapply avar_typed; [exact HW2|reflexivity|]. anorm_goal. reflexivity.
  - pose proof (aweaken_by [lift 1 0 IT; aDef IT] _ _ _ HG HW2) as H.
    first [exact H | anorm_in H; anorm_goal; exact H].
  - eapply avar_typed; [exact HW2|reflexivity|]. anorm_goal. reflexivity.
Qed.

(* iall binder at ctx [xs:payload; i:↑IT; F:aDef IT] *)
Lemma acim_iall_formation : forall Gamma IT G P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing (map erase [acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
    (acim_iall IT G P) (Raw.TSort 0).
Proof.
  intros Gamma IT G P HI HG HP.
  pose proof (acim_payload_formation _ _ _ HI HG) as Hpl.
  pose proof (adiagonal_motive_typing _ _ _ _ HI HG HP) as HQ.
  assert (HW1 : RT.wf (erase (aDef IT) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|
      rty (aDef_formation _ _ HI)]. }
  assert (HW2 : RT.wf (map erase [lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|].
    rty (aweaken _ _ _ _ _ HI (aDef_formation _ _ HI)). }
  assert (HW3 : RT.wf (map erase
      [acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW2|rty Hpl]. }
  unfold acim_iall. apply ty_iall.
  - exact (aweaken_by [acim_payload IT G; lift 1 0 IT; aDef IT] _ _ _ HI HW3).
  - eapply adef_app_typing.
    + exact (aweaken_by [acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HI HW3).
    + eapply avar_typed; [exact HW3|reflexivity|]. anorm_goal. reflexivity.
    + eapply avar_typed; [exact HW3|reflexivity|]. anorm_goal. reflexivity.
  - eapply acarrier_typing.
    + exact (aweaken_by [acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HI HW3).
    + pose proof (aweaken_by [acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HG HW3) as H. first [exact H | anorm_in H; anorm_goal; exact H].
  - eapply avar_typed; [exact HW3|reflexivity|]. anorm_goal. reflexivity.
  - pose proof (aweaken_by [acim_payload IT G; lift 1 0 IT; aDef IT]
      _ _ _ HQ HW3) as H. first [exact H | anorm_in H; anorm_goal; exact H].
Qed.

(* result at ctx [hs:iall; xs:payload; i:↑IT; F:aDef IT] : (↑⁴P) ↑⁴F i (in xs) *)
Lemma acim_result_formation : forall Gamma IT G P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing (map erase [acim_iall IT G P; acim_payload IT G; lift 1 0 IT;
      aDef IT] ++ Gamma) (acim_result IT G P) (Raw.TSort 0).
Proof.
  intros Gamma IT G P HI HG HP.
  pose proof (acim_payload_formation _ _ _ HI HG) as Hpl.
  pose proof (acim_iall_formation _ _ _ _ HI HG HP) as Hil.
  assert (HW1 : RT.wf (erase (aDef IT) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|
      rty (aDef_formation _ _ HI)]. }
  assert (HW2 : RT.wf (map erase [lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW1|].
    rty (aweaken _ _ _ _ _ HI (aDef_formation _ _ HI)). }
  assert (HW3 : RT.wf (map erase
      [acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW2|rty Hpl]. }
  assert (HW4 : RT.wf (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW3|rty Hil]. }
  assert (HW5 : RT.wf (map erase
      [aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW4|].
    rty (aDef_formation _ _
      (aweaken_by [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HI HW4)). }
  assert (HW6 : RT.wf (map erase
      [lift 5 0 IT; aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)).
  { cbn [map app]. eapply awf_cons; [exact HW5|].
    rty (aweaken_by [aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
      lift 1 0 IT; aDef IT] _ _ _ HI HW5). }
  (* CloseAt ↑⁶IT v1 ↑⁶G v0 at ctx6 *)
  assert (Hac : typing (map erase
      [lift 5 0 IT; aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)
      (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0)) (Raw.TSort 0)).
  { apply aCloseAt_typing.
    - pose proof (aweaken_by [lift 5 0 IT; aDef (lift 4 0 IT);
        acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HI HW6) as H. first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW6|reflexivity|]. anorm_goal. reflexivity.
    - pose proof (aweaken_by [lift 5 0 IT; aDef (lift 4 0 IT);
        acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT]
        _ _ _ HG HW6) as H. first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW6|reflexivity|]. anorm_goal. reflexivity. }
  (* B3 = Pi i. Pi x:CloseAt. Sort0 at ctx5 *)
  assert (HB3i : typing (map erase
      [lift 5 0 IT; aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)
      (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0)) (TSort 0))
      (Raw.TSort 1)).
  { change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
    apply ty_pi; [exact Hac|].
    apply ty_sort. cbn [map app].
    eapply awf_cons; [exact HW6|rty Hac]. }
  assert (HB3 : typing (map erase
      [aDef (lift 4 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)
      (TPi (lift 5 0 IT)
        (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
          (TSort 0)))
      (Raw.TSort 1)).
  { change (Raw.TSort 1) with (Raw.TSort (Nat.max 0 1)).
    apply ty_pi.
    - pose proof (aweaken_by [aDef (lift 4 0 IT); acim_iall IT G P;
        acim_payload IT G; lift 1 0 IT; aDef IT] _ _ _ HI HW5) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - exact HB3i. }
  (* the i-domain after F := v3 *)
  assert (HA2 : typing (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
      (subst (TVar 3) 0 (lift 5 0 IT)) (Raw.TSort 0)).
  { eapply asubst0.
    - pose proof (aweaken_by [aDef (lift 4 0 IT); acim_iall IT G P;
        acim_payload IT G; lift 1 0 IT; aDef IT] _ _ _ HI HW5) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity. }
  (* the x-domain Pi after F := v3 *)
  assert (HB2 : typing (map erase
      [subst (TVar 3) 0 (lift 5 0 IT); acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] ++ Gamma)
      (subst (TVar 3) 1
        (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
          (TSort 0)))
      (Raw.TSort 1)).
  { eapply asubst1.
    - pose proof (aweaken_by [aDef (lift 4 0 IT); acim_iall IT G P;
        acim_payload IT G; lift 1 0 IT; aDef IT] _ _ _ HI HW5) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - exact HB3i.
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity. }
  (* (↑⁴P) v3 : the F-application *)
  assert (Hf1 : typing (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
      (TApp (aDef (lift 4 0 IT))
        (TPi (lift 5 0 IT)
          (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
            (TSort 0)))
        (lift 4 0 P) (TVar 3))
      (Raw.TPi (erase (subst (TVar 3) 0 (lift 5 0 IT)))
        (erase (subst (TVar 3) 1
          (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
            (TSort 0)))))).
  { apply aapp_conv with (j:=1) (k:=1).
    - apply aDef_formation.
      exact (aweaken_by [acim_iall IT G P; acim_payload IT G; lift 1 0 IT;
        aDef IT] _ _ _ HI HW4).
    - exact HB3.
    - pose proof (aweaken_by [acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] _ _ _ HP HW4) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity.
    - anorm_goal. reflexivity. }
  (* the x-domain after F := v3, i := v2 *)
  assert (HA1 : typing (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
      (subst (TVar 2) 0 (subst (TVar 3) 1
        (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))))
      (Raw.TSort 0)).
  { eapply asubst0.
    - eapply asubst1.
      + pose proof (aweaken_by [aDef (lift 4 0 IT); acim_iall IT G P;
          acim_payload IT G; lift 1 0 IT; aDef IT] _ _ _ HI HW5) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + exact Hac.
      + eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity.
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity. }
  (* ((↑⁴P) v3) v2 : the i-application *)
  assert (Hf2 : typing (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
      (TApp (subst (TVar 3) 0 (lift 5 0 IT))
        (subst (TVar 3) 1
          (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
            (TSort 0)))
        (TApp (aDef (lift 4 0 IT))
          (TPi (lift 5 0 IT)
            (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
              (TSort 0)))
          (lift 4 0 P) (TVar 3))
        (TVar 2))
      (Raw.TPi
        (erase (subst (TVar 2) 0 (subst (TVar 3) 1
          (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0)))))
        (Raw.TSort 0))).
  { apply aapp_conv with (j:=0) (k:=1).
    - exact HA2.
    - exact HB2.
    - exact Hf1.
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity.
    - anorm_goal. reflexivity. }
  (* in v1 : A1 *)
  assert (Hin : typing (map erase
      [acim_iall IT G P; acim_payload IT G; lift 1 0 IT; aDef IT] ++ Gamma)
      (TInClose (lift 4 0 IT) (TVar 3) (lift 4 0 G) (TVar 2) (TVar 1))
      (erase (subst (TVar 2) 0 (subst (TVar 3) 1
        (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0)))))).
  { assert (HE : erase (subst (TVar 2) 0 (subst (TVar 3) 1
        (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))))
      = Raw.CloseAt (erase (lift 4 0 IT)) (erase (TVar 3))
          (erase (lift 4 0 G)) (erase (TVar 2))).
    { anorm_goal. reflexivity. }
    rewrite HE. apply ty_in_close.
    - exact (aweaken_by [acim_iall IT G P; acim_payload IT G; lift 1 0 IT;
        aDef IT] _ _ _ HI HW4).
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity.
    - pose proof (aweaken_by [acim_iall IT G P; acim_payload IT G;
        lift 1 0 IT; aDef IT] _ _ _ HG HW4) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity.
    - eapply avar_typed; [exact HW4|reflexivity|]. anorm_goal. reflexivity. }
  (* final application to (in xs) *)
  unfold acim_result.
  apply aapp_conv with (j:=0) (k:=1).
  - exact HA1.
  - apply ty_sort. eapply awf_cons; [exact HW4|rty HA1].
  - exact Hf2.
  - exact Hin.
  - anorm_goal. reflexivity.
Qed.

(* codomain of acim_method at ctx [F : aDef IT] *)
Lemma acim_rest_formation : forall Gamma IT G P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing (erase (aDef IT) :: Gamma) (acim_rest IT G P) (Raw.TSort 0).
Proof.
  intros Gamma IT G P HI HG HP; unfold acim_rest.
  change (Raw.TSort 0) with (Raw.TSort (Nat.max 0 (Nat.max 0 (Nat.max 0 0)))).
  apply ty_pi.
  - exact (aweaken _ _ _ _ _ HI (aDef_formation _ _ HI)).
  - apply ty_pi.
    + eapply acim_payload_formation; eassumption.
    + apply ty_pi.
      * eapply acim_iall_formation; eassumption.
      * eapply acim_result_formation; eassumption.
Qed.

Lemma acim_method_formation : forall Gamma IT G P,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma (acim_method IT G P) (Raw.TSort 1).
Proof.
  intros Gamma IT G P HI HG HP; unfold acim_method.
  change (Raw.TSort 1) with (Raw.TSort (Nat.max 1 0)).
  apply ty_pi; [apply aDef_formation; exact HI|
    eapply acim_rest_formation; eassumption].
Qed.

(* λ i:IT. λ x:(carrier i). CloseInd (↑²IT)(↑²G)(↑²P)(↑²st)(↑²G) i x *)
Lemma aclose_rec_lam_typing : forall Gamma IT G P st,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) ->
  typing Gamma (aclose_rec_lam IT G P st)
    (Raw.recursive_method (erase IT) (Raw.carrier (erase IT) (erase G))
      (Raw.diagonal_motive (erase G) (erase P))).
Proof.
  intros Gamma IT G P st HI HG HP HS;
  unfold aclose_rec_lam, aclose_rec_body.
  replace (Raw.recursive_method (erase IT) (Raw.carrier (erase IT) (erase G))
      (Raw.diagonal_motive (erase G) (erase P)))
    with (erase (arecursive_method IT (acarrier IT G)
        (adiagonal_motive IT G P)))
    by (rewrite erase_arecursive_method, erase_adiagonal_motive;
        unfold acarrier, Raw.carrier; cbn [erase]; reflexivity).
  unfold arecursive_method; cbn [erase].
  pose proof (acarrier_typing _ _ _ HI HG) as HX.
  pose proof (adiagonal_motive_typing _ _ _ _ HI HG HP) as HQ.
  pose proof (afam_binder_typing _ _ _ HI HX) as Hdom.
  pose proof (awf_cons _ _ _ (typing_context _ _ _ HI)
    (typing_erasure _ _ _ HI)) as HW1.
  pose proof (awf_cons _ _ _ HW1 (typing_erasure _ _ _ Hdom)) as HW2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HI HW2) as HI2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HG HW2) as HG2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HP HW2) as HP2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HS HW2) as HS2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HX HW2) as HX2.
  pose proof (aweaken_by [afamily_app (lift 1 0 IT)
      (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
      _ _ _ HQ HW2) as HQ2.
  pose proof (avar_nth _ 1 _ HW2 eq_refl) as Hi2.
  pose proof (avar_nth _ 0 _ HW2 eq_refl) as Hx2.
  apply ty_lam with (j:=0) (k:=0).
  - exact HI.
  - apply arec_codomain_formation; [exact HI|exact HX|exact HQ].
  - (* inner lam: codomain ann (↑²adiag)(i,x) : Sort 0; body = TCloseInd *)
    assert (HBann : typing (map erase
        [afamily_app (lift 1 0 IT)
          (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0); IT]
        ++ Gamma)
        (TApp (atotal (lift 2 0 IT)
                (TClose (lift 2 0 IT) (lift 2 0 G) (lift 2 0 G)))
          (TSort 0)
          (lift 2 0 (adiagonal_motive IT G P))
          (arec_pair IT (acarrier IT G)))
        (Raw.TSort 0)).
    { apply aapp_conv with (j:=0) (k:=1).
      - apply atotal_formation; [exact HI2|].
        eapply acarrier_typing; [exact HI2|].
        pose proof HG2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      - apply ty_sort. eapply awf_cons; [exact HW2|].
        apply typing_erasure. apply atotal_formation; [exact HI2|].
        eapply acarrier_typing; [exact HI2|].
        pose proof HG2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      - pose proof HQ2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      - (* pair (v1, v0) : e(atotal ↑²IT ↑²carrier) *)
        apply atotal_pair_typing.
        + exact HI2.
        + eapply acarrier_typing; [exact HI2|].
          pose proof HG2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
        + pose proof Hi2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
        + pose proof Hx2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      - anorm_goal. reflexivity. }
    apply ty_lam with (j:=0) (k:=0); [exact Hdom|exact HBann|].
    (* body TCloseInd ↑²IT ↑²G ↑²P ↑²st ↑²G v1 v0 *)
    eapply ty_conv.
    + apply ty_close_ind.
      * exact HI2.
      * pose proof HG2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      * pose proof HP2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      * pose proof HS2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      * pose proof HG2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      * pose proof Hi2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
      * pose proof Hx2 as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    + exact (typing_erasure _ _ _ HBann).
    + apply RCore.cv_sym. unfold arec_pair. cbn [erase].
      rewrite !erase_lift, erase_adiagonal_motive, RW.lift_diagonal_motive.
      apply RI.diagonal_motive_application_conversion.
Qed.

(* the st F i xs hs spine *)
Lemma acmethod_app_typing : forall Gamma IT G P st F i xs hs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) ->
  typing Gamma F (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) ->
  typing Gamma hs (Raw.TIAll (erase IT) (Raw.TApp (erase F) (erase i))
    (Raw.carrier (erase IT) (erase G)) (erase xs)
    (Raw.diagonal_motive (erase G) (erase P))) ->
  typing Gamma (acmethod_app IT G P st F i xs hs)
    (Raw.TApp (Raw.TApp (Raw.TApp (erase P) (erase F)) (erase i))
      (Raw.TIn (erase xs))).
Proof.
  intros Gamma IT G P st F i xs hs HI HG HP HS HF Hi Hxs Hhs.
  pose proof (acim_payload_formation _ _ _ HI HG) as Hpl.
  pose proof (acim_iall_formation _ _ _ _ HI HG HP) as Hiall.
  pose proof (acim_result_formation _ _ _ _ HI HG HP) as Hres.
  pose proof (acim_rest_formation _ _ _ _ HI HG HP) as Hrest.
  (* annotation formations *)
  pose proof (ty_pi _ _ _ _ _ Hiall Hres) as Hpi2.
  pose proof (ty_pi _ _ _ _ _ Hpl Hpi2) as Hpi1.
  pose proof (aweaken _ _ _ _ _ HI (aDef_formation _ _ HI)) as HAiD.
  (* normalized argument typings at subst-instance types *)
  assert (HiN : typing Gamma i (erase (subst F 0 (lift 1 0 IT)))).
  { anorm_goal. exact Hi. }
  assert (HxsN : typing Gamma xs
      (erase (subst i 0 (subst F 1 (acim_payload IT G))))).
  { anorm_goal. exact Hxs. }
  assert (HhsN : typing Gamma hs
      (erase (subst xs 0 (subst i 1 (subst F 2 (acim_iall IT G P)))))).
  { anorm_goal. exact Hhs. }
  (* F typed at the stuck annotation domain *)
  assert (HFa : typing Gamma F (erase (aDef IT))).
  { eapply ty_conv; [exact HF| |].
    - exact (typing_erasure _ _ _ (aDef_formation _ _ HI)).
    - anorm_goal. apply RCore.cv_refl. }
  (* F-substitution instances *)
  pose proof (asubst0 _ _ _ _ _ HAiD HFa) as HAi.
  pose proof (asubst1 _ _ _ _ _ _ _ HAiD Hpi1 HFa) as HBi.
  pose proof (asubst1 _ _ _ _ _ _ _ HAiD Hpl HFa) as HBpl.
  pose proof (asubst2 _ _ _ _ _ _ _ _ _ HAiD Hpl Hiall HFa) as HBiall.
  pose proof (asubst2 _ _ _ _ _ _ _ _ _ HAiD Hpl Hpi2 HFa) as HBpi2.
  pose proof (asubst3 _ _ _ _ _ _ _ _ _ _ _ HAiD Hpl Hiall Hres HFa) as HBres.
  (* i-substitution instances *)
  pose proof (asubst0 _ _ _ _ _ HBpl HiN) as HAxs.
  pose proof (asubst1 _ _ _ _ _ _ _ HBpl HBpi2 HiN) as HBxs.
  pose proof (asubst1 _ _ _ _ _ _ _ HBpl HBiall HiN) as HBiallI.
  pose proof (asubst2 _ _ _ _ _ _ _ _ _ HBpl HBiall HBres HiN) as HBresI.
  (* xs-substitution instances *)
  pose proof (asubst0 _ _ _ _ _ HBiallI HxsN) as HAh.
  pose proof (asubst1 _ _ _ _ _ _ _ HBiallI HBresI HxsN) as HBh.
  (* st F *)
  assert (Hst1 : typing Gamma (TApp (aDef IT) (acim_rest IT G P) st F)
      (Raw.TPi (erase (subst F 0 (lift 1 0 IT)))
        (erase (subst F 1 (TPi (acim_payload IT G)
          (TPi (acim_iall IT G P) (acim_result IT G P))))))).
  { apply aapp_conv with (j:=1) (k:=0).
    - apply aDef_formation. exact HI.
    - exact Hrest.
    - pose proof HS as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
    - exact HFa.
    - anorm_goal. reflexivity. }
  (* st F i *)
  assert (Hst2 : typing Gamma
      (TApp (subst F 0 (lift 1 0 IT))
        (subst F 1 (TPi (acim_payload IT G)
          (TPi (acim_iall IT G P) (acim_result IT G P))))
        (TApp (aDef IT) (acim_rest IT G P) st F) i)
      (Raw.TPi (erase (subst i 0 (subst F 1 (acim_payload IT G))))
        (erase (subst i 1 (subst F 2
          (TPi (acim_iall IT G P) (acim_result IT G P))))))).
  { apply aapp_conv with (j:=0) (k:=0).
    - exact HAi.
    - exact HBi.
    - exact Hst1.
    - exact HiN.
    - anorm_goal. reflexivity. }
  (* st F i xs *)
  assert (Hst3 : typing Gamma
      (TApp (subst i 0 (subst F 1 (acim_payload IT G)))
        (subst i 1 (subst F 2
          (TPi (acim_iall IT G P) (acim_result IT G P))))
        (TApp (subst F 0 (lift 1 0 IT))
          (subst F 1 (TPi (acim_payload IT G)
            (TPi (acim_iall IT G P) (acim_result IT G P))))
          (TApp (aDef IT) (acim_rest IT G P) st F) i)
        xs)
      (Raw.TPi
        (erase (subst xs 0 (subst i 1 (subst F 2 (acim_iall IT G P)))))
        (erase (subst xs 1 (subst i 2 (subst F 3 (acim_result IT G P))))))).
  { apply aapp_conv with (j:=0) (k:=0).
    - exact HAxs.
    - exact HBxs.
    - exact Hst2.
    - exact HxsN.
    - anorm_goal. reflexivity. }
  (* st F i xs hs *)
  unfold acmethod_app.
  apply aapp_conv with (j:=0) (k:=0).
  - exact HAh.
  - exact HBh.
  - exact Hst3.
  - exact HhsN.
  - anorm_goal. reflexivity.
Qed.

(* the hyps argument THyps IT (F i) (carrier IT G) diag (rec-lam) xs *)
Lemma ahyps_close_typing : forall Gamma IT F G P st i xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma F (Raw.Def (erase IT)) ->
  typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) ->
  typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) ->
  typing Gamma (ahyps_close IT F G P st i xs)
    (Raw.TIAll (erase IT) (Raw.TApp (erase F) (erase i))
      (Raw.carrier (erase IT) (erase G)) (erase xs)
      (Raw.diagonal_motive (erase G) (erase P))).
Proof.
  intros Gamma IT F G P st i xs HI HF HG HP HS Hi Hxs; unfold ahyps_close.
  assert (Hlam : typing Gamma (aclose_rec_lam IT G P st)
    (Raw.recursive_method (erase IT) (erase (acarrier IT G))
      (erase (adiagonal_motive IT G P)))).
  { pose proof (aclose_rec_lam_typing _ _ _ _ _ HI HG HP HS) as H.
    first [exact H | anorm_in H; anorm_goal; exact H]. }
  assert (Hxs' : typing Gamma xs
    (Raw.TInterp (erase IT) (erase (adef_app IT F i))
      (erase (acarrier IT G)))).
  { first [exact Hxs | anorm_goal; exact Hxs]. }
  pose proof (ty_hyps _ _ _ _ _ _ _ HI
    (adef_app_typing _ _ _ _ HI HF Hi)
    (acarrier_typing _ _ _ HI HG)
    (adiagonal_motive_typing _ _ _ _ HI HG HP)
    Hlam Hxs') as H.
  anorm_in H; anorm_goal; exact H.
Qed.

(* the full close-induction reduct *)
Lemma aclose_ind_reduct_typing : forall Gamma IT G P st F i xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
  typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) ->
  typing Gamma F (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) ->
  typing Gamma (aclose_ind_reduct IT G P st F i xs)
    (Raw.TApp (Raw.TApp (Raw.TApp (erase P) (erase F)) (erase i))
      (Raw.TIn (erase xs))).
Proof.
  intros; unfold aclose_ind_reduct; eapply acmethod_app_typing;
    try eassumption.
  eapply ahyps_close_typing; eassumption.
Qed.

(* the close-case reduct b xs : Q (in xs) *)
Lemma aclose_case_reduct_typing : forall Gamma k IT F G i Q b xs,
  typing Gamma IT (Raw.TSort 0) -> typing Gamma F (Raw.Def (erase IT)) ->
  typing Gamma G (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
  typing Gamma Q (Raw.TPi
    (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) (Raw.TSort k)) ->
  typing Gamma b (Raw.close_case_method
    (erase IT) (erase F) (erase G) (erase i) (erase Q)) ->
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) ->
  typing Gamma (TApp (apayload IT F G i) (aclose_case_codomain k IT F G i Q)
      b xs)
    (Raw.TApp (erase Q) (Raw.TIn (erase xs))).
Proof.
  intros Gamma k IT F G i Q b xs HI HF HG Hi HQ Hb Hxs.
  pose proof (apayload_formation _ _ _ _ _ HI HF HG Hi) as Hpl.
  assert (HW1 : RT.wf (erase (apayload IT F G i) :: Gamma)).
  { eapply awf_cons; [eapply typing_context; exact HI|rty Hpl]. }
  unfold aclose_case_codomain.
  (* codomain annotation (↑Q)(in #0) : TSort k at [x:payload] *)
  assert (HB : typing (erase (apayload IT F G i) :: Gamma)
      (TApp (aCloseAt (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G) (lift 1 0 i))
        (TSort k) (lift 1 0 Q)
        (TInClose (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G) (lift 1 0 i)
          (TVar 0)))
      (Raw.TSort k)).
  { apply aapp_conv with (j:=0) (k:=S k).
    - eapply aCloseAt_typing.
      + exact (aweaken _ _ _ _ _ HI Hpl).
      + pose proof (aweaken _ _ _ _ _ HF Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken _ _ _ _ _ HG Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken _ _ _ _ _ Hi Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
    - apply ty_sort. eapply awf_cons; [exact HW1|].
      assert (HCa : typing (erase (apayload IT F G i) :: Gamma)
        (aCloseAt (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G) (lift 1 0 i))
        (Raw.TSort 0)).
      { apply aCloseAt_typing.
        - exact (aweaken _ _ _ _ _ HI Hpl).
        - pose proof (aweaken _ _ _ _ _ HF Hpl) as H.
          first [exact H | anorm_in H; anorm_goal; exact H].
        - pose proof (aweaken _ _ _ _ _ HG Hpl) as H.
          first [exact H | anorm_in H; anorm_goal; exact H].
        - pose proof (aweaken _ _ _ _ _ Hi Hpl) as H.
          first [exact H | anorm_in H; anorm_goal; exact H]. }
      rty HCa.
    - pose proof (aweaken _ _ _ _ _ HQ Hpl) as H.
      first [exact H | anorm_in H; anorm_goal; exact H].
    - (* TInClose ↑IT ↑F ↑G ↑i v0 : e aCloseAt-instance *)
      apply ty_in_close.
      + exact (aweaken _ _ _ _ _ HI Hpl).
      + pose proof (aweaken _ _ _ _ _ HF Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken _ _ _ _ _ HG Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + pose proof (aweaken _ _ _ _ _ Hi Hpl) as H.
        first [exact H | anorm_in H; anorm_goal; exact H].
      + eapply avar_typed; [exact HW1|reflexivity|]. anorm_goal. reflexivity.
    - anorm_goal. reflexivity. }
  apply aapp_conv with (j:=0) (k:=k).
  - exact Hpl.
  - exact HB.
  - pose proof Hb as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
  - pose proof Hxs as H'. first [exact H' | anorm_in H'; anorm_goal; exact H'].
  - anorm_goal. reflexivity.
Qed.
