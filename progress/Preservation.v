Require Export TypeRulesCore.
Require Import Progress ConversionInversion TypingSubstitution PayloadInversion.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Scheme wf_mut_ind_pres := Induction for wf Sort Prop
with synth_mut_ind_pres := Induction for synth Sort Prop
with check_mut_ind_pres := Induction for check Sort Prop
with branches_mut_ind_pres := Induction for check_branches Sort Prop
with sub_mut_ind_pres := Induction for sub Sort Prop.

Combined Scheme typing_mut_ind_pres
  from wf_mut_ind_pres, synth_mut_ind_pres, check_mut_ind_pres,
       branches_mut_ind_pres, sub_mut_ind_pres.

Lemma wf_tail : forall G A, wf (A :: G) -> wf G.
Proof. intros G A H; inversion H; assumption. Qed.

Lemma typing_context_wf :
  (forall G (_ : wf G), True) /\
  (forall G t A (_ : synth G t A), wf G) /\
  (forall G t A (_ : check G t A), wf G) /\
  (forall G Sf i E Q bs (_ : check_branches G Sf i E Q bs), True) /\
  (forall G A B (_ : sub G A B), True).
Proof.
  apply typing_mut_ind_pres; eauto using wf, wf_tail.
Qed.

Corollary synth_context_wf : forall G t A, synth G t A -> wf G.
Proof. exact (proj1 (proj2 typing_context_wf)). Qed.

Corollary check_context_wf : forall G t A, check G t A -> wf G.
Proof. exact (proj1 (proj2 (proj2 typing_context_wf))). Qed.

Lemma check_of_synth_pres : forall G t A, synth G t A -> check G t A.
Proof. intros; eapply ch_conv; [eassumption | apply cv_refl]. Qed.

Lemma conv_of_eval_pres : forall t u, eval t u -> conv t u.
Proof.
  intros t u H; induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply cv_step; exact H | exact IHeval].
Qed.

Lemma spine_mem_conv_pres : forall c d Phi,
  conv c d -> spine_mem c Phi -> spine_mem d Phi.
Proof.
  intros c d Phi Hcd Hm; induction Hm.
  - eapply sm_here; [exact H |].
    eapply cv_trans; [apply cv_sym; exact Hcd | exact H0].
  - eapply sm_there; eauto.
Qed.

Lemma sig_payload_conv_pres : forall Sf i E c c', conv c c' ->
  conv (TInterp (TApp (branches (TApp Sf i)) c') (Carrier E Sf))
       (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)).
Proof.
  intros. apply cv_interp.
  - apply cv_app; [apply cv_refl | apply cv_sym; exact H].
  - apply cv_refl.
Qed.

Lemma check_sort_raise : forall G j k,
  wf G -> j < k -> check G (TSort j) (TSort k).
Proof.
  intros G j k HG Hlt.
  eapply ch_sub.
  - apply check_of_synth_pres, sy_sort; exact HG.
  - apply su_sort. lia.
Qed.

Lemma check_unit_type : forall G k, wf G -> check G TUnitT (TSort k).
Proof.
  intros. apply check_of_synth_pres, sy_unitT; assumption.
Qed.

Lemma check_unit_intro : forall G, wf G -> check G TUnit TUnitT.
Proof.
  intros. apply check_of_synth_pres, sy_unit; assumption.
Qed.

(* The variable equation for interpretation is representative of the direct
   computation cases: all formation data are retained by the source rule. *)
Lemma interp_var_root : forall G IT i X,
  check G IT (TSort 0) ->
  check G i IT ->
  check G X (TPi IT (TSort 0)) ->
  check G (TApp X i) (TSort 0).
Proof.
  intros G IT i X HIT Hi HX.
  eapply ch_app with (A := IT) (B := TSort 0) (k := 1).
  - apply check_of_synth_pres. eapply sy_pi.
    + eapply ch_sub; [exact HIT | apply su_sort; lia].
    + apply check_of_synth_pres, sy_sort.
      apply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT].
  - exact HX.
  - exact Hi.
Qed.

Lemma interp_one_root : forall G, wf G -> check G TUnitT (TSort 0).
Proof. intros G HG; apply check_unit_type; exact HG. Qed.

Lemma interp_prod_root : forall G IT A B X,
  check G IT (TSort 0) ->
  check G A (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check (TInterp A X :: G) (lift 1 0 (TInterp B X)) (TSort 0) ->
  check G (TSigma (TInterp A X) (lift 1 0 (TInterp B X))) (TSort 0).
Proof.
  intros G IT A B X HIT HA HX HB.
  apply check_of_synth_pres. eapply sy_sigma.
  - apply check_of_synth_pres. eapply sy_interp; eassumption.
  - exact HB.
Qed.

Lemma interp_pi_root : forall G Sd T X,
  check G Sd (TSort 0) ->
  check (Sd :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0) ->
  check G
    (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (TSort 0).
Proof.
  intros G Sd T X HSd Hbody.
  apply check_of_synth_pres. eapply sy_pi; eassumption.
Qed.

Lemma interp_sig_root : forall G Sd T X,
  check G Sd (TSort 0) ->
  check (Sd :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0) ->
  check G
    (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (TSort 0).
Proof.
  intros G Sd T X HSd Hbody.
  apply check_of_synth_pres. eapply sy_sigma; eassumption.
Qed.

Lemma interp_choice_root : forall G E T X,
  check G E TEnumU ->
  check (TEnumT E :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0) ->
  check G
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    (TSort 0).
Proof.
  intros G E T X HE Hbody.
  apply check_of_synth_pres. eapply sy_sigma.
  - apply check_of_synth_pres, sy_enumt; exact HE.
  - exact Hbody.
Qed.

Lemma epi_nil_root : forall G k, wf G -> check G TUnitT (TSort k).
Proof. exact check_unit_type. Qed.

Lemma motive_app_root : forall G E P e k,
  check G E TEnumU ->
  check G P (TPi (TEnumT E) (TSort k)) ->
  check G e (TEnumT E) ->
  check G (TApp P e) (TSort k).
Proof.
  intros G E P e k HE HP He.
  eapply ch_app with (A := TEnumT E) (B := TSort k) (k := S k).
  - apply check_of_synth_pres. eapply sy_pi.
    + eapply ch_sub.
      * apply check_of_synth_pres, sy_enumt; exact HE.
      * apply su_sort; lia.
    + apply check_of_synth_pres, sy_sort.
      apply wf_cons with (k := 0).
      * eapply check_context_wf; exact HE.
      * apply check_of_synth_pres, sy_enumt; exact HE.
  - exact HP.
  - exact He.
Qed.

Lemma enum_motive_type_formation_pres : forall G E k,
  check G E TEnumU ->
  check G (TPi (TEnumT E) (TSort k)) (TSort (S k)).
Proof.
  intros G E k HE.
  assert (HET : check G (TEnumT E) (TSort 0)).
  { apply check_of_synth_pres, sy_enumt; exact HE. }
  assert (HW : wf (TEnumT E :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HE | exact HET]. }
  apply check_of_synth_pres. eapply sy_pi.
  - eapply ch_sub; [exact HET | apply su_sort; lia].
  - apply check_of_synth_pres, sy_sort. exact HW.
Qed.

Lemma epi_cons_root : forall G tg E P k,
  check G (TConsE tg E) TEnumU ->
  check G P (TPi (TEnumT (TConsE tg E)) (TSort k)) ->
  check G TEZero (TEnumT (TConsE tg E)) ->
  check (TApp P TEZero :: G)
    (lift 1 0
      (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))))
    (TSort k) ->
  check G
    (TSigma (TApp P TEZero)
      (lift 1 0
        (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))))
    (TSort k).
Proof.
  intros G tg E P k HE HP Hzero Htail.
  apply check_of_synth_pres. eapply sy_sigma.
  - eapply motive_app_root.
    + exact HE.
    + exact HP.
    + exact Hzero.
  - exact Htail.
Qed.

Lemma switch_zero_root : forall G P p0,
  check G p0 (TApp P TEZero) -> check G p0 (TApp P TEZero).
Proof. auto. Qed.

Lemma switch_succ_root : forall G E P ps n k,
  check G E TEnumU ->
  check G
    (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))
    (TPi (TEnumT E) (TSort k)) ->
  check G ps
    (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))) ->
  check G n (TEnumT E) ->
  check G
    (TSwitch E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))) ps n)
    (TApp (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))) n).
Proof.
  intros. apply check_of_synth_pres. eapply sy_switch; eassumption.
Qed.

Lemma iall_one_root : forall G, wf G -> check G TUnitT (TSort 0).
Proof. exact interp_one_root. Qed.

Lemma iall_var_root : forall G j x P IT X,
  check G
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0))
    (TSort 1) ->
  check G P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TPair j x) (TSigma IT (TApp (lift 1 0 X) (TVar 0))) ->
  check G (TApp P (TPair j x)) (TSort 0).
Proof.
  intros. eapply ch_app with
    (A := TSigma IT (TApp (lift 1 0 X) (TVar 0)))
    (B := TSort 0) (k := 1); eassumption.
Qed.

Lemma iall_prod_root : forall G A B X a b P,
  check G (TIAll A X a P) (TSort 0) ->
  check (TIAll A X a P :: G) (lift 1 0 (TIAll B X b P)) (TSort 0) ->
  check G
    (TSigma (TIAll A X a P) (lift 1 0 (TIAll B X b P))) (TSort 0).
Proof.
  intros. apply check_of_synth_pres. eapply sy_sigma; eassumption.
Qed.

Lemma iall_pi_root : forall G Sd T X f P,
  check G Sd (TSort 0) ->
  check (Sd :: G)
    (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
       (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)) (TSort 0) ->
  check G
    (TPi Sd
      (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
        (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P))) (TSort 0).
Proof.
  intros. apply check_of_synth_pres. eapply sy_pi; eassumption.
Qed.

Lemma iall_recursive_root : forall G IT D X x P,
  check G IT (TSort 0) ->
  check G D (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G x (TInterp D X) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TIAll D X x P) (TSort 0).
Proof.
  intros. apply check_of_synth_pres. eapply sy_iall; eassumption.
Qed.

Lemma hyps_one_root : forall G X P,
  wf G -> check G TUnit (TIAll TI1 X TUnit P).
Proof.
  intros G X P HG.
  eapply ch_expand.
  - apply cv_step, st_iall_one.
  - apply check_unit_intro; exact HG.
Qed.

Lemma hyps_var_root : forall G j X x P h,
  check G (TApp (TApp h j) x) (TApp P (TPair j x)) ->
  check G (TApp (TApp h j) x) (TIAll (TIVar j) X x P).
Proof.
  intros. eapply ch_expand; [apply cv_step, st_iall_var | exact H].
Qed.

Lemma hyps_prod_root : forall G A B X P h a b,
  check G (THyps A X P h a) (TIAll A X a P) ->
  check G (THyps B X P h b)
    (subst (THyps A X P h a) 0 (lift 1 0 (TIAll B X b P))) ->
  check G
    (TPair (THyps A X P h a) (THyps B X P h b))
    (TIAll (TIProd A B) X (TPair a b) P).
Proof.
  intros G A B X P h a b HA HB.
  eapply ch_expand; [apply cv_step, st_iall_prod |].
  apply ch_pair with (A := TIAll A X a P)
    (B := lift 1 0 (TIAll B X b P)).
  - exact HA.
  - exact HB.
Qed.

Lemma hyps_pi_root : forall G Sd T X P h f,
  check (Sd :: G)
    (THyps (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X) (lift 1 0 P)
      (lift 1 0 h) (TApp (lift 1 0 f) (TVar 0)))
    (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
      (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)) ->
  check G
    (TLam
      (THyps (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X) (lift 1 0 P)
        (lift 1 0 h) (TApp (lift 1 0 f) (TVar 0))))
    (TIAll (TIPi Sd T) X f P).
Proof.
  intros G Sd T X P h f Hbody.
  eapply ch_expand; [apply cv_step, st_iall_pi |].
  apply ch_lam; exact Hbody.
Qed.

Lemma hyps_sig_root : forall G Sd T X P h s x,
  check G (THyps (TApp T s) X P h x) (TIAll (TApp T s) X x P) ->
  check G (THyps (TApp T s) X P h x)
    (TIAll (TISig Sd T) X (TPair s x) P).
Proof.
  intros. eapply ch_expand; [apply cv_step, st_iall_sig | exact H].
Qed.

Lemma hyps_choice_root : forall G E T X P h e x,
  check G (THyps (TApp T e) X P h x) (TIAll (TApp T e) X x P) ->
  check G (THyps (TApp T e) X P h x)
    (TIAll (TIChoice E T) X (TPair e x) P).
Proof.
  intros. eapply ch_expand; [apply cv_step, st_iall_choice | exact H].
Qed.

Lemma pair_second_root : forall G a b' A B,
  check G a A -> check G b' (subst a 0 B) ->
  check G (TPair a b') (TSigma A B).
Proof. intros; eapply ch_pair; eassumption. Qed.

Lemma in_mui_root : forall G xs R i IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G i IT ->
  check G xs (TInterp (TApp R i) (TMuI R)) ->
  check G (TIn xs) (TApp (TMuI R) i).
Proof. intros; eapply ch_in_mui; eassumption. Qed.

Lemma in_sig_root : forall G c xs Sf i IT E Phi,
  check G IT (TSort 0) -> check G E TEnumU ->
  check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  check G i IT -> check G c (Label E) ->
  eval (labels (TApp Sf i)) Phi -> spine_mem c Phi ->
  check G xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
  check G (TIn (TPair c xs)) (TApp (SigMu E Sf) i).
Proof. intros; eapply ch_in_sig; eassumption. Qed.

Lemma app_congr_root : forall G f' a C A B k,
  check G (TPi A B) (TSort k) ->
  check G f' C -> eval C (TPi A B) -> check G a A ->
  check G (TApp f' a) (subst a 0 B).
Proof.
  intros G f' a C A B k Hform Hf He Ha.
  eapply ch_app; [exact Hform | | exact Ha].
  eapply ch_expand; [apply cv_sym, conv_of_eval_pres; exact He | exact Hf].
Qed.

Lemma fst_congr_root : forall G p' C A B k,
  check G (TSigma A B) (TSort k) ->
  check G p' C -> eval C (TSigma A B) ->
  check G (TFst p') A.
Proof.
  intros G p' C A B k Hform Hp He.
  eapply ch_fst; [exact Hform |].
  eapply ch_expand; [apply cv_sym, conv_of_eval_pres; exact He | exact Hp].
Qed.

Lemma snd_congr_root : forall G p' C A B k,
  check G (TSigma A B) (TSort k) ->
  check G p' C -> eval C (TSigma A B) ->
  check G (TSnd p') (subst (TFst p') 0 B).
Proof.
  intros G p' C A B k Hform Hp He.
  eapply ch_snd; [exact Hform |].
  eapply ch_expand; [apply cv_sym, conv_of_eval_pres; exact He | exact Hp].
Qed.

(* Introduction origins survive arbitrary outer conversion/subsumption. *)
Lemma check_lam_origin : forall G b T,
  check G (TLam b) T ->
  exists A B, check (A :: G) b B /\ sub G (TPi A B) T.
Proof.
  intros G b T H; remember (TLam b) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [A0 [B0 [Hb Hsub]]].
    exists A0, B0. split; [exact Hb | eapply su_trans; eassumption].
  - destruct (IHcheck eq_refl) as [A0 [B0 [Hb Hsub]]].
    exists A0, B0. split; [exact Hb |].
    eapply su_trans; [exact Hsub | apply su_conv, cv_sym; exact H].
  - exists A, B. split; [exact H | apply su_conv, cv_refl].
Qed.

Lemma check_pair_origin : forall G a b T,
  check G (TPair a b) T ->
  exists A B,
    check G a A /\ check G b (subst a 0 B) /\
    sub G (TSigma A B) T.
Proof.
  intros G a b T H; remember (TPair a b) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [A0 [B0 [Ha [Hb Hsub]]]].
    exists A0, B0. repeat split; try assumption.
    eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [A0 [B0 [Ha [Hb Hsub]]]].
    exists A0, B0. repeat split; try assumption.
    eapply su_trans; [exact Hsub | apply su_conv, cv_sym; exact H].
  - exists A, B. repeat split; try assumption. apply su_conv, cv_refl.
Qed.

Lemma check_conse_origin_pres : forall G tg E T,
  check G (TConsE tg E) T ->
  check G tg TUId /\ check G E TEnumU.
Proof.
  intros G tg E T H; remember (TConsE tg E) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate; eauto.
  inversion H; subst; eauto.
Qed.

Lemma check_esucc_origin_pres : forall G n T,
  check G (TESucc n) T ->
  exists tg E, check G tg TUId /\ check G n (TEnumT E) /\
    sub G (TEnumT (TConsE tg E)) T.
Proof.
  intros G n T H; remember (TESucc n) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [tg [E [Htg [Hn HS]]]].
    exists tg, E; repeat split; try assumption. eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [tg [E [Htg [Hn HS]]]].
    exists tg, E; repeat split; try assumption.
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists _, _; repeat split; try eassumption. apply su_conv, cv_refl.
Qed.

Lemma check_ivar_origin_pres : forall G i T,
  check G (TIVar i) T ->
  exists IT, check G i IT /\ sub G (TIDesc IT) T.
Proof.
  intros G i T H; remember (TIVar i) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [IT [Hi HS]].
    exists IT; split; [exact Hi | eapply su_trans; eassumption].
  - destruct (IHcheck eq_refl) as [IT [Hi HS]].
    exists IT; split; [exact Hi |].
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists; split; [eassumption | apply su_conv, cv_refl].
Qed.

Lemma check_iprod_origin_pres : forall G A B T,
  check G (TIProd A B) T ->
  exists IT, check G A (TIDesc IT) /\ check G B (TIDesc IT) /\
    sub G (TIDesc IT) T.
Proof.
  intros G A B T H; remember (TIProd A B) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [IT [HA [HB HS]]].
    exists IT; repeat split; try assumption. eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [IT [HA [HB HS]]].
    exists IT; repeat split; try assumption.
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists; repeat split; try eassumption. apply su_conv, cv_refl.
Qed.

Lemma check_ipi_origin_pres : forall G Sd T C,
  check G (TIPi Sd T) C ->
  exists IT, check G Sd (TSort 0) /\
    check G T (TPi Sd (TIDesc (lift 1 0 IT))) /\
    sub G (TIDesc IT) C.
Proof.
  intros G Sd T C H; remember (TIPi Sd T) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [IT [HSd [HT HS]]].
    exists IT; repeat split; try assumption. eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [IT [HSd [HT HS]]].
    exists IT; repeat split; try assumption.
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists; repeat split; try eassumption. apply su_conv, cv_refl.
Qed.

Lemma check_isig_origin_pres : forall G Sd T C,
  check G (TISig Sd T) C ->
  exists IT, check G Sd (TSort 0) /\
    check G T (TPi Sd (TIDesc (lift 1 0 IT))) /\
    sub G (TIDesc IT) C.
Proof.
  intros G Sd T C H; remember (TISig Sd T) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [IT [HSd [HT HS]]].
    exists IT; repeat split; try assumption. eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [IT [HSd [HT HS]]].
    exists IT; repeat split; try assumption.
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists; repeat split; try eassumption. apply su_conv, cv_refl.
Qed.

Lemma check_ichoice_origin_pres : forall G E T C,
  check G (TIChoice E T) C ->
  exists IT, check G E TEnumU /\
    check G T (TPi (TEnumT E) (TIDesc (lift 1 0 IT))) /\
    sub G (TIDesc IT) C.
Proof.
  intros G E T C H; remember (TIChoice E T) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [IT [HE [HT HS]]].
    exists IT; repeat split; try assumption. eapply su_trans; eassumption.
  - destruct (IHcheck eq_refl) as [IT [HE [HT HS]]].
    exists IT; repeat split; try assumption.
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
  - eexists; repeat split; try eassumption. apply su_conv, cv_refl.
Qed.

Inductive direct_in (G : ctx) : term -> term -> Prop :=
| di_mui : forall xs R i IT,
    check G IT (TSort 0) ->
    check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
    check G i IT ->
    check G xs (TInterp (TApp R i) (TMuI R)) ->
    direct_in G (TIn xs) (TApp (TMuI R) i)
| di_sig : forall c xs Sf i IT E Phi,
    check G IT (TSort 0) -> check G E TEnumU ->
    check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check G i IT -> check G c (Label E) ->
    eval (labels (TApp Sf i)) Phi -> spine_mem c Phi ->
    check G xs
      (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
    direct_in G (TIn (TPair c xs)) (TApp (SigMu E Sf) i).

Lemma check_in_origin : forall G x T,
  check G (TIn x) T ->
  exists U, direct_in G (TIn x) U /\ sub G U T.
Proof.
  intros G x T H; remember (TIn x) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - inversion H.
  - destruct (IHcheck eq_refl) as [U [HU Hsub]].
    exists U. split; [exact HU | eapply su_trans; eassumption].
  - destruct (IHcheck eq_refl) as [U [HU Hsub]].
    exists U. split; [exact HU |].
    eapply su_trans; [exact Hsub | apply su_conv, cv_sym; exact H].
  - eexists. split; [eapply di_mui; eassumption | apply su_conv, cv_refl].
  - eexists. split; [eapply di_sig; eassumption | apply su_conv, cv_refl].
Qed.

Lemma enum_pos_injective_pres : forall c d n,
  enum_pos c n -> enum_pos d n -> c = d.
Proof.
  intros c d n Hc; revert d.
  induction Hc; intros d Hd; inversion Hd; subst; [reflexivity |].
  f_equal. eauto.
Qed.

Lemma enum_pos_step_normal_pres : forall c n,
  enum_pos c n -> forall c', ~ step c c'.
Proof.
  intros c n H; induction H; intros c' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHenum_pos; eassumption.
Qed.

Lemma distinct_positions_pres : forall cs,
  distinct cs -> Forall (fun c => exists n, enum_pos c n) cs.
Proof.
  intros cs H; induction H; constructor; eauto.
Qed.

Lemma distinct_member_step_absurd : forall cs c,
  distinct cs -> In c cs -> forall c', step c c' -> False.
Proof.
  intros cs c Hd Hin c' Hs.
  pose proof (distinct_positions_pres cs Hd) as Hall.
  apply Forall_forall with (x := c) in Hall; [|exact Hin].
  destruct Hall as [n Hpos]. eapply enum_pos_step_normal_pres; eassumption.
Qed.

Lemma case_label_step_impossible_pres : forall
    (bs1 bs2 : list (term * term)) c c' b,
  distinct (map fst (bs1 ++ (c,b) :: bs2)) -> step c c' -> False.
Proof.
  intros bs1 bs2 c c' b Hd Hs.
  eapply (distinct_member_step_absurd
    (map fst (bs1 ++ (c,b) :: bs2)) c Hd).
  - apply in_map_iff. exists (c,b). split; [reflexivity |].
    apply in_or_app. right. cbn; auto.
  - exact Hs.
Qed.

Lemma check_branches_nth : forall G Sf i E Q bs,
  check_branches G Sf i E Q bs ->
  forall k c b, nth_error bs k = Some (c,b) ->
  check G c (Label E) /\
  check
    (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf) :: G)
    b (lift 1 0 Q).
Proof.
  intros G Sf i E Q bs H; induction H; intros k c0 b0 Hnth.
  - destruct k; discriminate.
  - destruct k as [|k]; cbn in Hnth.
    + inversion Hnth; subst. auto.
    + eapply IHcheck_branches; exact Hnth.
Qed.

Lemma case_root_from_payload : forall G Sf i E Q bs a xs k c b n,
  check_branches G Sf i E Q bs ->
  nth_error bs k = Some (c,b) ->
  enum_pos c n -> enum_pos a n ->
  check G xs
    (TInterp (TApp (branches (TApp Sf i)) a) (Carrier E Sf)) ->
  (forall G A u t B,
    check G u A -> check (A :: G) t B ->
    check G (subst u 0 t) (subst u 0 B)) ->
  (forall f a, subst a 0 (lift 1 0 f) = f) ->
  check G (subst xs 0 b) Q.
Proof.
  intros G Sf i E Q bs a xs k c b n Hbs Hnth Hc Ha Hxs Hsubst Hcancel.
  destruct (check_branches_nth _ _ _ _ _ _ Hbs _ _ _ Hnth)
    as [_ Hb].
  pose proof (enum_pos_injective_pres _ _ _ Hc Ha) as ->.
  specialize (Hsubst _ _ _ _ _ Hxs Hb).
  rewrite Hcancel in Hsubst. exact Hsubst.
Qed.

Lemma check_case_synth_origin : forall G M Q bs T,
  check G (TCase M Q bs) T ->
  exists U, synth G (TCase M Q bs) U /\ sub G U T.
Proof.
  intros G M Q bs T H; remember (TCase M Q bs) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - exists A. split; [exact H | apply su_conv; exact H0].
  - destruct (IHcheck eq_refl) as [U [HU HS]].
    exists U. split; [exact HU | eapply su_trans; eassumption].
  - destruct (IHcheck eq_refl) as [U [HU HS]].
    exists U. split; [exact HU |].
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
Qed.

Lemma check_ind_synth_origin : forall G R P stp i x T,
  check G (TInd R P stp i x) T ->
  exists U, synth G (TInd R P stp i x) U /\ sub G U T.
Proof.
  intros G R P stp i x T H; remember (TInd R P stp i x) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - exists A. split; [exact H | apply su_conv; exact H0].
  - destruct (IHcheck eq_refl) as [U [HU HS]].
    exists U. split; [exact HU | eapply su_trans; eassumption].
  - destruct (IHcheck eq_refl) as [U [HU HS]].
    exists U. split; [exact HU |].
    eapply su_trans; [exact HS | apply su_conv, cv_sym; exact H].
Qed.

Lemma check_pi_components_pres : forall G A B T,
  check G (TPi A B) T ->
  exists k, check G A (TSort k) /\ check (A :: G) B (TSort k).
Proof.
  intros G A B T H.
  remember (TPi A B) as t eqn:Et.
  induction H; inversion Et; subst; try discriminate.
  - match goal with Hs : synth _ (TPi _ _) _ |- _ =>
      inversion Hs; subst; eexists; split; eassumption
    end.
  - eapply IHcheck. reflexivity.
  - eapply IHcheck. reflexivity.
Qed.

Section PreservationDraft.

Variable check_subst0_api : forall G A u t B,
  check G u A -> check (A :: G) t B ->
  check G (subst u 0 t) (subst u 0 B).

Variable sub_pi_application_api : forall G A0 B0 A B a k,
  check G (TPi A B) (TSort k) ->
  sub G (TPi A0 B0) (TPi A B) -> check G a A ->
  check G a A0 /\ sub G (subst a 0 B0) (subst a 0 B).

Lemma beta_root : forall G b a A B k,
  check G (TPi A B) (TSort k) ->
  check G (TLam b) (TPi A B) -> check G a A ->
  check G (subst a 0 b) (subst a 0 B).
Proof.
  intros G b a A B k Hform Hlam Ha.
  destruct (check_lam_origin _ _ _ Hlam)
    as [A0 [B0 [Hb Hpi]]].
  destruct (sub_pi_application_api _ _ _ _ _ _ _ Hform Hpi Ha)
    as [Ha0 Hcod].
  eapply ch_sub; [eapply check_subst0_api; eassumption | exact Hcod].
Qed.

End PreservationDraft.

Section FullDraft.
Variable check_subst0_full : forall G A u t B,
  check G u A -> check (A :: G) t B ->
  check G (subst u 0 t) (subst u 0 B).
Variable sub_pi_application_full : forall G A0 B0 A B a k,
  check G (TPi A B) (TSort k) ->
  sub G (TPi A0 B0) (TPi A B) -> check G a A ->
  check G a A0 /\ sub G (subst a 0 B0) (subst a 0 B).
Variable conv_subst_full : forall k t t' a a',
  conv t t' -> conv a a' ->
  conv (subst a k t) (subst a' k t').
Variable checked_pair_fst_full : forall G a b A B k,
  check G (TSigma A B) (TSort k) ->
  check G (TPair a b) (TSigma A B) -> check G a A.
Variable checked_pair_snd_full : forall G a b A B k,
  check G (TSigma A B) (TSort k) ->
  check G (TPair a b) (TSigma A B) ->
  check G b (subst (TFst (TPair a b)) 0 B).
Variable sub_idesc_target_conv_full : forall G I0 I D,
  check G D (TIDesc I) ->
  sub G (TIDesc I0) (TIDesc I) -> conv I0 I.
Variable sub_enum_cons_tail_conv_full : forall G tg0 E0 tg E n,
  check G (TESucc n) (TEnumT (TConsE tg E)) ->
  sub G (TEnumT (TConsE tg0 E0)) (TEnumT (TConsE tg E)) -> conv E0 E.
Variable check_weaken0_full : forall G A t B,
  wf (A :: G) -> check G t B ->
  check (A :: G) (lift 1 0 t) (lift 1 0 B).
Variable subst_lift_zero_full : forall f a,
  subst a 0 (lift 1 0 f) = f.
Variable lift_zero_full : forall f k, lift 0 k f = f.
Variable conv_lift_full : forall t u d k,
  conv t u -> conv (lift d k t) (lift d k u).
Variable subst_eta_cancel_full : forall t,
  subst (TVar 0) 0 (lift 1 1 t) = t.
Variable subst_lift_two_full : forall t a b,
  subst b 0 (subst a 1 (lift 2 0 t)) = t.
Variable subst_lift_three_full : forall t a b c,
  subst c 0 (subst b 1 (subst a 2 (lift 3 0 t))) = t.
Variable lift_lift_one_zero_full : forall t,
  lift 1 1 (lift 1 0 t) = lift 1 0 (lift 1 0 t).
Variable lift_lift_two_zero_full : forall t,
  lift 1 2 (lift 2 0 t) = lift 2 0 (lift 1 0 t).
Variable lift_fuse_two_full : forall t k,
  lift 1 (S k) (lift 1 k t) = lift 2 k t.
Variable lift_two_gap1_full : forall t,
  lift 1 1 (lift 2 0 t) = lift 1 0 (lift 2 0 t).
Variable lift_fuse_three_full : forall t,
  lift 1 0 (lift 2 0 t) = lift 3 0 t.
Variable lift_ind_step_type_two_full : forall R P IT,
  lift 1 0 (lift 1 0
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1)))))))) =
  TPi (lift 2 0 IT)
    (TPi (TInterp (TApp (lift 1 0 (lift 2 0 R)) (TVar 0))
                  (TMuI (lift 1 0 (lift 2 0 R))))
      (TPi (TIAll (TApp (lift 2 0 (lift 2 0 R)) (TVar 1))
                   (TMuI (lift 2 0 (lift 2 0 R)))
                   (TVar 0) (lift 2 0 (lift 2 0 P)))
        (TApp (lift 3 0 (lift 2 0 P))
              (TPair (TVar 2) (TIn (TVar 1)))))).
Variable lift_predicate_type_two_full : forall IT X,
  lift 1 0 (lift 1 0
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0))) =
  TPi (TSigma (lift 2 0 IT)
    (TApp (lift 1 0 (lift 2 0 X)) (TVar 0))) (TSort 0).
Variable lift_idesc_family_type_two_full : forall IT,
  lift 1 0 (lift 1 0 (TPi IT (TIDesc (lift 1 0 IT)))) =
  TPi (lift 2 0 IT) (TIDesc (lift 1 0 (lift 2 0 IT))).
Variable mui_in_payload_same_full : forall G R i xs IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G i IT ->
  check G (TIn xs) (TApp (TMuI R) i) ->
  check G xs (TInterp (TApp R i) (TMuI R)).
Variable mus_in_pair_payload_same_full : forall G Sf i a xs IT E,
  check G IT (TSort 0) -> check G E TEnumU ->
  check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
  check G i IT ->
  check G (TIn (TPair a xs)) (TApp (SigMu E Sf) i) ->
  check G xs
    (TInterp (TApp (branches (TApp Sf i)) a) (Carrier E Sf)).
Lemma checked_app_full : forall G f a A B k,
  check G (TPi A B) (TSort k) ->
  check G f (TPi A B) -> check G a A ->
  check G (TApp f a) (subst a 0 B).
Proof. intros; eapply ch_app; eassumption. Qed.

Lemma small_family_type_formation_full : forall G IT,
  check G IT (TSort 0) ->
  check G (TPi IT (TSort 0)) (TSort 1).
Proof.
  intros G IT HIT.
  assert (HW : wf (IT :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT]. }
  apply check_of_synth_pres. eapply sy_pi.
  - eapply ch_sub; [exact HIT | apply su_sort; lia].
  - apply check_of_synth_pres, sy_sort. exact HW.
Qed.

Lemma predicate_type_formation_full : forall G IT X,
  check G IT (TSort 0) ->
  check G X (TPi IT (TSort 0)) ->
  check G
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0))
    (TSort 1).
Proof.
  intros G IT X HIT HX.
  assert (HW : wf (IT :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT]. }
  pose proof (check_weaken0_full G IT IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G IT X (TPi IT (TSort 0)) HW HX) as HXw.
  assert (Hv : check (IT :: G) (TVar 0) (lift 1 0 IT)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  assert (Hfam : check (IT :: G)
    (TPi (lift 1 0 IT) (TSort 0)) (TSort 1)).
  { apply small_family_type_formation_full. exact HITw. }
  assert (HXv : check (IT :: G) (TApp (lift 1 0 X) (TVar 0)) (TSort 0)).
  { pose proof (checked_app_full _ _ _ _ _ 1 Hfam HXw Hv) as H.
    cbn [subst] in H. exact H. }
  assert (Hsig : check G
    (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma; eassumption. }
  assert (HWsig : wf (TSigma IT (TApp (lift 1 0 X) (TVar 0)) :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact Hsig]. }
  apply check_of_synth_pres. eapply sy_pi.
  - eapply ch_sub; [exact Hsig | apply su_sort; lia].
  - apply check_of_synth_pres, sy_sort. exact HWsig.
Qed.

Lemma idesc_family_type_formation_full : forall G IT Sd,
  check G IT (TSort 0) -> check G Sd (TSort 0) ->
  check G (TPi Sd (TIDesc (lift 1 0 IT))) (TSort 1).
Proof.
  intros G IT Sd HIT HSd.
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  apply check_of_synth_pres. eapply sy_pi.
  - eapply ch_sub; [exact HSd | apply su_sort; lia].
  - apply check_of_synth_pres, sy_idesc. exact HITw.
Qed.

Lemma idesc_family_var_app_full : forall G IT Sd T,
  check G IT (TSort 0) -> check G Sd (TSort 0) ->
  check G T (TPi Sd (TIDesc (lift 1 0 IT))) ->
  check (Sd :: G) (TApp (lift 1 0 T) (TVar 0))
    (TIDesc (lift 1 0 IT)).
Proof.
  intros G IT Sd T HIT HSd HT.
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G Sd Sd (TSort 0) HW HSd) as HSdw.
  pose proof (check_weaken0_full G Sd T
    (TPi Sd (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  cbn [lift] in HITw, HSdw, HTw.
  rewrite lift_lift_one_zero_full in HTw.
  assert (Hv : check (Sd :: G) (TVar 0) (lift 1 0 Sd)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (checked_app_full _ _ _ _ _ 1
    (idesc_family_type_formation_full _ _ _ HITw HSdw) HTw Hv) as H.
  cbn [subst] in H. rewrite subst_lift_zero_full in H. exact H.
Qed.

Lemma checked_family_var_app_full : forall G A B f k,
  check G A (TSort k) -> check (A :: G) B (TSort k) ->
  check G f (TPi A B) ->
  check (A :: G) (TApp (lift 1 0 f) (TVar 0)) B.
Proof.
  intros G A B f k HA HB Hf.
  assert (HW : wf (A :: G)).
  { eapply wf_cons with (k := k); [eapply check_context_wf; exact HA | exact HA]. }
  assert (Hform : check G (TPi A B) (TSort k)).
  { apply check_of_synth_pres. eapply sy_pi; eassumption. }
  pose proof (check_weaken0_full G A (TPi A B) (TSort k) HW Hform) as Hformw.
  pose proof (check_weaken0_full G A f (TPi A B) HW Hf) as Hfw.
  assert (Hv : check (A :: G) (TVar 0) (lift 1 0 A)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (checked_app_full _ _ _ _ _ k Hformw Hfw Hv) as H.
  cbn [subst] in H. rewrite subst_eta_cancel_full in H. exact H.
Qed.

Lemma epi_tail_motive_full : forall G tg E P k,
  check G (TConsE tg E) TEnumU ->
  check G P (TPi (TEnumT (TConsE tg E)) (TSort k)) ->
  check G E TEnumU /\
  check G (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))
    (TPi (TEnumT E) (TSort k)).
Proof.
  intros G tg E P k Hcons HP.
  destruct (check_conse_origin_pres _ _ _ _ Hcons) as [Htg HE].
  assert (HET : check G (TEnumT E) (TSort 0)).
  { apply check_of_synth_pres, sy_enumt. exact HE. }
  assert (HWE : wf (TEnumT E :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HE | exact HET]. }
  pose proof (check_weaken0_full G (TEnumT E) tg TUId HWE Htg) as Htgw.
  pose proof (check_weaken0_full G (TEnumT E) E TEnumU HWE HE) as HEw.
  pose proof (check_weaken0_full G (TEnumT E) P
    (TPi (TEnumT (TConsE tg E)) (TSort k)) HWE HP) as HPw.
  assert (Hv : check (TEnumT E :: G) (TVar 0) (TEnumT (lift 1 0 E))).
  { apply check_of_synth_pres. eapply sy_var with (A := TEnumT E);
      [exact HWE | reflexivity]. }
  assert (Hsucc : check (TEnumT E :: G) (TESucc (TVar 0))
    (TEnumT (TConsE (lift 1 0 tg) (lift 1 0 E)))).
  { apply ch_esucc; assumption. }
  assert (Hconsw : check (TEnumT E :: G)
    (TConsE (lift 1 0 tg) (lift 1 0 E)) TEnumU).
  { apply check_of_synth_pres, sy_conse; assumption. }
  pose proof (checked_app_full _ _ _ _ _ (S k)
    (enum_motive_type_formation_pres _ _ _ Hconsw) HPw Hsucc) as Happ.
  cbn [subst] in Happ. simpl in Happ. repeat rewrite lift_zero_full in Happ.
  split; [exact HE | apply ch_lam; exact Happ].
Qed.

Lemma epi_cons_pair_components_full : forall G tg E P u ps k,
  check G (TConsE tg E) TEnumU ->
  check G P (TPi (TEnumT (TConsE tg E)) (TSort k)) ->
  check G (TPair u ps) (TEPi (TConsE tg E) P) ->
  check G u (TApp P TEZero) /\
  check G ps
    (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))).
Proof.
  intros G tg E P u ps k Hcons HP Hpair.
  destruct (check_conse_origin_pres _ _ _ _ Hcons) as [Htg HE].
  assert (Hz : check G TEZero (TEnumT (TConsE tg E))).
  { apply ch_ezero; assumption. }
  assert (HA : check G (TApp P TEZero) (TSort k)).
  { pose proof (checked_app_full _ _ _ _ _ _
      (enum_motive_type_formation_pres _ _ _ Hcons) HP Hz) as H.
    cbn [subst] in H. exact H. }
  destruct (epi_tail_motive_full _ _ _ _ _ Hcons HP) as [_ Hmot].
  assert (Htail : check G
    (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))) (TSort k)).
  { apply check_of_synth_pres. eapply sy_epi; eassumption. }
  assert (HW : wf (TApp P TEZero :: G)).
  { eapply wf_cons with (k := k); [eapply check_context_wf; exact Hcons|exact HA]. }
  assert (HB : check (TApp P TEZero :: G)
    (lift 1 0 (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))))
    (TSort k)).
  { pose proof (check_weaken0_full G (TApp P TEZero)
      (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))
      (TSort k) HW Htail) as H. cbn [lift] in H. exact H. }
  assert (Hform : check G
    (TSigma (TApp P TEZero)
      (lift 1 0 (TEPi E
        (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))))) (TSort k)).
  { apply check_of_synth_pres. eapply sy_sigma; eassumption. }
  assert (Hsigma : check G (TPair u ps)
    (TSigma (TApp P TEZero)
      (lift 1 0 (TEPi E
        (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_epi_cons | exact Hpair]. }
  split.
  - eapply checked_pair_fst_full; [exact Hform|exact Hsigma].
  - pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hps.
    rewrite subst_lift_zero_full in Hps. exact Hps.
Qed.

Lemma esucc_tail_same_full : forall G tg E n,
  check G (TESucc n) (TEnumT (TConsE tg E)) -> check G n (TEnumT E).
Proof.
  intros G tg E n H.
  destruct (check_esucc_origin_pres _ _ _ H)
    as [tg0 [E0 [Htg0 [Hn HS]]]].
  pose proof (sub_enum_cons_tail_conv_full _ _ _ _ _ _ H HS) as HC.
  eapply ch_expand; [apply cv_enumt, cv_sym; exact HC | exact Hn].
Qed.

Lemma switch_succ_compute_full : forall G tg E P u ps n k,
  check G (TConsE tg E) TEnumU ->
  check G P (TPi (TEnumT (TConsE tg E)) (TSort k)) ->
  check G (TPair u ps) (TEPi (TConsE tg E) P) ->
  check G (TESucc n) (TEnumT (TConsE tg E)) ->
  check G
    (TSwitch E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))) ps n)
    (TApp P (TESucc n)).
Proof.
  intros G tg E P u ps n k Hcons HP Hpair Hsucc.
  destruct (epi_tail_motive_full _ _ _ _ _ Hcons HP) as [HE Hmot].
  destruct (epi_cons_pair_components_full _ _ _ _ _ _ _ Hcons HP Hpair) as [_ Hps].
  pose proof (esucc_tail_same_full _ _ _ _ Hsucc) as Hn.
  eapply ch_expand.
  - replace (TApp P (TESucc n)) with
      (subst n 0 (TApp (lift 1 0 P) (TESucc (TVar 0)))).
    2:{ cbn [subst]. simpl. rewrite subst_lift_zero_full, lift_zero_full. reflexivity. }
    apply cv_sym, cv_step, st_beta.
  - eapply switch_succ_root; eassumption.
Qed.

Lemma epi_cons_compute_data_full : forall G tg E P k,
  check G (TConsE tg E) TEnumU ->
  check G P (TPi (TEnumT (TConsE tg E)) (TSort k)) ->
  check G TEZero (TEnumT (TConsE tg E)) /\
  check (TApp P TEZero :: G)
    (lift 1 0 (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))))
    (TSort k).
Proof.
  intros G tg E P k Hcons HP.
  destruct (check_conse_origin_pres _ _ _ _ Hcons) as [Htg HE].
  assert (Hz : check G TEZero (TEnumT (TConsE tg E))).
  { apply ch_ezero; assumption. }
  assert (HET : check G (TEnumT E) (TSort 0)).
  { apply check_of_synth_pres, sy_enumt. exact HE. }
  assert (HWE : wf (TEnumT E :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HE | exact HET]. }
  pose proof (check_weaken0_full G (TEnumT E) tg TUId HWE Htg) as Htgw.
  pose proof (check_weaken0_full G (TEnumT E) E TEnumU HWE HE) as HEw.
  pose proof (check_weaken0_full G (TEnumT E) P
    (TPi (TEnumT (TConsE tg E)) (TSort k)) HWE HP) as HPw.
  assert (Hv : check (TEnumT E :: G) (TVar 0) (TEnumT (lift 1 0 E))).
  { apply check_of_synth_pres. eapply sy_var with (A := TEnumT E);
      [exact HWE | reflexivity]. }
  assert (Hsucc : check (TEnumT E :: G) (TESucc (TVar 0))
    (TEnumT (TConsE (lift 1 0 tg) (lift 1 0 E)))).
  { apply ch_esucc; assumption. }
  assert (Hconsw : check (TEnumT E :: G)
    (TConsE (lift 1 0 tg) (lift 1 0 E)) TEnumU).
  { apply check_of_synth_pres, sy_conse; assumption. }
  pose proof (checked_app_full _ _ _ _ _ (S k)
    (enum_motive_type_formation_pres _ _ _ Hconsw) HPw Hsucc) as Happ.
  cbn [subst] in Happ. simpl in Happ.
  repeat rewrite lift_zero_full in Happ.
  assert (Hmot : check G
    (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))
    (TPi (TEnumT E) (TSort k))).
  { apply ch_lam. exact Happ. }
  assert (Htail : check G
    (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0))))) (TSort k)).
  { apply check_of_synth_pres. eapply sy_epi; eassumption. }
  pose proof (checked_app_full _ _ _ _ _ (S k)
    (enum_motive_type_formation_pres _ _ _ Hcons) HP Hz) as HPz.
  cbn [subst] in HPz.
  assert (HWz : wf (TApp P TEZero :: G)).
  { eapply wf_cons with (k := k); [eapply check_context_wf; exact HP | exact HPz]. }
  split; [exact Hz |].
  exact (check_weaken0_full G (TApp P TEZero)
    (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))
    (TSort k) HWz Htail).
Qed.

Lemma ivar_same_index_full : forall G i IT,
  check G (TIVar i) (TIDesc IT) -> check G i IT.
Proof.
  intros G i IT H.
  destruct (check_ivar_origin_pres _ _ _ H) as [IT0 [Hi HS]].
  pose proof (sub_idesc_target_conv_full _ _ _ _ H HS) as HC.
  eapply ch_expand; [apply cv_sym; exact HC | exact Hi].
Qed.

Lemma iall_var_compute_full : forall G IT j X xs P,
  check G IT (TSort 0) ->
  check G (TIVar j) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G xs (TInterp (TIVar j) X) ->
  check G P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TApp P (TPair j xs)) (TSort 0).
Proof.
  intros G IT j X xs P HIT Hj HX Hxs HP.
  pose proof (ivar_same_index_full _ _ _ Hj) as Hji.
  assert (Hxs' : check G xs (TApp X j)).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_var | exact Hxs]. }
  assert (Hpair : check G (TPair j xs)
    (TSigma IT (TApp (lift 1 0 X) (TVar 0)))).
  { apply ch_pair; [exact Hji |].
    cbn [subst]. rewrite subst_lift_zero_full, lift_zero_full. exact Hxs'. }
  pose proof (checked_app_full _ _ _ _ _ 1
    (predicate_type_formation_full _ _ _ HIT HX) HP Hpair) as Happ.
  cbn [subst] in Happ. simpl in Happ.
  repeat rewrite lift_zero_full in Happ. exact Happ.
Qed.

Lemma hypothesis_type_data_full : forall G IT X P,
  check G IT (TSort 0) ->
  check G X (TPi IT (TSort 0)) ->
  check G P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G
      (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
        (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0)))))
      (TSort 0) /\
  forall j, check G j IT ->
    check G
      (subst j 0
        (TPi (TApp (lift 1 0 X) (TVar 0))
          (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0)))))
      (TSort 0).
Proof.
  intros G IT X P HIT HX HP.
  assert (HW1 : wf (IT :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT]. }
  assert (HIT1 : check G IT (TSort 1)).
  { eapply ch_sub; [exact HIT | apply su_sort; lia]. }
  assert (HS1 : check (IT :: G) (TSort 0) (TSort 1)).
  { apply check_of_synth_pres, sy_sort. exact HW1. }
  pose proof (checked_family_var_app_full G IT (TSort 0) X 1
    HIT1 HS1 HX) as HX0.
  set (X0 := TApp (lift 1 0 X) (TVar 0)) in *.
  assert (HW2 : wf (X0 :: IT :: G)).
  { eapply wf_cons with (k := 0); [exact HW1 | exact HX0]. }
  pose proof (check_weaken0_full G IT IT (TSort 0) HW1 HIT) as HITw.
  pose proof (check_weaken0_full (IT :: G) X0 (lift 1 0 IT)
    (TSort 0) HW2 HITw) as HIT2.
  pose proof (check_weaken0_full G IT X (TPi IT (TSort 0)) HW1 HX) as HXw.
  pose proof (check_weaken0_full (IT :: G) X0 (lift 1 0 X)
    (lift 1 0 (TPi IT (TSort 0))) HW2 HXw) as HX2.
  pose proof (check_weaken0_full G IT P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) HW1 HP) as HPw.
  pose proof (check_weaken0_full (IT :: G) X0 (lift 1 0 P)
    (lift 1 0
      (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)))
    HW2 HPw) as HP2.
  rewrite lift_predicate_type_two_full in HP2.
  repeat rewrite <- lift_lift_one_zero_full in HIT2, HX2, HP2.
  repeat rewrite lift_fuse_two_full in HIT2, HX2, HP2.
  rewrite <- (lift_lift_one_zero_full (TPi IT (TSort 0))) in HX2.
  rewrite (lift_fuse_two_full (TPi IT (TSort 0)) 0) in HX2.
  cbn [lift] in HX2.
  assert (Hi : check (X0 :: IT :: G) (TVar 1) (lift 2 0 IT)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity]. }
  assert (Hx : check (X0 :: IT :: G) (TVar 0)
    (TApp (lift 2 0 X) (TVar 1))).
  { assert (H0 : check (X0 :: IT :: G) (TVar 0) (lift 1 0 X0)).
    { apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity]. }
    unfold X0 in H0. cbn [lift] in H0.
    rewrite <- lift_lift_one_zero_full in H0.
    rewrite lift_fuse_two_full in H0. exact H0. }
  assert (Hxs : check (X0 :: IT :: G) (TVar 0)
    (TInterp (TIVar (TVar 1)) (lift 2 0 X))).
  { eapply ch_expand; [apply cv_step, st_interp_var | exact Hx]. }
  assert (HD : check (X0 :: IT :: G) (TIVar (TVar 1))
    (TIDesc (lift 2 0 IT))).
  { apply ch_ivar. exact Hi. }
  assert (HPair : check (X0 :: IT :: G)
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))) (TSort 0)).
  { exact (iall_var_compute_full _ _ _ _ _ _ HIT2 HD HX2 Hxs HP2). }
  assert (Hinner : check (IT :: G)
    (TPi X0 (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0)))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_pi; [exact HX0 | exact HPair]. }
  split.
  - apply check_of_synth_pres. eapply sy_pi; [exact HIT | exact Hinner].
  - intros j Hj.
    pose proof (check_subst0_full G IT j _ (TSort 0) Hj Hinner) as H.
    cbn [subst] in H. exact H.
Qed.

Lemma hypothesis_type_formation_full : forall G IT X P,
  check G IT (TSort 0) ->
  check G X (TPi IT (TSort 0)) ->
  check G P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G
    (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
      (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0)))))
    (TSort 0).
Proof.
  intros. exact (proj1 (hypothesis_type_data_full _ _ _ _ H H0 H1)).
Qed.

Lemma hyps_var_compute_full : forall G IT j X xs P h,
  check G IT (TSort 0) ->
  check G (TIVar j) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
  check G xs (TInterp (TIVar j) X) ->
  check G (TApp (TApp h j) xs) (TApp P (TPair j xs)).
Proof.
  intros G IT j X xs P h HIT Hj HX HP Hh Hxs.
  pose proof (ivar_same_index_full _ _ _ Hj) as Hji.
  assert (Hxs' : check G xs (TApp X j)).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_var | exact Hxs]. }
  pose proof (checked_app_full _ _ _ _ _ 0
    (hypothesis_type_formation_full _ _ _ _ HIT HX HP) Hh Hji) as H1.
  cbn [subst] in H1. simpl in H1.
  repeat rewrite subst_eta_cancel_full in H1.
  repeat rewrite subst_lift_zero_full in H1.
  repeat rewrite lift_zero_full in H1.
  destruct (hypothesis_type_data_full _ _ _ _ HIT HX HP) as [_ Hafter].
  pose proof (Hafter _ Hji) as Hform2.
  cbn [subst] in Hform2. simpl in Hform2.
  repeat rewrite subst_eta_cancel_full in Hform2.
  repeat rewrite subst_lift_zero_full in Hform2.
  repeat rewrite lift_zero_full in Hform2.
  pose proof (checked_app_full _ _ _ _ _ 0 Hform2 H1 Hxs') as H2.
  cbn [subst] in H2. simpl in H2.
  repeat rewrite subst_eta_cancel_full in H2.
  repeat rewrite subst_lift_zero_full in H2.
  repeat rewrite lift_zero_full in H2.
  rewrite subst_lift_two_full in H2.
  exact H2.
Qed.

Lemma iprod_same_components_full : forall G A B IT,
  check G (TIProd A B) (TIDesc IT) ->
  check G A (TIDesc IT) /\ check G B (TIDesc IT).
Proof.
  intros G A B IT H.
  destruct (check_iprod_origin_pres _ _ _ _ H) as [IT0 [HA [HB HS]]].
  pose proof (sub_idesc_target_conv_full _ _ _ _ H HS) as HC.
  split.
  - eapply ch_expand; [apply cv_idesc, cv_sym; exact HC | exact HA].
  - eapply ch_expand; [apply cv_idesc, cv_sym; exact HC | exact HB].
Qed.

Lemma interp_prod_compute_full : forall G IT A B X,
  check G IT (TSort 0) -> check G (TIProd A B) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G (TInterp A X) (TSort 0) /\
  check (TInterp A X :: G) (lift 1 0 (TInterp B X)) (TSort 0).
Proof.
  intros G IT A B X HIT HD HX.
  destruct (iprod_same_components_full _ _ _ _ HD) as [HA HB].
  assert (HIA : check G (TInterp A X) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_interp; eassumption. }
  split; [exact HIA |].
  assert (HW : wf (TInterp A X :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIA]. }
  apply check_of_synth_pres. eapply sy_interp with (IT := lift 1 0 IT).
  - exact (check_weaken0_full G (TInterp A X) IT (TSort 0) HW HIT).
  - exact (check_weaken0_full G (TInterp A X) B (TIDesc IT) HW HB).
  - exact (check_weaken0_full G (TInterp A X) X (TPi IT (TSort 0)) HW HX).
Qed.

Lemma iprod_payloads_full : forall G IT A B X a b,
  check G IT (TSort 0) ->
  check G X (TPi IT (TSort 0)) ->
  check G (TIProd A B) (TIDesc IT) ->
  check G (TPair a b) (TInterp (TIProd A B) X) ->
  check G A (TIDesc IT) /\ check G B (TIDesc IT) /\
  check G a (TInterp A X) /\ check G b (TInterp B X).
Proof.
  intros G IT A B X a b HIT HX HD Hpair.
  destruct (iprod_same_components_full _ _ _ _ HD) as [HA HB].
  assert (Hsigma : check G (TPair a b)
    (TSigma (TInterp A X) (lift 1 0 (TInterp B X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_prod | exact Hpair]. }
  destruct (interp_prod_compute_full _ _ _ _ _ HIT HD HX) as [HIA HIB].
  assert (Hform : check G
    (TSigma (TInterp A X) (lift 1 0 (TInterp B X))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma; eassumption. }
  pose proof (checked_pair_fst_full _ _ _ _ _ _ Hform Hsigma) as Ha.
  pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hb.
  rewrite subst_lift_zero_full in Hb. repeat split; assumption.
Qed.

Lemma iall_prod_compute_full : forall G IT A B X a b P,
  check G IT (TSort 0) -> check G (TIProd A B) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G (TPair a b) (TInterp (TIProd A B) X) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TIAll A X a P) (TSort 0) /\
  check (TIAll A X a P :: G) (lift 1 0 (TIAll B X b P)) (TSort 0).
Proof.
  intros G IT A B X a b P HIT HD HX Hpair HP.
  destruct (iprod_payloads_full _ _ _ _ _ _ _ HIT HX HD Hpair)
    as [HA [HB [Ha Hb]]].
  assert (HIA : check G (TIAll A X a P) (TSort 0)).
  { apply iall_recursive_root with (IT := IT); assumption. }
  assert (HIB : check G (TIAll B X b P) (TSort 0)).
  { apply iall_recursive_root with (IT := IT); assumption. }
  split; [exact HIA |].
  assert (HW : wf (TIAll A X a P :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIA]. }
  exact (check_weaken0_full G (TIAll A X a P) (TIAll B X b P)
    (TSort 0) HW HIB).
Qed.

Lemma hyps_prod_compute_full : forall G A B X P h a b IT,
  check G IT (TSort 0) -> check G (TIProd A B) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
  check G (TPair a b) (TInterp (TIProd A B) X) ->
  check G (THyps A X P h a) (TIAll A X a P) /\
  check G (THyps B X P h b)
    (subst (THyps A X P h a) 0 (lift 1 0 (TIAll B X b P))).
Proof.
  intros G A B X P h a b IT HIT HD HX HP Hh Hpair.
  destruct (iprod_payloads_full _ _ _ _ _ _ _ HIT HX HD Hpair)
    as [HA [HB [Ha Hb]]].
  assert (Hha : check G (THyps A X P h a) (TIAll A X a P)).
  { apply check_of_synth_pres. eapply sy_hyps with (IT := IT); eassumption. }
  assert (Hhb : check G (THyps B X P h b) (TIAll B X b P)).
  { apply check_of_synth_pres. eapply sy_hyps with (IT := IT); eassumption. }
  split; [exact Hha |]. rewrite subst_lift_zero_full. exact Hhb.
Qed.

Lemma ipi_same_data_full : forall G Sd T IT,
  check G (TIPi Sd T) (TIDesc IT) ->
  check G Sd (TSort 0) /\
  check G T (TPi Sd (TIDesc (lift 1 0 IT))).
Proof.
  intros G Sd T IT H.
  destruct (check_ipi_origin_pres _ _ _ _ H) as [IT0 [HSd [HT HS]]].
  pose proof (sub_idesc_target_conv_full _ _ _ _ H HS) as HC.
  split; [exact HSd |].
  eapply ch_expand.
  - apply cv_pi; [apply cv_refl | apply cv_idesc, cv_sym].
    exact (conv_lift_full _ _ 1 0 HC).
  - exact HT.
Qed.

Lemma interp_pi_compute_full : forall G IT Sd T X,
  check G IT (TSort 0) -> check G (TIPi Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G Sd (TSort 0) /\
  check (Sd :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0).
Proof.
  intros G IT Sd T X HIT HD HX.
  destruct (ipi_same_data_full _ _ _ _ HD) as [HSd HT]. split; [exact HSd |].
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G Sd T
    (TPi Sd (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  pose proof (check_weaken0_full G Sd X (TPi IT (TSort 0)) HW HX) as HXw.
  assert (Hv : check (Sd :: G) (TVar 0) (lift 1 0 Sd)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (idesc_family_var_app_full _ _ _ _ HIT HSd HT) as HTapp.
  apply check_of_synth_pres. eapply sy_interp with (IT := lift 1 0 IT);
    eassumption.
Qed.

Lemma iall_pi_compute_full : forall G Sd T X xs P IT,
  check G IT (TSort 0) -> check G (TIPi Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G xs (TInterp (TIPi Sd T) X) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G Sd (TSort 0) /\
  check (Sd :: G)
    (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
      (TApp (lift 1 0 xs) (TVar 0)) (lift 1 0 P)) (TSort 0).
Proof.
  intros G Sd T X xs P IT HIT HD HX Hxs HP.
  destruct (ipi_same_data_full _ _ _ _ HD) as [HSd HT]. split; [exact HSd |].
  assert (HxsPi : check G xs
    (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_pi | exact Hxs]. }
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G Sd T
    (TPi Sd (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  pose proof (check_weaken0_full G Sd X (TPi IT (TSort 0)) HW HX) as HXw.
  pose proof (check_weaken0_full G Sd xs
    (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    HW HxsPi) as Hxsw.
  pose proof (check_weaken0_full G Sd P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) HW HP) as HPw.
  cbn [lift] in HPw. rewrite lift_lift_one_zero_full in HPw.
  assert (Hv : check (Sd :: G) (TVar 0) (lift 1 0 Sd)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (idesc_family_var_app_full _ _ _ _ HIT HSd HT) as HTapp.
  destruct (interp_pi_compute_full _ _ _ _ _ HIT HD HX) as [_ Hbody].
  pose proof (checked_family_var_app_full _ _ _ _ 0 HSd Hbody HxsPi)
    as Hxsapp.
  apply check_of_synth_pres. eapply sy_iall with (IT := lift 1 0 IT).
  - exact HITw.
  - exact HTapp.
  - exact HXw.
  - exact Hxsapp.
  - exact HPw.
Qed.

Lemma hyps_pi_compute_full : forall G Sd T X P h xs IT,
  check G IT (TSort 0) -> check G (TIPi Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
  check G xs (TInterp (TIPi Sd T) X) ->
  check (Sd :: G)
    (THyps (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X) (lift 1 0 P)
      (lift 1 0 h) (TApp (lift 1 0 xs) (TVar 0)))
    (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
      (TApp (lift 1 0 xs) (TVar 0)) (lift 1 0 P)).
Proof.
  intros G Sd T X P h xs IT HIT HD HX HP Hh Hxs.
  destruct (ipi_same_data_full _ _ _ _ HD) as [HSd HT].
  assert (HxsPi : check G xs
    (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_pi | exact Hxs]. }
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G Sd T
    (TPi Sd (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  pose proof (check_weaken0_full G Sd X (TPi IT (TSort 0)) HW HX) as HXw.
  pose proof (check_weaken0_full G Sd P
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) HW HP) as HPw.
  pose proof (check_weaken0_full G Sd h
    (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
      (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) HW Hh) as Hhw.
  pose proof (check_weaken0_full G Sd xs
    (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))
    HW HxsPi) as Hxsw.
  cbn [lift] in HPw, Hhw.
  repeat rewrite lift_lift_one_zero_full in HPw, Hhw.
  repeat rewrite lift_lift_two_zero_full in Hhw.
  assert (Hv : check (Sd :: G) (TVar 0) (lift 1 0 Sd)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (idesc_family_var_app_full _ _ _ _ HIT HSd HT) as HTapp.
  destruct (interp_pi_compute_full _ _ _ _ _ HIT HD HX) as [_ Hbody].
  pose proof (checked_family_var_app_full _ _ _ _ 0 HSd Hbody HxsPi)
    as Hxsapp.
  apply check_of_synth_pres. eapply sy_hyps with (IT := lift 1 0 IT);
    eassumption.
Qed.

Lemma isig_same_data_full : forall G Sd T IT,
  check G (TISig Sd T) (TIDesc IT) ->
  check G Sd (TSort 0) /\
  check G T (TPi Sd (TIDesc (lift 1 0 IT))).
Proof.
  intros G Sd T IT H.
  destruct (check_isig_origin_pres _ _ _ _ H) as [IT0 [HSd [HT HS]]].
  pose proof (sub_idesc_target_conv_full _ _ _ _ H HS) as HC.
  split; [exact HSd |]. eapply ch_expand.
  - apply cv_pi; [apply cv_refl | apply cv_idesc, cv_sym].
    exact (conv_lift_full _ _ 1 0 HC).
  - exact HT.
Qed.

Lemma interp_sig_compute_full : forall G IT Sd T X,
  check G IT (TSort 0) -> check G (TISig Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G Sd (TSort 0) /\
  check (Sd :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0).
Proof.
  intros G IT Sd T X HIT HD HX.
  destruct (isig_same_data_full _ _ _ _ HD) as [HSd HT]. split; [exact HSd |].
  assert (HW : wf (Sd :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HSd]. }
  pose proof (check_weaken0_full G Sd IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G Sd T
    (TPi Sd (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  pose proof (check_weaken0_full G Sd X (TPi IT (TSort 0)) HW HX) as HXw.
  assert (Hv : check (Sd :: G) (TVar 0) (lift 1 0 Sd)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (idesc_family_var_app_full _ _ _ _ HIT HSd HT) as HTapp.
  apply check_of_synth_pres. eapply sy_interp with (IT := lift 1 0 IT);
    eassumption.
Qed.

Lemma ichoice_same_data_full : forall G E T IT,
  check G (TIChoice E T) (TIDesc IT) ->
  check G E TEnumU /\
  check G T (TPi (TEnumT E) (TIDesc (lift 1 0 IT))).
Proof.
  intros G E T IT H.
  destruct (check_ichoice_origin_pres _ _ _ _ H) as [IT0 [HE [HT HS]]].
  pose proof (sub_idesc_target_conv_full _ _ _ _ H HS) as HC.
  split; [exact HE |]. eapply ch_expand.
  - apply cv_pi; [apply cv_refl | apply cv_idesc, cv_sym].
    exact (conv_lift_full _ _ 1 0 HC).
  - exact HT.
Qed.

Lemma interp_choice_compute_full : forall G IT E T X,
  check G IT (TSort 0) -> check G (TIChoice E T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G E TEnumU /\
  check (TEnumT E :: G)
    (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)) (TSort 0).
Proof.
  intros G IT E T X HIT HD HX.
  destruct (ichoice_same_data_full _ _ _ _ HD) as [HE HT]. split; [exact HE |].
  assert (HET : check G (TEnumT E) (TSort 0)).
  { apply check_of_synth_pres. apply sy_enumt. exact HE. }
  assert (HW : wf (TEnumT E :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HET]. }
  pose proof (check_weaken0_full G (TEnumT E) IT (TSort 0) HW HIT) as HITw.
  pose proof (check_weaken0_full G (TEnumT E) T
    (TPi (TEnumT E) (TIDesc (lift 1 0 IT))) HW HT) as HTw.
  pose proof (check_weaken0_full G (TEnumT E) X (TPi IT (TSort 0)) HW HX) as HXw.
  assert (Hv : check (TEnumT E :: G) (TVar 0) (lift 1 0 (TEnumT E))).
  { apply check_of_synth_pres. eapply sy_var; [exact HW | reflexivity]. }
  pose proof (idesc_family_var_app_full _ _ _ _ HIT HET HT) as HTapp.
  apply check_of_synth_pres. eapply sy_interp with (IT := lift 1 0 IT);
    eassumption.
Qed.

Lemma iall_sig_compute_full : forall G Sd T X s x P IT,
  check G IT (TSort 0) -> check G (TISig Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G (TPair s x) (TInterp (TISig Sd T) X) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TIAll (TApp T s) X x P) (TSort 0).
Proof.
  intros G Sd T X s x P IT HIT HD HX Hpair HP.
  destruct (isig_same_data_full _ _ _ _ HD) as [HSd HT].
  assert (Hsigma : check G (TPair s x)
    (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_sig | exact Hpair]. }
  destruct (interp_sig_compute_full _ _ _ _ _ HIT HD HX) as [_ Hbody].
  assert (Hform : check G
    (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma; eassumption. }
  pose proof (checked_pair_fst_full _ _ _ _ _ _ Hform Hsigma) as Hs.
  pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hx0.
  assert (HTs : check G (TApp T s) (TIDesc IT)).
  { pose proof (checked_app_full _ _ _ _ _ 1
      (idesc_family_type_formation_full _ _ _ HIT HSd) HT Hs) as H.
    cbn [subst] in H. rewrite subst_lift_zero_full in H. exact H. }
  assert (Hx : check G x (TInterp (TApp T s) X)).
  { replace (TInterp (TApp T s) X) with
      (subst s 0
        (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))).
    2:{ cbn [subst]. simpl. rewrite !subst_lift_zero_full, !lift_zero_full. reflexivity. }
    eapply ch_expand.
    - eapply conv_subst_full; [apply cv_refl | apply cv_sym, cv_step, st_fst].
    - exact Hx0. }
  apply iall_recursive_root with (IT := IT); assumption.
Qed.

Lemma iall_choice_compute_full : forall G E T X e x P IT,
  check G IT (TSort 0) -> check G (TIChoice E T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G (TPair e x) (TInterp (TIChoice E T) X) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G (TIAll (TApp T e) X x P) (TSort 0).
Proof.
  intros G E T X e x P IT HIT HD HX Hpair HP.
  destruct (ichoice_same_data_full _ _ _ _ HD) as [HE HT].
  assert (Hsigma : check G (TPair e x)
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_choice | exact Hpair]. }
  destruct (interp_choice_compute_full _ _ _ _ _ HIT HD HX) as [HE' Hbody].
  assert (Hform : check G
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma;
      [apply check_of_synth_pres, sy_enumt; exact HE'|exact Hbody]. }
  pose proof (checked_pair_fst_full _ _ _ _ _ _ Hform Hsigma) as He.
  pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hx0.
  assert (HTe : check G (TApp T e) (TIDesc IT)).
  { assert (HET : check G (TEnumT E) (TSort 0)).
    { apply check_of_synth_pres, sy_enumt; exact HE. }
    pose proof (checked_app_full _ _ _ _ _ 1
      (idesc_family_type_formation_full _ _ _ HIT HET) HT He) as H.
    cbn [subst] in H. rewrite subst_lift_zero_full in H. exact H. }
  assert (Hx : check G x (TInterp (TApp T e) X)).
  { replace (TInterp (TApp T e) X) with
      (subst e 0
        (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))).
    2:{ cbn [subst]. simpl. rewrite !subst_lift_zero_full, !lift_zero_full. reflexivity. }
    eapply ch_expand.
    - eapply conv_subst_full; [apply cv_refl | apply cv_sym, cv_step, st_fst].
    - exact Hx0. }
  apply iall_recursive_root with (IT := IT); assumption.
Qed.

Lemma hyps_sig_compute_full : forall G Sd T X P h s x IT,
  check G IT (TSort 0) -> check G (TISig Sd T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
  check G (TPair s x) (TInterp (TISig Sd T) X) ->
  check G (THyps (TApp T s) X P h x) (TIAll (TApp T s) X x P).
Proof.
  intros G Sd T X P h s x IT HIT HD HX HP Hh Hpair.
  destruct (isig_same_data_full _ _ _ _ HD) as [HSd HT].
  assert (Hsigma : check G (TPair s x)
    (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_sig | exact Hpair]. }
  destruct (interp_sig_compute_full _ _ _ _ _ HIT HD HX) as [_ Hbody].
  assert (Hform : check G
    (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma; eassumption. }
  pose proof (checked_pair_fst_full _ _ _ _ _ _ Hform Hsigma) as Hs.
  pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hx0.
  assert (HTs : check G (TApp T s) (TIDesc IT)).
  { pose proof (checked_app_full _ _ _ _ _ 1
      (idesc_family_type_formation_full _ _ _ HIT HSd) HT Hs) as H.
    cbn [subst] in H. rewrite subst_lift_zero_full in H. exact H. }
  assert (Hx : check G x (TInterp (TApp T s) X)).
  { replace (TInterp (TApp T s) X) with
      (subst s 0 (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))).
    2:{ cbn [subst]. simpl. rewrite !subst_lift_zero_full, !lift_zero_full. reflexivity. }
    eapply ch_expand.
    - eapply conv_subst_full; [apply cv_refl | apply cv_sym, cv_step, st_fst].
    - exact Hx0. }
  apply check_of_synth_pres. eapply sy_hyps with (IT := IT); eassumption.
Qed.

Lemma hyps_choice_compute_full : forall G E T X P h e x IT,
  check G IT (TSort 0) -> check G (TIChoice E T) (TIDesc IT) ->
  check G X (TPi IT (TSort 0)) ->
  check G P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
  check G h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
  check G (TPair e x) (TInterp (TIChoice E T) X) ->
  check G (THyps (TApp T e) X P h x) (TIAll (TApp T e) X x P).
Proof.
  intros G E T X P h e x IT HIT HD HX HP Hh Hpair.
  destruct (ichoice_same_data_full _ _ _ _ HD) as [HE HT].
  assert (Hsigma : check G (TPair e x)
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))).
  { eapply ch_expand; [apply cv_sym, cv_step, st_interp_choice | exact Hpair]. }
  destruct (interp_choice_compute_full _ _ _ _ _ HIT HD HX) as [HE' Hbody].
  assert (Hform : check G
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_sigma;
      [apply check_of_synth_pres, sy_enumt; exact HE'|exact Hbody]. }
  pose proof (checked_pair_fst_full _ _ _ _ _ _ Hform Hsigma) as He.
  pose proof (checked_pair_snd_full _ _ _ _ _ _ Hform Hsigma) as Hx0.
  assert (HTe : check G (TApp T e) (TIDesc IT)).
  { assert (HET : check G (TEnumT E) (TSort 0)).
    { apply check_of_synth_pres, sy_enumt; exact HE. }
    pose proof (checked_app_full _ _ _ _ _ 1
      (idesc_family_type_formation_full _ _ _ HIT HET) HT He) as H.
    cbn [subst] in H. rewrite subst_lift_zero_full in H. exact H. }
  assert (Hx : check G x (TInterp (TApp T e) X)).
  { replace (TInterp (TApp T e) X) with
      (subst e 0 (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X))).
    2:{ cbn [subst]. simpl. rewrite !subst_lift_zero_full, !lift_zero_full. reflexivity. }
    eapply ch_expand.
    - eapply conv_subst_full; [apply cv_refl | apply cv_sym, cv_step, st_fst].
    - exact Hx0. }
  apply check_of_synth_pres. eapply sy_hyps with (IT := IT); eassumption.
Qed.

(* Formation of the induction step type.  The final codomain does not
   depend on the induction hypothesis argument, so it is formed once in the
   two-variable context and weakened across the [iAll] binder. *)
Lemma ind_step_type_formation_full : forall G R P IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) ->
  check G
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1)))))))
    (TSort 0).
Proof.
  intros G R P IT HIT HR HP.
  assert (HW1 : wf (IT :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT]. }
  pose proof (check_weaken0_full G IT IT (TSort 0) HW1 HIT) as HIT1.
  pose proof (check_weaken0_full G IT R
    (TPi IT (TIDesc (lift 1 0 IT))) HW1 HR) as HR1.
  assert (Hmu1 : check (IT :: G) (TMuI (lift 1 0 R))
    (TPi (lift 1 0 IT) (TSort 0))).
  { apply check_of_synth_pres. eapply sy_mui.
    - exact HIT1.
    - cbn [lift] in HR1. rewrite lift_lift_one_zero_full in HR1. exact HR1. }
  assert (HD1 : check (IT :: G)
      (TApp (lift 1 0 R) (TVar 0)) (TIDesc (lift 1 0 IT))).
  { eapply idesc_family_var_app_full; eassumption. }
  assert (HX1 : check (IT :: G)
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R))) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_interp with (IT := lift 1 0 IT);
      eassumption. }
  assert (HW2 : wf
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)).
  { eapply wf_cons with (k := 0); [exact HW1 | exact HX1]. }
  pose proof (check_weaken0_full G IT IT (TSort 0) HW1 HIT) as HIT1'.
  pose proof (check_weaken0_full (IT :: G)
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
    (lift 1 0 IT) (TSort 0) HW2 HIT1') as HIT2.
  pose proof (check_weaken0_full G IT R
    (TPi IT (TIDesc (lift 1 0 IT))) HW1 HR) as HR1'.
  pose proof (check_weaken0_full (IT :: G)
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
    (lift 1 0 R) (lift 1 0 (TPi IT (TIDesc (lift 1 0 IT))))
    HW2 HR1') as HR2.
  pose proof (check_weaken0_full G IT P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) HW1 HP) as HP1.
  pose proof (check_weaken0_full (IT :: G)
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
    (lift 1 0 P)
    (lift 1 0 (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)))
    HW2 HP1) as HP2.
  change (check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (lift 1 0 (lift 1 0 P))
    (lift 1 0 (lift 1 0
      (TPi (TSigma IT (TApp (lift 1 0 (TMuI R)) (TVar 0))) (TSort 0)))))
    in HP2.
  rewrite (lift_predicate_type_two_full IT (TMuI R)) in HP2.
  rewrite <- (lift_lift_one_zero_full P) in HP2.
  rewrite (lift_fuse_two_full P 0) in HP2.
  rewrite (lift_idesc_family_type_two_full IT) in HR2.
  rewrite <- (lift_lift_one_zero_full R) in HR2.
  rewrite (lift_fuse_two_full R 0) in HR2.
  cbn [lift] in HIT2.
  repeat rewrite <- lift_lift_one_zero_full in HIT2.
  repeat rewrite lift_fuse_two_full in HIT2.
  assert (HD2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TApp (lift 2 0 R) (TVar 1)) (TIDesc (lift 2 0 IT))).
  { pose proof (check_weaken0_full (IT :: G)
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
      (TApp (lift 1 0 R) (TVar 0)) (TIDesc (lift 1 0 IT)) HW2 HD1) as H.
    cbn [lift] in H.
    repeat rewrite <- lift_lift_one_zero_full in H.
    repeat rewrite lift_fuse_two_full in H.
    exact H. }
  assert (Hmu2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TMuI (lift 2 0 R)) (TPi (lift 2 0 IT) (TSort 0))).
  { pose proof (check_weaken0_full (IT :: G)
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
      (TMuI (lift 1 0 R)) (TPi (lift 1 0 IT) (TSort 0)) HW2 Hmu1) as H.
    cbn [lift] in H.
    repeat rewrite <- lift_lift_one_zero_full in H.
    repeat rewrite lift_fuse_two_full in H.
    exact H. }
  assert (Hxs2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TVar 0)
    (TInterp (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R)))).
  { assert (H0 : check
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
      (TVar 0)
      (lift 1 0
        (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R))))).
    { apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity]. }
    cbn [lift] in H0.
    repeat rewrite <- lift_lift_one_zero_full in H0.
    repeat rewrite lift_fuse_two_full in H0.
    exact H0. }
  assert (HAll : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
      (TVar 0) (lift 2 0 P)) (TSort 0)).
  { apply check_of_synth_pres. eapply sy_iall with (IT := lift 2 0 IT).
    - exact HIT2.
    - exact HD2.
    - exact Hmu2.
    - exact Hxs2.
    - exact HP2. }
  assert (HW3 : wf
    (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
      (TVar 0) (lift 2 0 P) ::
     TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)).
  { eapply wf_cons with (k := 0); [exact HW2 | exact HAll]. }
  assert (Hi2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TVar 1) (lift 2 0 IT)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity]. }
  assert (Hin2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TIn (TVar 0)) (TApp (TMuI (lift 2 0 R)) (TVar 1))).
  { eapply ch_in_mui with (IT := lift 2 0 IT).
    - exact HIT2.
    - exact HR2.
    - exact Hi2.
    - exact Hxs2. }
  assert (HPi2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TPi (TSigma (lift 2 0 IT)
       (TApp (lift 1 0 (TMuI (lift 2 0 R))) (TVar 0))) (TSort 0)) (TSort 1)).
  { apply predicate_type_formation_full; eassumption. }
  assert (HPair2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TPair (TVar 1) (TIn (TVar 0)))
    (TSigma (lift 2 0 IT)
      (TApp (lift 1 0 (TMuI (lift 2 0 R))) (TVar 0)))).
  { apply ch_pair; [exact Hi2 |].
    replace (subst (TVar 1) 0
      (TApp (lift 1 0 (TMuI (lift 2 0 R))) (TVar 0))) with
      (TApp (TMuI (lift 2 0 R)) (TVar 1)).
    2:{ cbn [subst]. rewrite subst_lift_zero_full. reflexivity. }
    exact Hin2. }
  assert (HBody2 : check
    (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TApp (lift 2 0 P) (TPair (TVar 1) (TIn (TVar 0)))) (TSort 0)).
  { change (check
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
      (lift 2 0 P)
      (TPi (TSigma (lift 2 0 IT)
        (TApp (lift 1 0 (TMuI (lift 2 0 R))) (TVar 0))) (TSort 0))) in HP2.
    change (check
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
      (TApp (lift 2 0 P) (TPair (TVar 1) (TIn (TVar 0))))
      (subst (TPair (TVar 1) (TIn (TVar 0))) 0 (TSort 0))).
    eapply ch_app; [exact HPi2 | exact HP2 | exact HPair2]. }
  assert (HBody : check
    (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
      (TVar 0) (lift 2 0 P) ::
     TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
    (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1)))) (TSort 0)).
  { pose proof (check_weaken0_full
      (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)) :: IT :: G)
      (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
        (TVar 0) (lift 2 0 P))
      (TApp (lift 2 0 P) (TPair (TVar 1) (TIn (TVar 0)))) (TSort 0)
      HW3 HBody2) as H.
    cbn [lift] in H. cbn in H.
    rewrite lift_fuse_three_full in H. exact H. }
  apply check_of_synth_pres. eapply sy_pi; [exact HIT |].
  apply check_of_synth_pres. eapply sy_pi; [exact HX1 |].
  apply check_of_synth_pres. eapply sy_pi; [exact HAll | exact HBody].
Qed.

Lemma ind_step_apply_full : forall G R P stp i xs h IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) ->
  check G stp
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1))))))) ->
  check G i IT ->
  check G xs (TInterp (TApp R i) (TMuI R)) ->
  check G h (TIAll (TApp R i) (TMuI R) xs P) ->
  check G (TApp (TApp (TApp stp i) xs) h)
    (TApp P (TPair i (TIn xs))).
Proof.
  intros G R P stp i xs h IT HIT HR HP Hstp Hi Hxs Hh.
  pose proof (ind_step_type_formation_full _ _ _ _ HIT HR HP) as Hform0.
  destruct (check_pi_components_pres _ _ _ _ Hform0)
    as [k0 [_ HB0]].
  pose proof (checked_app_full _ _ _ _ _ 0 Hform0 Hstp Hi) as H1.
  pose proof (check_subst0_full G IT i _ (TSort k0) Hi HB0) as Hform1.
  cbn [subst] in H1. simpl in H1.
  cbn [subst] in Hform1. simpl in Hform1.
  repeat rewrite subst_lift_zero_full in H1.
  repeat rewrite subst_lift_zero_full in Hform1.
  repeat rewrite lift_zero_full in H1.
  repeat rewrite lift_zero_full in Hform1.
  destruct (check_pi_components_pres _ _ _ _ Hform1)
    as [k1 [_ HB1]].
  pose proof (checked_app_full _ _ _ _ _ k0 Hform1 H1 Hxs) as H2.
  pose proof (check_subst0_full G _ xs _ (TSort k1) Hxs HB1) as Hform2.
  cbn [subst] in H2. simpl in H2.
  cbn [subst] in Hform2. simpl in Hform2.
  repeat rewrite subst_eta_cancel_full in H2.
  repeat rewrite subst_eta_cancel_full in Hform2.
  repeat rewrite subst_lift_zero_full in H2.
  repeat rewrite subst_lift_zero_full in Hform2.
  repeat rewrite lift_zero_full in H2.
  repeat rewrite lift_zero_full in Hform2.
  repeat rewrite subst_lift_two_full in H2.
  repeat rewrite subst_lift_two_full in Hform2.
  pose proof (checked_app_full _ _ _ _ _ k1 Hform2 H2 Hh) as H3.
  cbn [subst] in H3. simpl in H3.
  repeat rewrite subst_eta_cancel_full in H3.
  repeat rewrite subst_lift_zero_full in H3.
  repeat rewrite lift_zero_full in H3.
  repeat rewrite subst_lift_two_full in H3.
  rewrite subst_lift_three_full in H3.
  exact H3.
Qed.

Lemma ind_hypothesis_full : forall G R P stp IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) ->
  check G stp
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1))))))) ->
  check G
    (TLam (TLam
      (TInd (lift 2 0 R) (lift 2 0 P) (lift 2 0 stp)
        (TVar 1) (TVar 0))))
    (TPi IT
      (TPi (TApp (TMuI (lift 1 0 R)) (TVar 0))
        (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))).
Proof.
  intros G R P stp IT HIT HR HP Hstp.
  assert (HW1 : wf (IT :: G)).
  { eapply wf_cons with (k := 0); [eapply check_context_wf; exact HIT | exact HIT]. }
  pose proof (check_weaken0_full G IT IT (TSort 0) HW1 HIT) as HIT1.
  pose proof (check_weaken0_full G IT R
    (TPi IT (TIDesc (lift 1 0 IT))) HW1 HR) as HR1.
  assert (Hmu1 : check (IT :: G) (TMuI (lift 1 0 R))
    (TPi (lift 1 0 IT) (TSort 0))).
  { apply check_of_synth_pres. eapply sy_mui.
    - exact HIT1.
    - cbn [lift] in HR1. rewrite lift_lift_one_zero_full in HR1.
      exact HR1. }
  assert (Hpi1 : check (IT :: G) (TPi (lift 1 0 IT) (TSort 0)) (TSort 1)).
  { assert (HWpi : wf (lift 1 0 IT :: IT :: G)).
    { eapply wf_cons with (k := 0); [exact HW1 | exact HIT1]. }
    apply check_of_synth_pres. eapply sy_pi.
    - eapply ch_sub; [exact HIT1 | apply su_sort; lia].
    - apply check_of_synth_pres, sy_sort. exact HWpi. }
  assert (Hi0 : check (IT :: G) (TVar 0) (lift 1 0 IT)).
  { apply check_of_synth_pres. eapply sy_var; [exact HW1 | reflexivity]. }
  assert (HX1 : check (IT :: G)
    (TApp (TMuI (lift 1 0 R)) (TVar 0)) (TSort 0)).
  { pose proof (@ch_app (IT :: G) (TMuI (lift 1 0 R)) (TVar 0)
      (lift 1 0 IT) (TSort 0) 1 Hpi1 Hmu1 Hi0) as H.
    cbn [subst] in H. exact H. }
  set (X1 := TApp (TMuI (lift 1 0 R)) (TVar 0)) in *.
  assert (HW2 : wf (X1 :: IT :: G)).
  { eapply wf_cons with (k := 0); [exact HW1 | exact HX1]. }
  pose proof (check_weaken0_full (IT :: G) X1 (lift 1 0 IT)
    (TSort 0) HW2 HIT1) as HIT2.
  pose proof (check_weaken0_full G IT R
    (TPi IT (TIDesc (lift 1 0 IT))) HW1 HR) as HR1'.
  pose proof (check_weaken0_full (IT :: G) X1 (lift 1 0 R)
    (lift 1 0 (TPi IT (TIDesc (lift 1 0 IT)))) HW2 HR1') as HR2.
  pose proof (check_weaken0_full G IT P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0))
    HW1 HP) as HP1.
  pose proof (check_weaken0_full (IT :: G) X1 (lift 1 0 P)
    (lift 1 0
      (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)))
    HW2 HP1) as HP2.
  pose proof (check_weaken0_full G IT stp _ HW1 Hstp) as Hstp1.
  pose proof (check_weaken0_full (IT :: G) X1 (lift 1 0 stp) _ HW2 Hstp1)
    as Hstp2.
  apply ch_lam, ch_lam.
  apply check_of_synth_pres.
  eapply sy_ind with (IT := lift 2 0 IT).
  - rewrite <- lift_lift_one_zero_full in HIT2.
    rewrite (lift_fuse_two_full IT 0) in HIT2. exact HIT2.
  - cbn [lift] in HR2.
    repeat rewrite <- lift_lift_one_zero_full in HR2.
    repeat rewrite lift_fuse_two_full in HR2.
    repeat rewrite lift_two_gap1_full in HR2.
    exact HR2.
  - cbn [lift] in HP2.
    repeat rewrite <- lift_lift_one_zero_full in HP2.
    repeat rewrite lift_fuse_two_full in HP2.
    repeat rewrite lift_two_gap1_full in HP2.
    cbn [Nat.ltb] in HP2.
    exact HP2.
  - rewrite lift_ind_step_type_two_full in Hstp2.
    rewrite <- lift_lift_one_zero_full in Hstp2.
    rewrite lift_fuse_two_full in Hstp2.
    exact Hstp2.
  - apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity].
  - assert (Hx : check (X1 :: IT :: G) (TVar 0) (lift 1 0 X1)).
    { apply check_of_synth_pres. eapply sy_var; [exact HW2 | reflexivity]. }
    unfold X1 in Hx. cbn [lift] in Hx.
    rewrite <- lift_lift_one_zero_full in Hx.
    rewrite lift_fuse_two_full in Hx. exact Hx.
Qed.

Lemma ind_root_from_payload_full : forall G R P stp i xs IT,
  check G IT (TSort 0) ->
  check G R (TPi IT (TIDesc (lift 1 0 IT))) ->
  check G P
    (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) ->
  check G stp
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1))))))) ->
  check G i IT ->
  check G (TIn xs) (TApp (TMuI R) i) ->
  check G
    (TApp (TApp (TApp stp i) xs)
      (THyps (TApp R i) (TMuI R) P
        (TLam (TLam
          (TInd (lift 2 0 R) (lift 2 0 P) (lift 2 0 stp)
            (TVar 1) (TVar 0)))) xs))
    (TApp P (TPair i (TIn xs))).
Proof.
  intros G R P stp i xs IT HIT HR HP Hstp Hi Hin.
  pose proof (mui_in_payload_same_full _ _ _ _ _ HIT HR Hi Hin) as Hxs.
  pose proof (checked_app_full _ _ _ _ _ 1
    (idesc_family_type_formation_full _ _ _ HIT HIT) HR Hi) as HD.
  cbn [subst] in HD. rewrite subst_lift_zero_full in HD.
  assert (Hmu : check G (TMuI R) (TPi IT (TSort 0))).
  { apply check_of_synth_pres. eapply sy_mui; eassumption. }
  pose proof (ind_hypothesis_full _ _ _ _ _ HIT HR HP Hstp) as Hh.
  assert (Hhyps : check G
    (THyps (TApp R i) (TMuI R) P
      (TLam (TLam
        (TInd (lift 2 0 R) (lift 2 0 P) (lift 2 0 stp)
          (TVar 1) (TVar 0)))) xs)
    (TIAll (TApp R i) (TMuI R) xs P)).
  { apply check_of_synth_pres. eapply sy_hyps; eassumption. }
  eapply ind_step_apply_full; eassumption.
Qed.

Lemma preservation_full_draft : forall G t A,
  check G t A -> forall u, step t u -> check G u A.
Proof.
  intros G t A Hty.
  induction Hty using check_mut_ind_pres
    with (P := fun G (_ : wf G) => True)
         (P0 := fun G t A (_ : synth G t A) =>
                  forall u, step t u -> check G u A)
         (P1 := fun G t A (_ : check G t A) =>
                  forall u, step t u -> check G u A)
         (P2 := fun G Sf i E Q bs (_ : check_branches G Sf i E Q bs) => True)
         (P3 := fun G A B (_ : sub G A B) => True);
    try exact I;
    try match goal with
    | Hc : conv ?X ?Y,
      IH : forall u, step ?t u -> check ?G u ?X
      |- forall u, step ?t u -> check ?G u ?Y =>
        intros u Hu; eapply ch_expand; [apply cv_sym; exact Hc | eauto]
    | Hs : sub ?G ?X ?Y,
      IH : forall u, step ?t u -> check ?G u ?X
      |- forall u, step ?t u -> check ?G u ?Y =>
        intros u Hu; eapply ch_sub; [eauto | exact Hs]
    | Hc : conv ?X ?Y,
      IH : forall u, step ?t u -> check ?G u ?Y
      |- forall u, step ?t u -> check ?G u ?X =>
        intros u Hu; eapply ch_expand; [exact Hc | eauto]
    end;
    intros u Hred; inversion Hred; subst;
    repeat match goal with
    | Hbad : synth _ (TLam _) _ |- _ => inversion Hbad
    | Hbad : synth _ (TPair _ _) _ |- _ => inversion Hbad
    | Hbad : synth _ (TIn _) _ |- _ => inversion Hbad
    end;
    try match goal with
    | HE : step ?E ?E',
      IHE : forall u, step ?E u -> check ?G u TEnumU,
      HP : check ?G ?P (TPi (TEnumT ?E) (TSort ?k))
      |- check ?G (TEPi ?E' ?P) (TSort ?k) =>
        apply check_of_synth_pres; eapply sy_epi;
        [eapply IHE; exact HE |];
        eapply ch_expand;
        [ apply cv_pi; [apply cv_enumt, cv_sym, cv_step; exact HE | apply cv_refl]
        | exact HP ]
    end;
    try match goal with
    | Hck : check ?G _ _ |- check ?G TUnitT (TSort _) =>
        apply check_unit_type; eapply check_context_wf; exact Hck
    | Hsy : synth ?G _ _ |- check ?G TUnitT (TSort _) =>
        apply check_unit_type; eapply synth_context_wf; exact Hsy
    end;
    try match goal with
    | Hck : check ?G _ _ |- check ?G TUnit (TIAll TI1 _ TUnit _) =>
        apply hyps_one_root; eapply check_context_wf; exact Hck
    | Hsy : synth ?G _ _ |- check ?G TUnit (TIAll TI1 _ TUnit _) =>
        apply hyps_one_root; eapply synth_context_wf; exact Hsy
    end;
    try match goal with
    | HE : step ?E ?E',
      IHE : forall u, step ?E u -> check ?G u TEnumU,
      HP : check ?G ?P (TPi (TEnumT ?E) (TSort ?k)),
      Hp : check ?G ?p (TEPi ?E ?P),
      He : check ?G ?e (TEnumT ?E)
      |- check ?G (TSwitch ?E' ?P ?p ?e) (TApp ?P ?e) =>
        apply check_of_synth_pres; eapply sy_switch;
        [ eapply IHE; exact HE
        | eapply ch_expand;
          [ apply cv_pi; [apply cv_enumt, cv_sym, cv_step; exact HE | apply cv_refl]
          | exact HP ]
        | eapply ch_expand;
          [ apply cv_epi; [apply cv_sym, cv_step; exact HE | apply cv_refl]
          | exact Hp ]
        | eapply ch_expand;
          [ apply cv_enumt, cv_sym, cv_step; exact HE | exact He ] ]
    | Hpstep : step ?p ?p',
      IHp : forall u, step ?p u -> check ?G u (TEPi ?E ?P),
      HE : check ?G ?E TEnumU,
      HP : check ?G ?P (TPi (TEnumT ?E) (TSort ?k)),
      He : check ?G ?e (TEnumT ?E)
      |- check ?G (TSwitch ?E ?P ?p' ?e) (TApp ?P ?e) =>
        apply check_of_synth_pres; eapply sy_switch;
        [exact HE | exact HP | eapply IHp; exact Hpstep | exact He]
    | Hestep : step ?e ?e',
      IHe : forall u, step ?e u -> check ?G u (TEnumT ?E),
      HE : check ?G ?E TEnumU,
      HP : check ?G ?P (TPi (TEnumT ?E) (TSort ?k)),
      Hp : check ?G ?p (TEPi ?E ?P)
      |- check ?G (TSwitch ?E ?P ?p ?e') (TApp ?P ?e) =>
        eapply ch_expand;
        [ apply cv_app; [apply cv_refl | apply cv_step; exact Hestep]
        | apply check_of_synth_pres; eapply sy_switch;
          [exact HE | exact HP | exact Hp | eapply IHe; exact Hestep] ]
    end;
    try match goal with
    | HDstep : step ?D ?D',
      IHD : forall u, step ?D u -> check ?G u (TIDesc ?IT),
      HIT : check ?G ?IT (TSort 0),
      HX : check ?G ?X (TPi ?IT (TSort 0))
      |- check ?G (TInterp ?D' ?X) (TSort 0) =>
        apply check_of_synth_pres; eapply sy_interp;
        [exact HIT | eapply IHD; exact HDstep | exact HX]
    end;
    try match goal with
    | HDstep : step ?D ?D',
      IHD : forall u, step ?D u -> check ?G u (TIDesc ?IT),
      HIT : check ?G ?IT (TSort 0),
      HX : check ?G ?X (TPi ?IT (TSort 0)),
      Hxs : check ?G ?xs (TInterp ?D ?X),
      HP : check ?G ?P
        (TPi (TSigma ?IT (TApp (lift 1 0 ?X) (TVar 0))) (TSort 0))
      |- check ?G (TIAll ?D' ?X ?xs ?P) (TSort 0) =>
        apply check_of_synth_pres; eapply sy_iall;
        [exact HIT | eapply IHD; exact HDstep | exact HX | | exact HP];
        eapply ch_expand;
        [ apply cv_interp; [apply cv_sym, cv_step; exact HDstep | apply cv_refl]
        | exact Hxs ]
    | Hxsstep : step ?xs ?xs',
      IHxs : forall u, step ?xs u -> check ?G u (TInterp ?D ?X),
      HIT : check ?G ?IT (TSort 0),
      HD : check ?G ?D (TIDesc ?IT),
      HX : check ?G ?X (TPi ?IT (TSort 0)),
      HP : check ?G ?P
        (TPi (TSigma ?IT (TApp (lift 1 0 ?X) (TVar 0))) (TSort 0))
      |- check ?G (TIAll ?D ?X ?xs' ?P) (TSort 0) =>
        apply check_of_synth_pres; eapply sy_iall;
        [exact HIT | exact HD | exact HX | eapply IHxs; exact Hxsstep | exact HP]
    end;
    try match goal with
    | Hastep : step ?a ?a',
      IHa : forall u, step ?a u -> check ?G u ?A,
      Hb : check ?G ?b (subst ?a 0 ?B)
      |- check ?G (TPair ?a' ?b) (TSigma ?A ?B) =>
        apply ch_pair;
        [eapply IHa; exact Hastep |];
        eapply ch_expand;
        [ eapply conv_subst_full; [apply cv_refl | apply cv_sym, cv_step; exact Hastep]
        | exact Hb ]
    end;
    try match goal with
    | |- check _ (TCase _ _ (_ ++ _ :: _)) _ =>
        exfalso; eapply case_label_step_impossible_pres; eassumption
    end;
    try match goal with
    | HMstep : step ?M ?M',
      IHM : forall u, step ?M u -> check ?G u (TApp (SigMu ?E ?Sf) ?i)
      |- check ?G (TCase ?M' ?Q ?bs) ?Q =>
        apply check_of_synth_pres; eapply sy_case; eauto 6
    end;
    try match goal with
    | Hxstep : step ?x ?x',
      IHx : forall u, step ?x u -> check ?G u (TApp (TMuI ?R) ?i)
      |- check ?G (TInd ?R ?P ?stp ?i ?x') (TApp ?P (TPair ?i ?x)) =>
        eapply ch_expand;
        [ apply cv_app; [apply cv_refl | apply cv_pair; [apply cv_refl | apply cv_step; exact Hxstep]]
        | apply check_of_synth_pres; eapply sy_ind; eauto 6 ]
    end;
    try match goal with
    | HDstep : step ?D ?D',
      IHD : forall u, step ?D u -> check ?G u (TIDesc ?IT)
      |- check ?G (THyps ?D' ?X ?P ?h ?xs) (TIAll ?D ?X ?xs ?P) =>
        eapply ch_expand;
        [ apply cv_iall; [apply cv_step; exact HDstep | apply cv_refl | apply cv_refl | apply cv_refl]
        | apply check_of_synth_pres; eapply sy_hyps; eauto 6;
          eapply ch_expand;
          [apply cv_interp; [apply cv_sym, cv_step; exact HDstep | apply cv_refl] | eassumption] ]
    | Hxsstep : step ?xs ?xs',
      IHxs : forall u, step ?xs u -> check ?G u (TInterp ?D ?X)
      |- check ?G (THyps ?D ?X ?P ?h ?xs') (TIAll ?D ?X ?xs ?P) =>
        eapply ch_expand;
        [ apply cv_iall; [apply cv_refl | apply cv_refl | apply cv_step; exact Hxsstep | apply cv_refl]
        | apply check_of_synth_pres; eapply sy_hyps; eauto 6 ]
    end;
    try match goal with
    | Hp : step ?p ?p',
      Hform : check ?G (TSigma ?A ?B) (TSort ?k),
      IH : forall u, step ?p u -> check ?G u ?C,
      He : eval ?C (TSigma ?A ?B)
      |- check ?G (TSnd ?p') (subst (TFst ?p) 0 ?B) =>
        eapply ch_expand;
        [ eapply conv_subst_full; [apply cv_refl | apply cv_step, st_fst1; exact Hp]
        | eapply snd_congr_root; [exact Hform | eapply IH; exact Hp | exact He] ]
    end;
    try match goal with
    | Hpstep : step ?p ?p',
      IHp : forall u, step ?p u -> check ?G u (TSigma ?A ?B),
      Hform : check ?G (TSigma ?A ?B) (TSort ?k)
      |- check ?G (TSnd ?p') (subst (TFst ?p) 0 ?B) =>
        eapply ch_expand;
        [ eapply conv_subst_full; [apply cv_refl | apply cv_step, st_fst1; exact Hpstep]
        | eapply ch_snd; [exact Hform | eapply IHp; exact Hpstep] ]
    end;
    try match goal with
    | Hpair : step (TPair ?c ?xs) ?x'
      |- check ?G (TIn ?x') (TApp (SigMu ?E ?Sf) ?i) =>
        inversion Hpair; subst
    end;
    try match goal with
    | Hastep : step ?a ?a',
      IHa : forall u, step ?a u -> check ?G u (Label ?E),
      Hmem : spine_mem ?a ?Phi,
      Hxs : check ?G ?xs
        (TInterp (TApp (branches (TApp ?Sf ?i)) ?a) (Carrier ?E ?Sf))
      |- check ?G (TIn (TPair ?a' ?xs)) (TApp (SigMu ?E ?Sf) ?i) =>
        eapply ch_in_sig; try eassumption;
        try solve [eapply IHa; exact Hastep];
        try solve [eapply spine_mem_conv_pres; [apply cv_step; exact Hastep | exact Hmem]];
        try solve [eapply ch_expand;
          [apply sig_payload_conv_pres, cv_step; exact Hastep | exact Hxs]]
    end;
    try match goal with
    | Hp : check ?G (TPair ?a ?b) (TSigma ?A ?B)
      |- check ?G ?a ?A => eapply checked_pair_fst_full; exact Hp
    | Hp : check ?G (TPair ?a ?b) (TSigma ?A ?B)
      |- check ?G ?b (subst (TFst (TPair ?a ?b)) 0 ?B) =>
        eapply checked_pair_snd_full; exact Hp
    end;
    try match goal with
    | Hlam : check ?G (TLam ?b) (TPi ?A ?B),
      Ha : check ?G ?a ?A,
      Hform : check ?G (TPi ?A ?B) (TSort ?k)
      |- check ?G (subst ?a 0 ?b) (subst ?a 0 ?B) =>
        eapply (beta_root check_subst0_full sub_pi_application_full);
        [exact Hform | exact Hlam | exact Ha]
    end;
    try solve [
      let H := fresh "Hdata" in
      pose proof (epi_cons_compute_data_full _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply epi_cons_root; eassumption];
    try solve [
      let H := fresh "Hparts" in
      pose proof (epi_cons_pair_components_full _ _ _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H; destruct H;
      eapply switch_zero_root; eassumption];
    try solve [eapply switch_succ_compute_full; eassumption];
    try solve [eapply interp_var_root; [eassumption | eapply ivar_same_index_full; eassumption | eassumption]];
    try solve [
      let H := fresh "Hdata" in
      pose proof (interp_prod_compute_full _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; apply check_of_synth_pres; eapply sy_sigma; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (interp_pi_compute_full _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply interp_pi_root; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (interp_sig_compute_full _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply interp_sig_root; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (interp_choice_compute_full _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply interp_choice_root; eassumption];
    try solve [eapply iall_var_compute_full; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (iall_prod_compute_full _ _ _ _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
        ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply iall_prod_root; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (iall_pi_compute_full _ _ _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
        ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply iall_pi_root; eassumption];
    try solve [eapply iall_sig_compute_full; eassumption];
    try solve [eapply iall_choice_compute_full; eassumption];
    try solve [eapply hyps_var_root; eapply hyps_var_compute_full; eassumption];
    try solve [
      let H := fresh "Hdata" in
      pose proof (hyps_prod_compute_full _ _ _ _ _ _ _ _ _
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
        ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as H;
      destruct H; eapply hyps_prod_root; eassumption];
    try solve [eapply hyps_pi_root; eapply hyps_pi_compute_full; eassumption];
    try solve [eapply hyps_sig_root; eapply hyps_sig_compute_full; eassumption];
    try solve [eapply hyps_choice_root; eapply hyps_choice_compute_full; eassumption];
    try match goal with
    | Hscrut : check ?G (TIn (TPair ?a ?xs)) (TApp (SigMu ?E ?Sf) ?i),
      HIT : check ?G ?IT (TSort 0),
      HE : check ?G ?E TEnumU,
      HSf : check ?G ?Sf
        (TPi ?IT (Sig (lift 1 0 ?IT) (lift 1 0 ?E))),
      Hi : check ?G ?i ?IT,
      Hbs : check_branches ?G ?Sf ?i ?E ?Q ?bs,
      Hnth : nth_error ?bs ?k = Some (?c, ?b),
      Hc : enum_pos ?c ?n,
      Ha : enum_pos ?a ?n
      |- check ?G (subst ?xs 0 ?b) ?Q =>
        eapply case_root_from_payload with
          (Sf := Sf) (i := i) (E := E) (bs := bs)
          (a := a) (k := k) (c := c) (n := n);
        [ exact Hbs | exact Hnth | exact Hc | exact Ha
        | eapply mus_in_pair_payload_same_full; eassumption
        | exact check_subst0_full | exact subst_lift_zero_full ]
    end;
    try solve [eapply case_root_from_payload;
      eauto 12 using mus_in_pair_payload_same_full];
    try solve [eapply ind_root_from_payload_full; eauto 12];
    eauto 4 using check, synth, beta_root,
      check_subst0_full, sub_pi_application_full,
      epi_nil_root, interp_var_root, interp_one_root,
      iall_one_root, hyps_one_root, app_congr_root,
      fst_congr_root, snd_congr_root.
Qed.
End FullDraft.

(* Production adapters.  These keep the preservation proof independent of
   the premise ordering used by the structural metatheory. *)
Lemma check_subst0_pres : forall G A u t B,
  check G u A -> check (A :: G) t B ->
  check G (subst u 0 t) (subst u 0 B).
Proof. intros; eapply check_subst0; eassumption. Qed.

Lemma check_weaken0_pres : forall G A t B,
  wf (A :: G) -> check G t B ->
  check (A :: G) (lift 1 0 t) (lift 1 0 B).
Proof. intros; eapply check_weaken0; eassumption. Qed.

Lemma conv_lift_pres : forall t u d k,
  conv t u -> conv (lift d k t) (lift d k u).
Proof. intros; eapply conv_lift_typing; eassumption. Qed.

Ltac apply_conv_head_pres :=
  match goal with
  | |- conv (TPi _ _) (TPi _ _) => apply cv_pi
  | |- conv (TLam _) (TLam _) => apply cv_lam
  | |- conv (TApp _ _) (TApp _ _) => apply cv_app
  | |- conv (TSigma _ _) (TSigma _ _) => apply cv_sigma
  | |- conv (TPair _ _) (TPair _ _) => apply cv_pair
  | |- conv (TFst _) (TFst _) => apply cv_fst
  | |- conv (TSnd _) (TSnd _) => apply cv_snd
  | |- conv (TConsE _ _) (TConsE _ _) => apply cv_conse
  | |- conv (TEnumT _) (TEnumT _) => apply cv_enumt
  | |- conv (TESucc _) (TESucc _) => apply cv_esucc
  | |- conv (TEPi _ _) (TEPi _ _) => apply cv_epi
  | |- conv (TSwitch _ _ _ _) (TSwitch _ _ _ _) => apply cv_switch
  | |- conv (TIDesc _) (TIDesc _) => apply cv_idesc
  | |- conv (TIVar _) (TIVar _) => apply cv_ivar
  | |- conv (TIProd _ _) (TIProd _ _) => apply cv_iprod
  | |- conv (TIPi _ _) (TIPi _ _) => apply cv_ipi
  | |- conv (TISig _ _) (TISig _ _) => apply cv_isig
  | |- conv (TIChoice _ _) (TIChoice _ _) => apply cv_ichoice
  | |- conv (TInterp _ _) (TInterp _ _) => apply cv_interp
  | |- conv (TMuI _) (TMuI _) => apply cv_mui
  | |- conv (TMuS _) (TMuS _) => apply cv_mus
  | |- conv (TIn _) (TIn _) => apply cv_in
  | |- conv (TInd _ _ _ _ _) (TInd _ _ _ _ _) => apply cv_ind
  | |- conv (TIAll _ _ _ _) (TIAll _ _ _ _) => apply cv_iall
  | |- conv (THyps _ _ _ _ _) (THyps _ _ _ _ _) => apply cv_hyps
  | |- conv (TList _) (TList _) => apply cv_list
  | |- conv (TLNil _) (TLNil _) => apply cv_lnil
  | |- conv (TLCons _ _ _) (TLCons _ _ _) => apply cv_lcons
  end.

Ltac solve_conv_head_pres IH Haa :=
  apply_conv_head_pres;
  (eapply IH; [cbn; lia | exact Haa]).

Lemma conv_subst_arg_pres : forall t k a a',
  conv a a' -> conv (subst a k t) (subst a' k t).
Proof.
  apply (tsize_strong_ind (fun t => forall k a a',
    conv a a' -> conv (subst a k t) (subst a' k t))).
  intros t IH k a a' Haa. destruct t; cbn [subst].
  all: try solve [apply cv_refl].
  all: try solve [solve_conv_head_pres IH Haa].
  - destruct (n <? k) eqn:Hnk; [apply cv_refl |].
    destruct (n =? k) eqn:Hneq; [apply conv_lift_pres; exact Haa | apply cv_refl].
  - eapply cv_trans.
    + apply cv_case.
      * eapply IH; [cbn; lia | exact Haa].
      * eapply IH; [cbn; lia | exact Haa].
    + assert (HB : forall pre xs,
          (forall c b, In (c,b) xs -> In (c,b) bs) ->
          conv
            (TCase (subst a' k t1) (subst a' k t2)
              (pre ++ map (fun '(x,y) =>
                (subst a k x, subst a (S k) y)) xs))
            (TCase (subst a' k t1) (subst a' k t2)
              (pre ++ map (fun '(x,y) =>
                (subst a' k x, subst a' (S k) y)) xs))).
      { intros pre xs Hinc. revert pre Hinc.
        induction xs as [|[c b] xs IHxs]; intros pre Hinc; cbn.
        - apply cv_refl.
        - eapply cv_trans.
          + apply cv_case_br.
            * eapply IH. eapply tsize_case_bs. apply Hinc. left; reflexivity.
              exact Haa.
            * eapply IH. eapply tsize_case_bs_body. apply Hinc. left; reflexivity.
              exact Haa.
          + pose proof (IHxs
              (pre ++ [(subst a' k c, subst a' (S k) b)])
              ltac:(intros; apply Hinc; right; assumption)) as Htail.
            replace
              (pre ++ (subst a' k c, subst a' (S k) b) ::
                map (fun '(x,y) => (subst a k x, subst a (S k) y)) xs)
              with
              ((pre ++ [(subst a' k c, subst a' (S k) b)]) ++
                map (fun '(x,y) => (subst a k x, subst a (S k) y)) xs)
              by (rewrite <- app_assoc; reflexivity).
            replace
              (pre ++ (subst a' k c, subst a' (S k) b) ::
                map (fun '(x,y) => (subst a' k x, subst a' (S k) y)) xs)
              with
              ((pre ++ [(subst a' k c, subst a' (S k) b)]) ++
                map (fun '(x,y) => (subst a' k x, subst a' (S k) y)) xs)
              by (rewrite <- app_assoc; reflexivity).
            exact Htail. }
      apply (HB [] bs). auto.
Qed.

Lemma conv_subst_pres : forall k t t' a a',
  conv t t' -> conv a a' ->
  conv (subst a k t) (subst a' k t').
Proof.
  intros k t t' a a' Htt Haa.
  eapply cv_trans.
  - exact (conv_subst_same _ _ Htt a k).
  - apply conv_subst_arg_pres; exact Haa.
Qed.

Lemma checked_pair_snd_pres_closed : forall G a b A B k,
  check G (TSigma A B) (TSort k) ->
  check G (TPair a b) (TSigma A B) ->
  check G b (subst (TFst (TPair a b)) 0 B).
Proof.
  intros G a b A B k _ Hpair.
  destruct (SignatureLemmas.pair_origin _ _ _ _ Hpair)
    as [A0 [B0 [Ha [Hb Hsub]]]].
  destruct (conv_sigma_components _ _ _ _
    (SignatureLemmas.sub_sigma_endpoints_conv _ _ _ _ _ Hsub)) as [_ HB].
  eapply ch_expand.
  - eapply conv_subst_pres.
    + apply cv_sym; exact HB.
    + apply cv_step, st_fst.
  - exact Hb.
Qed.

Lemma sub_pi_action_pres : forall G X Y,
  sub G X Y -> forall A0 B0 A B a,
  conv X (TPi A0 B0) -> conv Y (TPi A B) -> check G a A ->
  check G a A0 /\ sub G (subst a 0 B0) (subst a 0 B).
Proof.
  intros G X Y Hsub; induction Hsub;
    intros A0 B0 A1 B1 a HX HY Ha.
  - pose proof (cv_trans (cv_sym HX) (cv_trans H HY)) as HPi.
    destruct (conv_pi_components _ _ _ _ HPi) as [Hdom Hcod].
    split.
    + eapply ch_expand; [exact Hdom | exact Ha].
    + apply su_conv. eapply conv_subst_pres; [exact Hcod | apply cv_refl].
  - assert (Hmid : exists Am Bm, conv B (TPi Am Bm)).
    { destruct (sub_transport _ _ _ Hsub2
        (TPi A1 B1) HPi HY (whd_shape _ HPi (hs_pi A1 B1)))
        as [HC | [[HK [U [HC HW]]] | [HK _]]].
      - exists A1, B1; exact HC.
      - destruct HK as [HK | [HK | HK]]; try discriminate.
        subst. destruct HW as [V [HE HV]]. inversion HV; subst.
        eexists; eexists. eapply cv_trans; [exact HC |].
        apply conv_of_eval_pres; exact HE.
      - discriminate. }
    destruct Hmid as [Am [Bm HM]].
    destruct (IHHsub2 Am Bm A1 B1 a HM HY Ha) as [Ham Hcod2].
    destruct (IHHsub1 A0 B0 Am Bm a HX HM Ham) as [Ha0 Hcod1].
    split; [exact Ha0 | eapply su_trans; eassumption].
  - exfalso.
    pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HSort (hs_sort k))
      (whd_shape _ HPi (hs_pi A1 B1))) as K; discriminate.
  - destruct (conv_pi_components _ _ _ _ HX) as [Hsd Hsc].
    destruct (conv_pi_components _ _ _ _ HY) as [Htd Htc].
    assert (Ha' : check Γ a A').
    { eapply ch_expand; [exact Htd | exact Ha]. }
    assert (HaS : check Γ a A).
    { eapply ch_sub; [exact Ha' | exact Hsub1]. }
    split.
    + eapply ch_expand; [apply cv_sym; exact Hsd | exact HaS].
    + eapply su_trans.
      * apply su_conv. eapply conv_subst_pres;
          [apply cv_sym; exact Hsc | apply cv_refl].
      * eapply su_trans.
        -- eapply sub_subst0; [exact Hsub2 | exact Ha'].
        -- apply su_conv. eapply conv_subst_pres;
             [exact Htc | apply cv_refl].
  - exfalso.
    assert (HW : whd (TApp (Carrier E Sf) i) HMuIApp).
    { unfold Carrier. apply whd_shape. constructor. }
    pose proof (conv_whd _ _ _ _ HY
      HW
      (whd_shape _ HPi (hs_pi A1 B1))) as K; discriminate.
  - exfalso.
    pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HMuSApp (hs_musapp (TPair E S2) i))
      (whd_shape _ HPi (hs_pi A1 B1))) as K; discriminate.
Qed.

Theorem sub_pi_application_pres_closed : forall G A0 B0 A B a k,
  check G (TPi A B) (TSort k) ->
  sub G (TPi A0 B0) (TPi A B) -> check G a A ->
  check G a A0 /\ sub G (subst a 0 B0) (subst a 0 B).
Proof.
  intros G A0 B0 A B a k _ Hsub Ha.
  eapply sub_pi_action_pres; [exact Hsub | apply cv_refl | apply cv_refl | exact Ha].
Qed.

Lemma subst_eta_cancel_pres : forall t,
  subst (TVar 0) 0 (lift 1 1 t) = t.
Proof. intro; apply _tmp_eta_cancel.subst_eta_beta_cancel_gen. Qed.

Lemma subst_lift_two_pres : forall t a b,
  subst b 0 (subst a 1 (lift 2 0 t)) = t.
Proof.
  intros t a b.
  assert (E : lift 2 0 t = lift 1 1 (lift 1 0 t)).
  { symmetry. change (lift 1 (0 + 1) (lift 1 0 t) = lift (1 + 1) 0 t).
    apply lift_fuse; lia. }
  rewrite E.
  rewrite !subst_lift_cancel. reflexivity.
Qed.

Lemma subst_lift_three_pres : forall t a b c,
  subst c 0 (subst b 1 (subst a 2 (lift 3 0 t))) = t.
Proof.
  intros t a b c.
  assert (E3 : lift 3 0 t = lift 1 2 (lift 2 0 t)).
  { symmetry. change (lift 1 (0 + 2) (lift 2 0 t) = lift (1 + 2) 0 t).
    apply lift_fuse; lia. }
  assert (E2 : lift 2 0 t = lift 1 1 (lift 1 0 t)).
  { symmetry. change (lift 1 (0 + 1) (lift 1 0 t) = lift (1 + 1) 0 t).
    apply lift_fuse; lia. }
  rewrite E3, E2.
  rewrite !subst_lift_cancel. reflexivity.
Qed.

Lemma lift_lift_one_zero_pres : forall t,
  lift 1 1 (lift 1 0 t) = lift 1 0 (lift 1 0 t).
Proof. intro; apply lift_lift_one_zero. Qed.

Lemma lift_lift_two_zero_pres : forall t,
  lift 1 2 (lift 2 0 t) = lift 2 0 (lift 1 0 t).
Proof. intro; apply lift_lift_two_zero. Qed.

Lemma lift_fuse_two_pres : forall t k,
  lift 1 (S k) (lift 1 k t) = lift 2 k t.
Proof.
  intros. replace (S k) with (k + 1) by lia.
  replace 2 with (1 + 1) by lia. apply lift_fuse; lia.
Qed.

Lemma lift_two_gap1_pres : forall t,
  lift 1 1 (lift 2 0 t) = lift 1 0 (lift 2 0 t).
Proof.
  intro t.
  transitivity (lift 3 0 t).
  - change (lift 1 (0 + 1) (lift 2 0 t) = lift (1 + 2) 0 t).
    apply lift_fuse; lia.
  - symmetry. change (lift 1 (0 + 0) (lift 2 0 t) = lift (1 + 2) 0 t).
    apply lift_fuse; lia.
Qed.

Lemma lift_fuse_three_pres : forall t,
  lift 1 0 (lift 2 0 t) = lift 3 0 t.
Proof.
  intro. change (lift 1 (0 + 0) (lift 2 0 t) = lift (1 + 2) 0 t).
  apply lift_fuse; lia.
Qed.

Lemma lift_fuse_same_pres : forall t k,
  lift 1 k (lift 1 k t) = lift 2 k t.
Proof.
  intros. replace k with (k + 0) at 1 by lia.
  replace 2 with (1 + 1) by lia.
  apply lift_fuse; lia.
Qed.

Lemma lift_var_below_pres : forall n d k, n < k ->
  lift d k (TVar n) = TVar n.
Proof.
  intros n d k Hlt. cbn [lift].
  destruct (n <? k) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E; lia.
Qed.

Lemma lift_ind_step_type_two_pres : forall R P IT,
  lift 1 0 (lift 1 0
    (TPi IT
      (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
        (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                    (TVar 0) (lift 2 0 P))
          (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1)))))))) =
  TPi (lift 2 0 IT)
    (TPi (TInterp (TApp (lift 1 0 (lift 2 0 R)) (TVar 0))
                  (TMuI (lift 1 0 (lift 2 0 R))))
      (TPi (TIAll (TApp (lift 2 0 (lift 2 0 R)) (TVar 1))
                   (TMuI (lift 2 0 (lift 2 0 R)))
                   (TVar 0) (lift 2 0 (lift 2 0 P)))
        (TApp (lift 3 0 (lift 2 0 P))
              (TPair (TVar 2) (TIn (TVar 1)))))).
Proof.
  intros. cbn [lift].
  repeat rewrite lift_fuse_same_pres.
  repeat rewrite lift_lift_one_zero.
  repeat rewrite lift_lift_two_zero.
  repeat rewrite lift_lift_zero_comm.
  cbn [Nat.ltb Nat.add].
  repeat rewrite lift_var_below_pres by lia.
  assert (EP : lift 2 3 (lift 3 0 P) = lift 3 0 (lift 2 0 P)).
  { replace 3 with (3 + 0) at 1 by lia. apply lift_lift_zero_comm. }
  rewrite EP.
  reflexivity.
Qed.

Lemma lift_predicate_type_two_pres : forall IT X,
  lift 1 0 (lift 1 0
    (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0))) =
  TPi (TSigma (lift 2 0 IT)
    (TApp (lift 1 0 (lift 2 0 X)) (TVar 0))) (TSort 0).
Proof.
  intros. cbn [lift]. repeat rewrite lift_fuse_same_pres.
  repeat rewrite lift_lift_one_zero. repeat rewrite lift_lift_two_zero.
  repeat rewrite lift_lift_zero_comm. cbn [lift]. reflexivity.
Qed.

Lemma lift_idesc_family_type_two_pres : forall IT,
  lift 1 0 (lift 1 0 (TPi IT (TIDesc (lift 1 0 IT)))) =
  TPi (lift 2 0 IT) (TIDesc (lift 1 0 (lift 2 0 IT))).
Proof.
  intros. cbn [lift]. repeat rewrite lift_fuse_same_pres.
  repeat rewrite lift_lift_one_zero. repeat rewrite lift_lift_two_zero.
  repeat rewrite lift_lift_zero_comm. cbn [lift]. reflexivity.
Qed.

Theorem preservation_integrated : forall G t u A,
  check G t A -> step t u -> check G u A.
Proof.
  intros G t u A Hty Hstep.
  exact (preservation_full_draft
    check_subst0_pres sub_pi_application_pres_closed conv_subst_pres
    checked_pair_fst_pres checked_pair_snd_pres_closed
    sub_idesc_target_conv_pres sub_enum_cons_tail_conv_pres
    check_weaken0_pres subst_lift_zero _tmp_commute.lift_zero_id_local
    conv_lift_pres subst_eta_cancel_pres subst_lift_two_pres
    subst_lift_three_pres lift_lift_one_zero_pres
    lift_lift_two_zero_pres lift_fuse_two_pres lift_two_gap1_pres
    lift_fuse_three_pres lift_ind_step_type_two_pres
    lift_predicate_type_two_pres lift_idesc_family_type_two_pres
    mui_in_payload_same_pres mus_in_pair_payload_same_pres
    G t A Hty u Hstep).
Qed.

Theorem preservation : forall G t u A,
  check G t A -> step t u -> check G u A.
Proof. exact preservation_integrated. Qed.

Print Assumptions preservation.
