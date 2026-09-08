Require Import Progress SignatureLemmas
 _luna_finish_erased_sigma_value _luna_finish_erased_enum_value
 _luna_finish_interp_pair_origin _parent_finish_cjoin_context.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
 Progress._work_cjoin Progress._work_cstep_invariants Progress._work_conv_whd_pos
 Progress.MuApplicationSort.

Definition bounded_progress_parent N := forall t T,
 tsize t <= N -> check [] t T -> value t \/ exists t', step t t'.
Definition erased_dead_step_parent N D := forall xs T X,
 tsize xs <= N -> check [] xs T ->
 cjoin(phi_erase T)(phi_erase(TInterp D X)) -> exists xs',step xs xs'.

Lemma interp_prod_join_parent : forall D X A B,eval D(TIProd A B)->
 cjoin(phi_erase(TInterp D X))
 (phi_erase(TSigma(TInterp A X)(lift 1 0(TInterp B X)))).
Proof.
 intros. apply conv_phi_cjoin. eapply cv_trans.
 - apply cv_interp; [apply conv_of_eval;exact H | apply cv_refl].
 - apply cv_step,st_interp_prod.
Qed.
Lemma interp_choice_join_parent : forall D X E F,eval D(TIChoice E F)->
 cjoin(phi_erase(TInterp D X))
 (phi_erase(TSigma(TEnumT E)(TInterp(TApp(lift 1 0 F)(TVar 0))(lift 1 0 X)))).
Proof.
 intros. apply conv_phi_cjoin. eapply cv_trans.
 - apply cv_interp; [apply conv_of_eval;exact H | apply cv_refl].
 - apply cv_step,st_interp_choice.
Qed.

Lemma against_nil_step_parent : forall N D E F,
 bounded_progress_parent N -> eval D(TIChoice E F) ->eval E TNilE ->
 erased_dead_step_parent N D.
Proof.
 intros N D E F HP HD HE xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_choice_join_parent D X E F HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_choice_origin a b T D X E F HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hza:tsize a<=N) by (cbn in Hsz;lia).
 destruct (HP a TA Hza HA) as [HVa | [a' Hstep]].
 - exfalso. eapply (erased_empty_check_value_luna [] a TA HA eq_refl HVa).
   eapply cjoin_trans; [exact HAJ |].
   change (cjoin(phi_erase(TEnumT E))(phi_erase(TEnumT TNilE))).
   apply conv_phi_cjoin,cv_enumt,conv_of_eval,HE.
 - exists(TPair a' b). apply st_pair1,Hstep.
Qed.

Lemma against_prod_left_step_parent : forall N D A B,
 bounded_progress_parent N -> eval D(TIProd A B) ->
 erased_dead_step_parent N A ->erased_dead_step_parent N D.
Proof.
 intros N D A B HP HD IH xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_prod_join_parent D X A B HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_prod_origin a b T D X A B HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hza:tsize a<=N) by (cbn in Hsz;lia).
 destruct (IH a TA X Hza HA HAJ) as [a' HS].
 exists(TPair a' b). apply st_pair1,HS.
Qed.
Lemma against_prod_right_step_parent : forall N D A B,
 bounded_progress_parent N -> eval D(TIProd A B) ->
 erased_dead_step_parent N B ->erased_dead_step_parent N D.
Proof.
 intros N D A B HP HD IH xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_prod_join_parent D X A B HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_prod_origin a b T D X A B HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hzb:tsize b<=N) by (cbn in Hsz;lia).
 destruct (IH b TB X Hzb HB HBJ) as [b' HS].
 exists(TPair a b'). apply st_pair2,HS.
Qed.

Definition erased_choice_step_parent N E F := forall a b TA TB X,
 tsize(TPair a b)<=N ->check [] a TA ->check [] b TB ->
 cjoin(phi_erase TA)(phi_erase(TEnumT E)) ->
 cjoin(phi_erase TB)(phi_erase(TInterp(TApp F a)X)) ->
 exists p,step(TPair a b)p.

Lemma erased_choice_step_transport_parent : forall N E F E' F',
 erased_choice_step_parent N E F ->
 cjoin(phi_erase E)(phi_erase E') ->cjoin(phi_erase F)(phi_erase F') ->
 erased_choice_step_parent N E' F'.
Proof.
 intros N E F E' F' HC HE HF a b TA TB X Hsz HA HB HJA HJB.
 apply(HC a b TA TB X Hsz HA HB).
 - eapply cjoin_trans;[exact HJA|]. apply cjoin_enumt_parent,cjoin_sym,HE.
 - eapply cjoin_trans;[exact HJB|].
   cbn[phi_erase]. apply cjoin_interp_parent;[|apply cjoin_refl].
   apply cjoin_app_parent;[apply cjoin_sym;exact HF|apply cjoin_refl].
Qed.

Lemma erased_choice_step_eval_transport_parent : forall N D E F,
 erased_choice_step_parent N E F ->eval D(TIChoice E F) ->
 forall E' F',eval D(TIChoice E' F')->erased_choice_step_parent N E' F'.
Proof.
 intros N D E F HC HD E' F' HD'.
 pose proof(conv_phi_cjoin _ _ (conv_of_common_eval _ _ _ HD HD')) as HJ.
 destruct(cjoin_ichoice_inv_parent _ _ _ _ HJ) as [HE HF].
 eapply erased_choice_step_transport_parent;eassumption.
Qed.

Lemma erased_choice_step_to_dead_parent : forall N D E F,
 bounded_progress_parent N ->eval D(TIChoice E F)->
 erased_choice_step_parent N E F ->erased_dead_step_parent N D.
Proof.
 intros N D E F HP HD HK xs T X Hsz HC HJ.
 destruct(HP xs T Hsz HC) as [HV|HS];[|exact HS].
 pose proof(cjoin_trans _ _ _ HJ(interp_choice_join_parent D X E F HD)) as HSigma.
 destruct(erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HSigma)
 as [a[b ->]].
 destruct(erased_pair_interp_choice_origin a b T D X E F HC HJ HD)
 as [TA[TB[HA[HB[HAJ HBJ]]]]].
 exact(HK a b TA TB X Hsz HA HB HAJ HBJ).
Qed.

Lemma erased_choice_nil_step_parent : forall N E F,
 bounded_progress_parent N ->eval E TNilE->erased_choice_step_parent N E F.
Proof.
 intros N E F HP HE a b TA TB X Hsz HA HB HJA HJB.
 assert(Hza:tsize a<=N) by(cbn in Hsz;lia).
 destruct(HP a TA Hza HA) as [HV|[a' HS]].
 - exfalso. eapply(erased_empty_check_value_luna [] a TA HA eq_refl HV).
   eapply cjoin_trans;[exact HJA|].
   change(cjoin(phi_erase(TEnumT E))(phi_erase(TEnumT TNilE))).
   apply conv_phi_cjoin,cv_enumt,conv_of_eval,HE.
 - exists(TPair a' b). apply st_pair1,HS.
Qed.

Lemma interp_prod_choice_clash_parent : forall D A B E F,
 eval D(TIProd A B)->eval D(TIChoice E F)->False.
Proof.
 intros. eapply no_cjoin_iprod_ichoice_parent.
 exact(conv_phi_cjoin _ _ (conv_of_common_eval _ _ _ H H0)).
Qed.

Lemma shifted_choice_beta_parent : forall F n,
 conv(TApp(TLam(TApp(lift 1 0 F)(TESucc(TVar 0))))n)
     (TApp F(TESucc n)).
Proof.
 intros F n.
 assert(Hsub:subst n 0(TApp(lift 1 0 F)(TESucc(TVar 0)))=TApp F(TESucc n)).
 { cbn[subst]. rewrite subst_lift_zero,Progress._tmp_commute.lift_zero_id_local.
   reflexivity. }
 rewrite <-Hsub. apply cv_step,st_beta.
Qed.
Lemma pair_step_succ_parent : forall a b p,step(TPair a b)p ->
 exists q,step(TPair(TESucc a)b)q.
Proof.
 intros a b p H;inversion H;subst.
 - eexists. apply st_pair1,st_esucc1;eassumption.
 - eexists. apply st_pair2;eassumption.
Qed.

Lemma erased_choice_cons_step_parent : forall N E F tg E',
 bounded_progress_parent N ->eval E(TConsE tg E') ->
 erased_dead_step_parent N(TApp F TEZero) ->
 erased_choice_step_parent N E' (TLam(TApp(lift 1 0 F)(TESucc(TVar 0)))) ->
 erased_choice_step_parent N E F.
Proof.
 intros N E F tg E' HP HE IH0 IHtail a b TA TB X Hsz HA HB HJA HJB.
 assert(Hza:tsize a<=N) by(cbn in Hsz;lia).
 destruct(HP a TA Hza HA) as [HVa|[a' HS]].
 2:{ exists(TPair a' b). apply st_pair1,HS. }
 destruct(erased_enum_check_value_origin_luna [] a TA HA eq_refl HVa
   (phi_erase E) HJA) as [[tg0[E0[-> HJE]]]|[n[tg0[E0[-> [HN HJE]]]]]].
 - assert(Hzb:tsize b<=N) by(cbn in Hsz;lia).
   destruct(IH0 b TB X Hzb HB HJB) as [b' HS].
   exists(TPair TEZero b'). apply st_pair2,HS.
 - pose proof(cjoin_reduce_right _ _ _ HJE(phi_erase_eval_csteps _ _ HE)) as HJJ.
   destruct(cjoin_conse_inv_parent _ _ _ _ HJJ) as [_ Htail].
   assert(Hzt:tsize(TPair n b)<=N) by(cbn in *;lia).
   assert(HJn:cjoin(phi_erase(TEnumT E0))(phi_erase(TEnumT E'))).
   { apply cjoin_enumt_parent,Htail. }
   assert(HJb:cjoin(phi_erase TB)
    (phi_erase(TInterp(TApp(TLam(TApp(lift 1 0 F)(TESucc(TVar 0))))n)X))).
   { eapply cjoin_trans;[exact HJB|].
     apply conv_phi_cjoin,cv_interp;[apply cv_sym,shifted_choice_beta_parent|apply cv_refl]. }
   destruct(IHtail n b (TEnumT E0) TB X Hzt HN HB HJn HJb) as [p HS].
   eapply pair_step_succ_parent;exact HS.
Qed.

Theorem desc_against_erased_step_mut_parent : forall N,
 bounded_progress_parent N ->forall D,desc_against D ->
 erased_dead_step_parent N D /\
 (forall E F,eval D(TIChoice E F)->erased_choice_step_parent N E F).
Proof.
 intros N HP D HD;induction HD.
 - assert(HC:erased_choice_step_parent N E T).
   { eapply erased_choice_nil_step_parent;eassumption. }
   split.
   + eapply erased_choice_step_to_dead_parent;eassumption.
   + eapply erased_choice_step_eval_transport_parent;eassumption.
 - destruct IHHD as [IH _]. split.
   + eapply against_prod_left_step_parent;eassumption.
   + intros E F HH. exfalso. eapply interp_prod_choice_clash_parent;eassumption.
 - destruct IHHD as [IH _]. split.
   + eapply against_prod_right_step_parent;eassumption.
   + intros E F HH. exfalso. eapply interp_prod_choice_clash_parent;eassumption.
 - destruct IHHD1 as [IH0 _]. destruct IHHD2 as [_ IHtail].
   assert(HC:erased_choice_step_parent N E T).
   { eapply erased_choice_cons_step_parent;[exact HP|exact H0|exact IH0|].
     apply IHtail,ev_refl. }
   split.
   + eapply erased_choice_step_to_dead_parent;eassumption.
   + eapply erased_choice_step_eval_transport_parent;eassumption.
Qed.
Theorem desc_against_erased_step_parent : forall N,
 bounded_progress_parent N ->forall D,desc_against D ->
 erased_dead_step_parent N D.
Proof. intros N HP D HD. exact(proj1(desc_against_erased_step_mut_parent N HP D HD)). Qed.
Print Assumptions desc_against_erased_step_parent.
