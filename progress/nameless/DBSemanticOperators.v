(* Semantic typing rules connecting the primitive operator theorems. *)
From Stdlib Require Import List Arith Lia.
Require Export nameless.DBSemanticCloseMethods.
Import ListNotations Full.

Lemma semantic_arrow_interp : forall n A B RA RB,
  calculus_interp n A RA -> calculus_interp n B RB ->
  calculus_interp n (arrow A B) (dependent_function RA (fun _ => RB)).
Proof.
  intros n A B RA RB HA HB; apply calculus_pi_interp; [exact HA|].
  intros a Ha; now rewrite subst_lift_zero.
Qed.
Lemma semantic_description_member : forall IT RI D,
  small_interp IT RI -> semantic_value D (TIDesc IT) -> small_code RI D.
Proof.
  intros IT RI D HI HD; eapply semantic_value_member; [exact HD|].
  apply (calculus_description_formation IT RI HI 1); lia.
Qed.
Lemma semantic_enum_member : forall E, semantic_value E TEnumU -> enumeration_computable E.
Proof. intros E HE; exact (semantic_value_member _ _ _ _ HE (calculus_enum_universe 0)). Qed.
Lemma semantic_description_function : forall IT RI A RA D,
  small_interp IT RI -> small_interp A RA -> semantic_value D (arrow A (TIDesc IT)) ->
  dependent_function RA (fun _ => small_code RI) D.
Proof.
  intros IT RI A RA D HI HA HD; eapply semantic_value_member; [exact HD|].
  apply semantic_arrow_interp with (n:=1); [now apply small_type_in_universe|now apply calculus_description_formation].
Qed.

Lemma semantic_interp : forall IT RI D X,
  small_interp IT RI -> semantic_value D (TIDesc IT) -> semantic_value X (Family IT) ->
  semantic_value (TInterp IT D X) (TSort 0).
Proof.
  intros IT RI D X HI HD HX.
  pose proof (semantic_description_member IT RI D HI HD) as HC.
  destruct (semantic_family IT RI X HI HX) as [HS HF].
  apply semantic_small_sort; eexists; eapply interpretation_computable;
    [exact (small_type_candidate _ _ HI)|exact HC|exact (type_interp_normalizing _ _ _ HI)|exact HS|exact HF].
Qed.
Lemma semantic_iall : forall IT RI D X xs P,
  small_interp IT RI -> semantic_value D (TIDesc IT) -> semantic_value X (Family IT) ->
  semantic_value xs (TInterp IT D X) -> semantic_value P (motive IT X) ->
  semantic_value (TIAll IT D X xs P) (TSort 0).
Proof.
  intros IT RI D X xs P HI HD HX Hxs HP.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_description_member IT RI D HI HD) as HC.
  pose proof (small_code_meaning RI CRI D HC) as HM.
  destruct (semantic_family IT RI X HI HX) as [HS HF].
  destruct (semantic_motive IT RI X _ P HI HF HP) as [HSP HQ].
  apply semantic_small_sort; eapply all_computable;
    [exact CRI|exact HC|exact HM|exact (type_interp_normalizing _ _ _ HI)|exact HS|exact HSP
    |exact (interpreted_family_stable _ _ _ HF)|exact HQ|].
  eapply small_semantic_member; [exact Hxs|].
  exact (semantic_interpretation_as IT RI D X _ _ HI HC HM HS HF).
Qed.
Lemma semantic_hyps : forall IT RI D X P h xs,
  small_interp IT RI -> semantic_value D (TIDesc IT) -> semantic_value X (Family IT) ->
  semantic_value P (motive IT X) -> semantic_value h (recursive_method IT X P) ->
  semantic_value xs (TInterp IT D X) -> semantic_value (THyps IT D X P h xs) (TIAll IT D X xs P).
Proof.
  intros IT RI D X P h xs HI HD HX HP Hh Hxs.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_description_member IT RI D HI HD) as HC.
  pose proof (small_code_meaning RI CRI D HC) as HM.
  destruct (semantic_family IT RI X HI HX) as [HS HF].
  destruct (semantic_motive IT RI X _ P HI HF HP) as [HSP HQ].
  pose proof (semantic_recursive_method IT RI X _ P h HI HF HQ Hh) as HH.
  pose proof (small_semantic_member _ _ _ Hxs (semantic_interpretation_as IT RI D X _ _ HI HC HM HS HF)) as Hpayload.
  pose proof (small_type_canonical _ (all_computable RI CRI D _ HC HM IT X _ P xs
    (type_interp_normalizing _ _ _ HI) HS HSP (interpreted_family_stable _ _ _ HF) HQ Hpayload)) as HA.
  apply small_semantic_value; eexists; split; [exact HA|].
  eapply hyps_computable; [exact CRI|exact HC|exact HM|exact (type_interp_normalizing _ _ _ HI)
    |exact HS|exact HSP|exact (interpreted_family_stable _ _ _ HF)|exact HQ|exact HH|exact Hpayload|exact HA].
Qed.
Lemma semantic_ind : forall IT RI D P st i x,
  small_interp IT RI -> semantic_value D (Def IT) ->
  semantic_value P (motive IT (TMuI IT D)) -> semantic_value st (mu_ind_method IT D P) ->
  semantic_value i IT -> semantic_value x (MuAt IT D i) ->
  semantic_value (TInd IT D P st i x) (TApp P (TPair i x)).
Proof.
  intros IT RI D P st i x HI HD HP Hst Hi Hx.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (computable_definition_meaning RI CRI D HDC) as HM.
  pose proof (semantic_mu_family IT RI D HI HDC) as HF.
  destruct (semantic_motive IT RI _ _ P HI HF HP) as [HSP HQ].
  pose proof (small_semantic_member _ _ _ Hi HI) as Hic.
  apply small_semantic_value.
  eapply ind_computable with (RI:=RI) (base_definition:=D) (F:=definition_meaning RI D);
    [exact CRI|exact HM| |exact (definition_is_interpreted RI CRI D HDC)|exact HQ
    |exact (semantic_mu_ind_method IT RI D P st HI HDC HSP HQ Hst)|exact Hic|].
  - constructor; [exact (type_interp_normalizing _ _ _ HI)|].
    constructor; [exact (proj1 HDC)|constructor; [exact HSP|]].
    constructor; [exact (proj1 (semantic_value_normalizing _ _ Hst))|constructor].
  - exact (small_semantic_member _ _ _ Hx (HF i Hic)).
Qed.
Lemma semantic_close_ind : forall IT RI G P st D i x,
  small_interp IT RI -> semantic_value G (Def IT) ->
  semantic_value P (close_motive IT G) -> semantic_value st (close_ind_method IT G P) ->
  semantic_value D (Def IT) -> semantic_value i IT -> semantic_value x (CloseAt IT D G i) ->
  semantic_value (TCloseInd IT G P st D i x) (TApp (TApp (TApp P D) i) x).
Proof.
  intros IT RI G P st D i x HI HG HP Hst HD Hi Hx.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (semantic_definition IT RI G HI HG) as HGC.
  pose proof (computable_definition_meaning RI CRI G HGC) as HM.
  destruct (semantic_close_motive IT RI G P HI HGC HP) as [HSP HQ].
  pose proof (small_semantic_member _ _ _ Hi HI) as Hic.
  apply small_semantic_value.
  eapply close_ind_computable with (RI:=RI) (base_definition:=G) (F:=definition_meaning RI G);
    [exact CRI|exact HM| |exact (definition_is_interpreted RI CRI G HGC)|exact HQ
    |exact (semantic_close_ind_method IT RI G P st HI HGC HQ Hst)|exact HDC|exact Hic|].
  - constructor; [exact (type_interp_normalizing _ _ _ HI)|].
    constructor; [exact (proj1 HGC)|constructor; [exact HSP|]].
    constructor; [exact (proj1 (semantic_value_normalizing _ _ Hst))|constructor].
  - exact (small_semantic_member _ _ _ Hx (semantic_close_family IT RI D G HI HDC HGC i Hic)).
Qed.

Print Assumptions semantic_interp.
Print Assumptions semantic_iall.
Print Assumptions semantic_hyps.
Print Assumptions semantic_ind.
Print Assumptions semantic_close_ind.
