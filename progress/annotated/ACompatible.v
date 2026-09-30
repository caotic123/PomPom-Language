(* Preservation through every compatible context, including all annotations.
   A local change carries conversion and type preservation. Bounded formation
   search and one constructor tactic cover the complete annotated syntax. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AContexts annotated.AEta.
Require nameless.DBOperatorFormations.
Import ListNotations.
Module RO := nameless.DBOperatorFormations.
Module RCore := nameless.DBCore.

Definition local_change t u := conversion t u /\
  forall Gamma T, typing Gamma t T -> typing Gamma u T.

Ltac type_conversion :=
  first [assumption | apply RCore.cv_refl | apply RCore.cv_sym; assumption |
    apply RW.conversion_lift; type_conversion |
    apply RS.conversion_subst; type_conversion |
    apply nameless.DBBeta.substitution_argument_conversion; type_conversion |
    apply RCore.cv_compatible; constructor; type_conversion].
Ltac macro_conversion :=
  unfold Raw.arrow, Raw.product, Raw.Def, Raw.Family, Raw.total, Raw.motive,
    Raw.recursive_method, Raw.close_motive, Raw.close_case_method,
    Raw.close_ind_method, Raw.mu_ind_method, Raw.diagonal_motive,
    Raw.payload, Raw.carrier, Raw.CloseAt, Raw.MuAt;
  type_conversion.

Ltac raw_context :=
  match goal with
  | H : RT.typing (?old :: ?g) ?tm ?ty |- RT.typing (?new :: ?g) ?tm _ =>
    eapply nameless.DBContexts.context_conversion with (T := ty);
      [eassumption|eassumption|macro_conversion|exact H]
  end.
Ltac raw_substitution :=
  match goal with
  | HB : RT.typing (?dom :: ?g) ?cod (Raw.TSort ?k),
    Ha : RT.typing ?g ?a ?dom |- RT.typing ?g (Raw.subst ?a 0 ?cod) _ =>
    exact (RS.substitution _ _ _ _ _ HB Ha)
  end.
Create HintDb annotation_forms0.
Create HintDb annotation_forms1.
Create HintDb annotation_forms2.
Create HintDb annotation_forms3.
#[local] Hint Resolve RT.ty_sort RT.ty_pi RT.ty_sigma RT.ty_unitT RT.ty_uid
    RT.ty_enumu RT.ty_enumt RT.ty_conse RT.ty_idesc RT.ty_interp RT.ty_iall
    RT.ty_epi RO.def_formation DT.family_formation DT.mu_at_formation
    DT.close_at_formation DT.total_formation nameless.DBInductionBeta.motive_formation
    nameless.DBInductionBeta.payload_formation DT.smart_mui DT.smart_close
    nameless.DBInductionBeta.def_application RO.recursive_method_formation
    RO.mu_method_formation RO.close_method_formation RO.close_motive_formation
    RO.close_case_method_formation RO.sort_codomain_formation
    nameless.DBConstructorGeneration.arrow_formation DT.regular_application
    RT.wf_cons RW.typing_context RW.weakening :
  annotation_forms0 annotation_forms1 annotation_forms2 annotation_forms3.
#[local] Hint Extern 3 (RT.typing _ _ _) => solve [raw_context | raw_substitution] :
  annotation_forms0 annotation_forms1 annotation_forms2 annotation_forms3.
Ltac raw_cast solver :=
  match goal with
  | HH : RT.typing ?g ?tm ?src |- RT.typing ?g ?tm ?dst =>
    let HC := fresh in assert (HC : RCore.conv src dst) by macro_conversion;
    eapply RT.ty_conv; [exact HH|solve [solver]|exact HC]
  end.
#[local] Hint Extern 8 (RT.typing _ _ _) => raw_cast ltac:(eauto 7 with annotation_forms0) : annotation_forms1.
#[local] Hint Extern 8 (RT.typing _ _ _) => raw_cast ltac:(eauto 7 with annotation_forms1) : annotation_forms2.
#[local] Hint Extern 8 (RT.typing _ _ _) => raw_cast ltac:(eauto 7 with annotation_forms2) : annotation_forms3.
Ltac raw_form := eauto 7 with annotation_forms3.
Ltac repair_type :=
  match goal with
  | H : typing ?G ?t ?S |- typing ?G ?t ?T =>
    let HC := fresh in assert (HC : RCore.conv S T) by macro_conversion;
    eapply ty_conv; [exact H|solve [raw_form]|exact HC]
  end.
Ltac repair_context :=
  match goal with
  | H : typing (?A :: ?G) ?t ?oldtype |- typing (?B :: ?G) ?t _ =>
    eapply context_conversion with (T := oldtype); [solve [raw_form]|solve [raw_form]|macro_conversion|exact H]
  end.
Ltac premise := first [eassumption | solve [repair_context] | solve [repair_type]].

Ltac build := match goal with
  | |- typing _ (TVar _) _ => eapply ty_var
  | |- typing _ (TSort _) _ => eapply ty_sort
  | |- typing _ (TPi _ _) _ => eapply ty_pi
  | |- typing _ (TLam _ _ _) _ => eapply ty_lam
  | |- typing _ (TApp _ _ _ _) _ => eapply ty_app
  | |- typing _ (TSigma _ _) _ => eapply ty_sigma
  | |- typing _ (TPair _ _ _ _) _ => eapply ty_pair
  | |- typing _ (TFst _ _ _) _ => eapply ty_fst
  | |- typing _ (TSnd _ _ _) _ => eapply ty_snd
  | |- typing _ (TUnitT) _ => eapply ty_unitT
  | |- typing _ (TUnit) _ => eapply ty_unit
  | |- typing _ (TUId) _ => eapply ty_uid
  | |- typing _ (TTag _) _ => eapply ty_tag
  | |- typing _ (TEnumU) _ => eapply ty_enumu
  | |- typing _ (TNilE) _ => eapply ty_nile
  | |- typing _ (TConsE _ _) _ => eapply ty_conse
  | |- typing _ (TEnumT _) _ => eapply ty_enumt
  | |- typing _ (TEZero _ _) _ => eapply ty_zero
  | |- typing _ (TESucc _ _ _) _ => eapply ty_succ
  | |- typing _ (TEPi _ _ _) _ => eapply ty_epi
  | |- typing _ (TSwitch _ _ _ _ _) _ => eapply ty_switch
  | |- typing _ (TIDesc _) _ => eapply ty_idesc
  | |- typing _ (TIVar _ _) _ => eapply ty_ivar
  | |- typing _ (TI1 _) _ => eapply ty_i1
  | |- typing _ (TIBot _) _ => eapply ty_ibot
  | |- typing _ (TIProd _ _ _) _ => eapply ty_iprod
  | |- typing _ (TIPi _ _ _) _ => eapply ty_ipi
  | |- typing _ (TISig _ _ _) _ => eapply ty_isig
  | |- typing _ (TIChoice _ _ _) _ => eapply ty_ichoice
  | |- typing _ (TInterp _ _ _) _ => eapply ty_interp
  | |- typing _ (TMuI _ _) _ => eapply ty_mui
  | |- typing _ (TInMu _ _ _ _) _ => eapply ty_in_mui
  | |- typing _ (TInClose _ _ _ _ _) _ => eapply ty_in_close
  | |- typing _ (TInd _ _ _ _ _ _) _ => eapply ty_ind
  | |- typing _ (TIAll _ _ _ _ _) _ => eapply ty_iall
  | |- typing _ (THyps _ _ _ _ _ _) _ => eapply ty_hyps
  | |- typing _ (TClose _ _ _) _ => eapply ty_close
  | |- typing _ (TCloseCase _ _ _ _ _ _ _ _) _ => eapply ty_close_case
  | |- typing _ (TCloseInd _ _ _ _ _ _ _) _ => eapply ty_close_ind
  end; premise.

Theorem compatible_preservation : forall Gamma t T,
  typing Gamma t T -> forall u, compatible local_change t u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros u Hcp.
  all: try solve [eapply ty_conv; [eapply IHtyping; exact Hcp|eassumption|eassumption]].
  all: try solve [eapply ty_cumul; [eapply IHtyping; exact Hcp|eassumption]].
  all: try solve [eapply ty_cumul_fun; [eapply IHtyping; exact Hcp|eassumption|eassumption|eassumption|eassumption]].
  all: match goal with HC : compatible _ ?src ?dst |- typing ?g ?out ?typ =>
    let HF := fresh "Hformed" in
    assert (HF : RT.type_wf g typ) by
      (eapply type_correctness with (t:=src); eauto 3 using typing)
  end.
  all: inversion Hcp; subst; clear Hcp.
  all: match goal with HC : local_change ?s ?s' |- _ =>
    destruct HC as [Hconv Hchange]; unfold conversion in Hconv;
    repeat match goal with HT : typing ?G s ?A |- _ =>
      tryif (match goal with _ : typing G s' A |- _ => idtac end) then fail else
      let Hnew := fresh "Hnew" in pose proof (Hchange G A HT) as Hnew
    end
  end.
  all: repeat match goal with HT : typing ?G ?t ?A |- _ =>
    tryif (match goal with _ : RT.typing G (erase t) A |- _ => idtac end) then fail else
    let Hraw := fresh "Hraw" in pose proof (typing_erasure _ _ _ HT) as Hraw
  end.
  all: match goal with HF : RT.type_wf _ _ |- _ =>
    let level := fresh "level" in let formed := fresh "formed" in
    destruct HF as [level formed]
  end.
  all: try solve [build].
  all: try solve [eapply ty_conv; [build|
    eassumption|
    macro_conversion]].
Qed.

Print Assumptions compatible_preservation.
