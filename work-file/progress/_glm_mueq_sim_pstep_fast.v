(* GLM worker 4 — mueq simulation infrastructure, part 3: parallel steps.    *)
(*                                                                          *)
(* Simulation of pstep/pbranches along mueq/mubeq — the named mutual        *)
(* squares:                                                                 *)
(*                                                                          *)
(*   pstep t u  and  mueq t t'   =>   exists u', pstep t' u' /\ mueq u u'    *)
(*   pbranches bs bs' and mubeq bs bs''                                      *)
(*     =>  exists bs''', pbranches bs'' bs''' /\ mubeq bs' bs'''            *)
(*                                                                          *)
(* One mutual induction over pstep/pbranches; the mueq side is inverted per *)
(* case (mueq is shape-directed except for the opaque [me_muapp] class,     *)
(* which only arises at [ps_app] and is closed via [pstep_conv] +           *)
(* [cv_trans]).  Root contractions that substitute need the conditional     *)
(* premise [conv_subst_compatible] (part 2); lifting needs nothing (part 1  *)
(* discharged it with [conv_lift_glm]).  [ps_case_red] uses the position    *)
(* rigidity lemmas (_glm_mueq_pos) and the nth transport for mubeq          *)
(* (_glm_mubeq_nth).  No simulation premise is a global axiom.              *)

Require Import Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations TypeRules.
Require Import _luna_mueq _luna_mueq_equiv.
Require Import _glm_mueq_pos _glm_mubeq_nth.
Require Import _glm_mueq_sim_lift _glm_mueq_sim_subst.

(* ------------------------------------------------------------------ *)
(*  Tactics                                                            *)
(* ------------------------------------------------------------------ *)

(* Consume one induction hypothesis [IH : forall t', mueq x t' -> ...]
   against the witness [Hm : mueq x y]. *)
Ltac mstep IH Hm :=
  let U := fresh "u" in
  let HS := fresh "Hst" in
  let HM := fresh "Hmq" in
  destruct (IH _ Hm) as [U [HS HM]].

Ltac sim_use_ihs :=
  repeat match goal with
  | IH : forall t' : term, mueq ?x t' -> exists u' : term, _ |- _ =>
    match goal with
    | Hm : mueq x ?y |- _ => mstep IH Hm
    end
  end.

(* Recursive closer for mueq-shaped goals: context assumptions, lifting
   (part 1), or a congruence constructor with recursive subgoals.  The
   final match guards recursion to mueq goals only. *)
Ltac me_deep :=
  solve [ eassumption
        | apply mueq_lift_glm; eassumption
        | match goal with |- mueq _ _ => constructor; me_deep end ].

Ltac sim_struct :=
  sim_use_ihs; eexists; split;
    [ solve [ econstructor; eassumption ]
    | me_deep ].

(* The case's own mueq premises ([me_*] derivation arguments) are dead
   weight once the induction hypotheses are at hand, and they would be
   re-consumed forever by [sim_use_ihs] (they precede the inversion's
   witnesses in the context).  Clear them before inverting. *)
Ltac sim_clear_premises :=
  repeat match goal with
  | IH : forall t' : term, mueq ?x t' -> _ |- _ =>
    match goal with
    | H : mueq x _ |- _ => clear H
    end
  end.

Ltac sim_inv_mueq :=
  match goal with
  | Hm : mueq _ _ |- _ => inversion Hm; subst; clear Hm
  end.

(* ------------------------------------------------------------------ *)
(*  Root handlers                                                      *)
(* ------------------------------------------------------------------ *)

(* ps_beta. *)
Ltac sim_beta :=
  match goal with
  | Hm : mueq (TApp (TLam _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TLam _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_beta; eassumption
        | match goal with
          | Hsub : conv_subst_compatible |- _ =>
            eapply (mueq_subst_glm Hsub); eassumption
          end ]
    end
  end.

(* ps_app: the me_app branch is structural; the me_muapp branch uses the
   opaque conv premise, pstep_conv, and cv_trans. *)
Ltac sim_app_muapp :=
  match goal with
  | Hc2 : conv (TApp (TMuS ?S1) ?i1) (TApp (TMuS ?S2) ?i2) |- _ =>
    match goal with
    | Hf : pstep (TMuS S1) _ |- _ =>
      inversion Hf; subst;
      match goal with
      | Hs : pstep S1 ?S1p, Hsa : pstep i1 ?a1 |- _ =>
        exists (TApp (TMuS S2) i2); split;
          [ apply pstep_refl
          | apply (me_muapp S1p S2 a1 i2
              (cv_trans (TApp (TMuS S1p) a1) (TApp (TMuS S1) i1)
                        (TApp (TMuS S2) i2)
                (cv_sym (TApp (TMuS S1) i1) (TApp (TMuS S1p) a1)
                  (cv_app (TMuS S1) (TMuS S1p) i1 a1
                    (cv_mus S1 S1p (pstep_conv S1 S1p Hs))
                    (pstep_conv i1 a1 Hsa)))
                Hc2)) ]
      end
    end
  end.

Ltac sim_app :=
  match goal with
  | Hm : mueq (TApp _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    try (sim_use_ihs; eexists; split;
           solve [ econstructor; eassumption | me_deep ]);
    try sim_app_muapp
  end.

Ltac sim_fst_pair :=
  match goal with
  | Hm : mueq (TFst (TPair _ _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_fst_pair; eassumption | me_deep ]
    end
  end.

Ltac sim_snd_pair :=
  match goal with
  | Hm : mueq (TSnd (TPair _ _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_snd_pair; eassumption | me_deep ]
    end
  end.

Ltac sim_epi_nil :=
  match goal with
  | Hm : mueq (TEPi TNilE _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq TNilE _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_epi_nil; eassumption | constructor ]
    end
  end.

Ltac sim_epi_cons :=
  match goal with
  | Hm : mueq (TEPi (TConsE _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TConsE _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_epi_cons; eassumption
        | constructor; me_deep ]
    end
  end.

Ltac sim_switch_zero :=
  match goal with
  | Hm : mueq (TSwitch (TConsE _ _) _ (TPair _ _) TEZero) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TConsE _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq TEZero _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_switch_zero; eassumption | me_deep ]
  end.

Ltac sim_switch_succ :=
  match goal with
  | Hm : mueq (TSwitch (TConsE _ _) _ (TPair _ _) (TESucc _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TConsE _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TESucc _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_switch_succ; eassumption
      | constructor; me_deep ]
  end.

Ltac sim_interp_var :=
  match goal with
  | Hm : mueq (TInterp (TIVar _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIVar _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_var; eassumption | apply me_app; me_deep ]
    end
  end.

Ltac sim_interp_one :=
  match goal with
  | Hm : mueq (TInterp TI1 _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq TI1 _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_one; eassumption | constructor ]
    end
  end.

Ltac sim_interp_prod :=
  match goal with
  | Hm : mueq (TInterp (TIProd _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIProd _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_prod; eassumption | constructor; me_deep ]
    end
  end.

Ltac sim_interp_pi :=
  match goal with
  | Hm : mueq (TInterp (TIPi _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIPi _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_pi; eassumption | constructor; me_deep ]
    end
  end.

Ltac sim_interp_sig :=
  match goal with
  | Hm : mueq (TInterp (TISig _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TISig _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_sig; eassumption | constructor; me_deep ]
    end
  end.

Ltac sim_interp_choice :=
  match goal with
  | Hm : mueq (TInterp (TIChoice _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIChoice _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_interp_choice; eassumption | constructor; me_deep ]
    end
  end.

Ltac sim_iall_var :=
  match goal with
  | Hm : mueq (TIAll (TIVar _) _ _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIVar _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_iall_var; eassumption
        | apply me_app; apply me_pair; me_deep ]
    end
  end.

Ltac sim_iall_one :=
  match goal with
  | Hm : mueq (TIAll TI1 _ TUnit _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq TI1 _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq TUnit _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_iall_one; eassumption | constructor ]
  end.

Ltac sim_iall_prod :=
  match goal with
  | Hm : mueq (TIAll (TIProd _ _) _ (TPair _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIProd _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_iall_prod; eassumption | constructor; me_deep ]
  end.

Ltac sim_iall_pi :=
  match goal with
  | Hm : mueq (TIAll (TIPi _ _) _ _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIPi _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_iall_pi; eassumption | constructor; me_deep ]
    end
  end.

Ltac sim_iall_sig :=
  match goal with
  | Hm : mueq (TIAll (TISig _ _) _ (TPair _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TISig _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_iall_sig; eassumption | apply me_iall; me_deep ]
  end.

Ltac sim_iall_choice :=
  match goal with
  | Hm : mueq (TIAll (TIChoice _ _) _ (TPair _ _) _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIChoice _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_iall_choice; eassumption | apply me_iall; me_deep ]
  end.

Ltac sim_hyps_var :=
  match goal with
  | Hm : mueq (THyps (TIVar _) _ _ _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIVar _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_hyps_var; eassumption
        | apply me_app; apply me_app; me_deep ]
    end
  end.

Ltac sim_hyps_one :=
  match goal with
  | Hm : mueq (THyps TI1 _ _ _ TUnit) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq TI1 _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq TUnit _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_hyps_one; eassumption | constructor ]
  end.

Ltac sim_hyps_prod :=
  match goal with
  | Hm : mueq (THyps (TIProd _ _) _ _ _ (TPair _ _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIProd _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_hyps_prod; eassumption | apply me_pair; me_deep ]
  end.

Ltac sim_hyps_pi :=
  match goal with
  | Hm : mueq (THyps (TIPi _ _) _ _ _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIPi _ _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_hyps_pi; eassumption
        | apply me_lam; apply me_hyps; me_deep ]
    end
  end.

Ltac sim_hyps_sig :=
  match goal with
  | Hm : mueq (THyps (TISig _ _) _ _ _ (TPair _ _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TISig _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_hyps_sig; eassumption | apply me_hyps; me_deep ]
  end.

Ltac sim_hyps_choice :=
  match goal with
  | Hm : mueq (THyps (TIChoice _ _) _ _ _ (TPair _ _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIChoice _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    sim_use_ihs; eexists; split;
      [ apply ps_hyps_choice; eassumption | apply me_hyps; me_deep ]
  end.

Ltac sim_ind_red :=
  match goal with
  | Hm : mueq (TInd _ _ _ _ (TIn _)) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIn _) _ |- _ =>
      inversion H1; subst; clear H1;
      sim_use_ihs; eexists; split;
        [ apply ps_ind_red; eassumption
        | apply me_app; apply me_app; apply me_app; apply me_app; me_deep ]
    end
  end.

(* ps_case (structural): uses the pbranches induction hypothesis. *)
Ltac sim_case :=
  match goal with
  | Hm : mueq (TCase _ _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    sim_use_ihs;
    match goal with
    | IHb : forall bs'' : list (term * term), mubeq ?bs bs'' -> _ |- _ =>
      match goal with
      | Hmb : mubeq bs ?bs0 |- _ =>
        let bs3 := fresh "bs" in
        let Hpb := fresh "Hpb" in
        let Hmb3 := fresh "Hmb" in
        destruct (IHb _ Hmb) as [bs3 [Hpb Hmb3]]
      end
    end;
    eexists; split;
      [ apply ps_case; eassumption
      | apply me_case; eassumption ]
  end.

(* ps_case_red: first-match contraction; needs position rigidity, the
   mubeq nth transport, and mueq substitution for the conclusion. *)
Ltac sim_case_red :=
  match goal with
  | Hm : mueq (TCase (TIn (TPair _ _)) _ _) _ |- _ =>
    inversion Hm; subst; clear Hm;
    match goal with
    | H1 : mueq (TIn _) _ |- _ => inversion H1; subst; clear H1
    end;
    match goal with
    | H1 : mueq (TPair _ _) _ |- _ => inversion H1; subst; clear H1
    end;
    (* the matched enum label is rigid: a0 = a *)
    match goal with
    | Hea : enum_pos ?a ?n |- _ =>
      match goal with
      | Haa : mueq a ?a0 |- _ =>
        assert (Ha0 : a0 = a) by
          (apply (mueq_enum_pos_right_glm a a0 n Hea Haa)); subst a0
      end
    end;
    (* transport the matched branch to the converted branch list *)
    match goal with
    | Hnth : nth_error ?bs ?k = Some (?c, ?b) |- _ =>
      match goal with
      | Hmb : mubeq bs ?bs0 |- _ =>
        destruct (mubeq_nth_error_fwd _ _ Hmb k c b Hnth)
          as [c0 [b0 [Hnth0 [Hcc0 Hbb0]]]];
        match goal with
        | Hec : enum_pos c ?n |- _ =>
          match goal with
          | Hcc0 : mueq c c0 |- _ =>
            assert (Hc0 : c0 = c) by
              (apply (mueq_enum_pos_right_glm c c0 n Hec Hcc0)); subst c0
          end
        end
      end
    end;
    sim_use_ihs;
    eexists; split;
      [ match goal with
        | Hnth0 : nth_error ?BS ?K = Some (?C, ?B0),
          Hmb : mubeq ?BS2 ?BS02,
          Hd : forall (j0 : nat) (cj0 bj0 : term), _ |- _ =>
          apply ps_case_red with (k := K);
            [ exact Hnth0
            | assumption
            | assumption
            | intros j cj bj Hjk Hnthj;
              destruct (mubeq_nth_error_bwd _ _ Hmb j cj bj Hnthj)
                as [xj [yj [Hnthj0 [Hxj Hyj]]]];
              destruct (Hd j xj yj Hjk Hnthj0) as [nj [Henumj Hnej]];
              assert (Hcj : cj = xj) by
                (apply (mueq_enum_pos_right_glm xj cj nj Henumj Hxj));
              subst cj;
              exists nj; split; assumption
            | eassumption
            | eassumption ]
        end
      | match goal with
        | Hsub : conv_subst_compatible |- _ =>
          eapply (mueq_subst_glm Hsub); eassumption
        end ]
  end.

(* pbs_nil. *)
Ltac sim_pbs_nil :=
  match goal with
  | Hmb : mubeq [] _ |- _ =>
    inversion Hmb; subst; clear Hmb;
    exists []; split; constructor
  end.

(* pbs_cons. *)
Ltac sim_pbs_cons :=
  match goal with
  | Hmb : mubeq ((_, _) :: _) _ |- _ =>
    inversion Hmb; subst; clear Hmb;
    sim_use_ihs;
    match goal with
    | IHr : forall bs'' : list (term * term), mubeq ?rest bs'' -> _ |- _ =>
      match goal with
      | Hmt : mubeq rest ?rest0 |- _ =>
        destruct (IHr _ Hmt) as [? [? ?]]
      end
    end;
    eexists; split;
      [ apply pbs_cons; eassumption
      | apply mbe_cons; eassumption ]
  end.

(* ------------------------------------------------------------------ *)
(*  The mutual simulation                                              *)
(* ------------------------------------------------------------------ *)

Theorem pstep_mueq_sim_mut :
  conv_subst_compatible ->
  ((forall t u (H : pstep t u), forall t', mueq t t' ->
      exists u', pstep t' u' /\ mueq u u') /\
   (forall bs bs' (H : pbranches bs bs'), forall bs'', mubeq bs bs'' ->
      exists bs''', pbranches bs'' bs''' /\ mubeq bs' bs''')).
Proof.
  intros Hc.
  apply (pstep_pbranches_ind
    (fun (t u : term) (_ : pstep t u) =>
      forall t' : term, mueq t t' ->
        exists u' : term, pstep t' u' /\ mueq u u')
    (fun (bs bs' : list (term * term)) (_ : pbranches bs bs') =>
      forall bs'' : list (term * term), mubeq bs bs'' ->
        exists bs''' : list (term * term),
          pbranches bs'' bs''' /\ mubeq bs' bs''')).
  all: intros.
  all: (match goal with
        | Hm : mueq ?l _ |- _ => idtac "S1-START M" l
        | Hmb : mubeq ?l _ |- _ => idtac "S1-START MB" l
        end;
        try (sim_clear_premises; sim_inv_mueq; sim_struct);
        idtac "S1-OK").
Abort.
