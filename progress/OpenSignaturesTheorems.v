(* Metatheory for the revised calculus. No conjectures remain: the two
   coherence statements are proved through the binary relational model in
   OpenSignaturesRel*.v. OpenSignaturesAudit prints the assumptions of every
   public claim. *)
From Stdlib Require Import List Arith String Lia FMapFacts.
Require Export OpenSignaturesExampleTyping OpenSignaturesSubtypingSoundness OpenSignaturesLabels OpenSignaturesObservers OpenSignaturesContexts OpenSignaturesCanonical OpenSignaturesDeadTyping OpenSignaturesNamedCanonical OpenSignaturesEndless OpenSignaturesContextInclusion OpenSignaturesClosedSubstitution OpenSignaturesPayloadInversion OpenSignaturesInductionBeta OpenSignaturesPreservation OpenSignaturesNormalization OpenSignaturesObservations.
Import ListNotations.
Require Export OpenSignaturesEtaPolymorphism.
Require OpenSignaturesRelElab.
Module VarMapFacts := FMapFacts.WFacts(VarMap).

(* Context validity follows directly from the core typing rules.
   See PROOF_START.md for the proof approach and acceptance check.
   No later conjectures are used. *)
Theorem context_validity :
  forall Gamma t A, typing Gamma t A -> wf Gamma.
Proof.
  intros Gamma t A Htyping.
  induction Htyping; assumption.
Qed.

(* The original attempts remain in the archive. Typed encoding and reflection
   now supply axiom-free structural rules and type correctness. *)
Theorem weakening :
  forall Gamma x t A B k,
    fresh_in Gamma x ->
    typing Gamma t A -> typing Gamma B (TSort k) ->
    typing (extend Gamma x B) t A.
Proof. exact named_weakening. Qed.
Theorem type_correctness :
  forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Proof. exact named_type_correctness. Qed.

(* Stable binding IDs: context extension leaves both t and A unchanged. *)
Theorem substitution :
  forall Gamma x A t B u,
    fresh_in Gamma x ->
    typing (extend Gamma x A) t B -> typing Gamma u A ->
    typing Gamma (subst u x t) (subst u x B).
Proof. exact named_substitution. Qed.
Theorem conversion_substitution :
  forall t u s k,
    conv t u -> conv (subst s k t) (subst s k u).
Proof.
  intros t u s k H.
  eapply cv_trans with (u := TApp (TLam k t) s).
  - apply cv_sym, cv_step, st_root. reflexivity.
  - eapply cv_trans with (u := TApp (TLam k u) s).
    + apply cv_compatible, cp_TApp; [|apply cv_refl].
      now apply cv_compatible, cp_TLam.
    + apply cv_step, st_root. reflexivity.
Qed.

Theorem next_step_sound :
  forall t u, next_step t = Some u -> step t u.
Proof.
  induction t; intros u H; cbn [next_step] in H;
    destruct (root_step _) eqn:Hr;
    try solve [inversion H; subst; now apply st_root].
  all: repeat match type of H with
    | context [match next_step ?t with _ => _ end] =>
        destruct (next_step t) eqn:?
    end; try discriminate; inversion H; subst; eauto using step.
Qed.
Theorem run_sound :
  forall fuel t, eval t (run fuel t).
Proof.
  induction fuel; intro t; cbn [run]; [constructor|].
  destruct (next_step t) eqn:H; eauto using eval, next_step_sound.
Qed.
(* Refuted by full_preservation_refuted, without axioms. Keep the exact
   original proposition for reference, but do not assert a false axiom.
   The pre-refutation declaration is preserved in proof-archive. *)
Definition full_preservation_statement : Prop :=
  forall Gamma t u A,
    typing Gamma t A -> reduction t u -> typing Gamma u A.
Theorem preservation :
  forall Gamma t u A, typing Gamma t A -> step t u -> typing Gamma u A.
Proof. exact named_preservation. Qed.
Theorem preservation_eval :
  forall Gamma t u A, typing Gamma t A -> eval t u -> typing Gamma u A.
Proof.
  intros Gamma t u A Htyping Heval. revert Htyping.
  induction Heval; eauto using preservation.
Qed.
Theorem normalization :
  forall Gamma t A, typing Gamma t A ->
    Acc (fun u v => reduction v u) t.
Proof. exact named_full_normalization. Qed.
Theorem conversion_joinability :
  forall Gamma t u A,
    typing Gamma t A -> typing Gamma u A -> conv t u ->
    exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof. intros; now apply raw_conversion_joinability. Qed.
(* Named representatives join modulo alpha; alpha conversion itself is not
   a reduction step, so it does not introduce reflexive reduction loops. *)
Theorem confluence :
  forall Gamma t A u v,
    typing Gamma t A -> reduces t u -> reduces t v ->
    exists w w', reduces u w /\ reduces v w' /\ alpha_equiv w w'.
Proof. intros; eapply raw_confluence; eassumption. Qed.
Theorem progress :
  forall t A, typing empty_ctx t A -> value t \/ exists u, step t u.
Proof. intros; eapply progress_from_conversion; eauto using conversion_joinability. Qed.

Theorem normalization_eval :
  forall t A, typing empty_ctx t A -> exists v, eval t v /\ value v.
Proof.
  intros t A Hty.
  destruct (accessible_run t (normalization _ _ _ Hty)) as [fuel Hnone].
  exists (run fuel t). split; [apply run_sound|].
  assert (Htyped : typing empty_ctx (run fuel t) A)
    by (eapply preservation_eval; [exact Hty|apply run_sound]).
  destruct (progress _ _ Htyped) as [Hv|[u Hu]]; [exact Hv|].
  destruct (step_has_next _ _ Hu) as [v Hv]. congruence.
Qed.

Theorem consistency :
  forall t, ~ typing empty_ctx t Bot.
Proof.
  intros t Hty. destruct (normalization_eval _ _ Hty) as [v [He Hv]].
  eapply (bottom_no_value conversion_joinability); [|exact Hv].
  eapply preservation_eval; eassumption.
Qed.

Theorem canonical_forms_close :
  forall IT F G i v,
    typing empty_ctx v (CloseAt IT F G i) -> value v ->
    exists xs, v = TIn xs /\ typing empty_ctx xs (payload IT F G i).
Proof.
  intros IT F G i v Ht Hv.
  destruct (close_value_shape _ _ _ _ _ _ Ht Hv) as [xs ->].
  exists xs; split; [reflexivity|now apply named_close_payload].
Qed.
Theorem canonical_forms_named :
  forall IT F G i t rs,
    typing empty_ctx t (CloseAt IT F G i) ->
    row_view empty_ctx IT (TApp F i) rs ->
    exists name D n xs,
      nth_error rs n = Some (name,D) /\
      eval t (TIn (TPair (enum_position n) xs)) /\
      typing empty_ctx xs (TInterp IT D (carrier IT G)).
Proof. exact (canonical_named_from_rules weakening preservation normalization_eval). Qed.

Theorem abort_typing :
  forall Gamma k A z,
    typing Gamma A (TSort k) -> typing Gamma z Bot ->
    typing Gamma (abort k A z) A.
Proof. exact (abort_from_weakening weakening). Qed.
Theorem unroll_typing :
  forall Gamma IT F G i x,
    close_input Gamma IT F G i ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (unroll IT F G i x) (payload IT F G i).
Proof. exact (unroll_from_weakening weakening). Qed.
Theorem unroll_beta :
  forall IT F G i xs, eval (unroll IT F G i (TIn xs)) xs.
Proof.
  intros. eapply ev_step; [apply st_root; reflexivity|].
  eapply ev_step; [apply st_root; reflexivity|constructor].
Qed.
Theorem close_induction_preservation :
  forall Gamma IT G P st F i x A u,
    typing Gamma (TCloseInd IT G P st F i x) A ->
    root_step (TCloseInd IT G P st F i x) = Some u ->
    typing Gamma u A.
Proof. exact named_close_ind_preservation. Qed.

Theorem row_code_typing :
  forall Gamma IT rs,
    row_input Gamma IT rs ->
    typing Gamma (row_code IT rs) (TIDesc IT).
Proof. exact (row_code_from_weakening weakening). Qed.
Theorem signature_typing :
  forall Gamma x IT rs,
    fresh_in Gamma x ->
    typing Gamma IT (TSort 0) ->
    row_input (extend Gamma x IT) IT rs ->
    typing Gamma (signature x IT rs) (Def IT).
Proof. exact (signature_from_weakening weakening). Qed.
Theorem row_position_identity :
  forall rs n name D,
    nth_error rs n = Some (name,D) ->
    label_at (row_enum rs) name (enum_position n).
Proof.
  induction rs as [|[s d] rs IH]; intros [|n] name D H;
    cbn in *; try discriminate.
  - inversion H; subst. constructor.
  - constructor. eauto.
Qed.
Theorem label_resolution_unique :
  forall Gamma rs name a b,
    NoDup (row_names rs) ->
    typing Gamma a (TEnumT (row_enum rs)) ->
    typing Gamma b (TEnumT (row_enum rs)) ->
    label_at (row_enum rs) name a -> label_at (row_enum rs) name b ->
    conv a b.
Proof. intros; eapply labels_unique; eassumption. Qed.

Theorem dead_sound :
  forall Gamma IT D X d,
    dead Gamma IT D X d ->
    typing Gamma d (arrow (TInterp IT D X) Bot).
Proof. exact (dead_from_rules weakening). Qed.
Theorem dead_close_uninhabited :
  forall IT F G i d,
    close_input empty_ctx IT F G i ->
    dead empty_ctx IT (TApp F i) (carrier IT G) d ->
    forall x, ~ typing empty_ctx x (CloseAt IT F G i).
Proof.
  intros IT F G i d Hinput Hdead x Hx.
  apply (consistency (TApp d (unroll IT F G i x))).
  eapply arrow_app with (A := payload IT F G i).
  - exact weakening.
  - apply payload_formation; [exact weakening|exact Hinput].
  - apply ty_enumt, ty_nile, wf_nil.
  - now apply dead_sound.
  - now apply unroll_typing.
Qed.
Theorem row_handlers_sound :
  forall Gamma IT X Y target source handlers,
    row_input Gamma IT source -> row_input Gamma IT target ->
    typing Gamma X (Family IT) -> typing Gamma Y (TSort 0) ->
    conv Y (TInterp IT (row_code IT target) X) ->
    row_handlers Gamma IT X Y target source handlers ->
    Forall2 (fun entry h =>
      typing Gamma h (arrow (TInterp IT (snd entry) X) Y)) source handlers.
Proof. exact (row_handlers_from_rules weakening dead_sound). Qed.
Theorem description_subtyping_sound :
  forall Gamma IT D D' X q,
    desc_sub Gamma IT D D' X q ->
    typing Gamma q (arrow (TInterp IT D X) (TInterp IT D' X)).
Proof. exact (description_subtyping_from_rules weakening dead_sound). Qed.
Theorem subtyping_sound :
  forall Gamma A B c, sub Gamma A B c -> typing Gamma c (arrow A B).
Proof. exact (subtyping_from_rules weakening type_correctness preservation dead_sound). Qed.
Theorem case_handlers_sound :
  forall Gamma k IT X Q bs rs handlers,
    row_input Gamma IT rs ->
    typing Gamma X (Family IT) -> typing Gamma Q (TSort k) ->
    elab_cases Gamma k IT X Q bs rs handlers ->
    typing Gamma (tuple handlers)
      (TEPi k (row_enum rs) (handler_motive IT rs X Q)).
Proof. exact (case_handlers_from_rules weakening dead_sound subtyping_sound). Qed.
Theorem synthesis_sound :
  forall Gamma e A t, elab_synth Gamma e A t -> typing Gamma t A.
Proof. exact (synthesis_from_rules weakening dead_sound subtyping_sound). Qed.
Theorem checking_sound :
  forall Gamma e A t, elab_check Gamma e A t -> typing Gamma t A.
Proof. exact (checking_from_rules weakening dead_sound subtyping_sound). Qed.

Theorem closing_substitution :
  forall Gamma env t A,
    closing Gamma env -> typing Gamma t A ->
    typing empty_ctx (instantiate env t) (instantiate env A).
Proof. exact named_closing_substitution. Qed.

Theorem close_roll_unroll_proof : forall Gamma IT F G i x,
  close_input Gamma IT F G i -> typing Gamma x (CloseAt IT F G i) ->
  observational_eq Gamma (CloseAt IT F G i) (TIn (unroll IT F G i x)) x.
Proof.
  intros Gamma IT F G i x Hinput Hx.
  assert (Hroll : typing Gamma (TIn (unroll IT F G i x)) (CloseAt IT F G i)).
  { destruct Hinput as [HIT [HF [HG Hi]]]. apply ty_in_close; try assumption.
    apply unroll_typing; [repeat split;assumption|exact Hx]. }
  split; [exact Hroll|]. split; [exact Hx|]. intros env Hclosing.
  pose proof (closing_substitution _ _ _ _ Hclosing Hx) as Hclosed.
  apply closed_observational_conversion.
  - eapply closing_substitution; eassumption.
  - exact Hclosed.
  - unfold CloseAt in Hclosed; rewrite instantiate_app, instantiate_close in Hclosed.
    destruct (normalization_eval _ _ Hclosed) as [v [He Hv]].
    pose proof (preservation_eval _ _ _ _ Hclosed He) as Hvt.
    destruct (close_value_shape _ _ _ _ _ _ Hvt Hv) as [xs ->].
    eapply cv_trans with (u:=TIn xs); [|apply cv_sym;now apply eval_conversion].
    unfold unroll. rewrite instantiate_in, instantiate_case.
    rewrite (instantiate_closed env identity) by reflexivity.
    apply eval_conversion, (eval_congruence TIn); [auto using st_TIn_x|].
    eapply eval_transitive.
    + apply (eval_congruence (fun t => TCloseCase 0 (instantiate env IT) (instantiate env F)
        (instantiate env G) (instantiate env i) _ identity t)); [auto using st_TCloseCase_x|exact He].
    + eapply ev_step; [apply st_root;reflexivity|].
      eapply ev_step; [apply st_root;reflexivity|constructor].
Qed.

(* No judgmental eta rule for close is assumed. *)
Theorem close_roll_unroll :
  forall Gamma IT F G i x,
    close_input Gamma IT F G i ->
    typing Gamma x (CloseAt IT F G i) ->
    observational_eq Gamma (CloseAt IT F G i)
      (TIn (unroll IT F G i x)) x.
Proof. exact close_roll_unroll_proof. Qed.
(* Proved through the binary relational model: OpenSignaturesRel*.v. *)
Theorem coercion_coherence :
  forall Gamma A B c d,
    sub Gamma A B c -> sub Gamma A B d ->
    observational_eq Gamma (arrow A B) c d.
Proof. exact OpenSignaturesRelCoercion.coercion_coherence_rel. Qed.
Theorem checking_coherence :
  forall Gamma e A t u,
    elab_check Gamma e A t -> elab_check Gamma e A u ->
    observational_eq Gamma A t u.
Proof. exact OpenSignaturesRelElab.checking_coherence_rel. Qed.

(* Symbolic example proofs use the shared weakening premise. The closed
   singleton elaboration below is independent of metatheory conjectures. *)
Theorem list_definitions_well_typed :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    typing Gamma (list_def A) (Def TUnitT) /\
    typing Gamma (nonempty_def A) (Def TUnitT) /\
    typing Gamma (tree_def A) (Def TUnitT).
Proof. exact (list_definitions_from_weakening weakening). Qed.
Theorem nil_typing :
  forall Gamma A,
    typing Gamma A (TSort 0) -> typing Gamma nil_value (list_type A).
Proof. exact (nil_from_weakening weakening). Qed.
Theorem cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (list_type A) ->
    typing Gamma (cons_value a xs) (list_type A).
Proof. exact (cons_from_weakening weakening). Qed.
Theorem nonempty_cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (list_type A) ->
    typing Gamma (nonempty_value a xs) (nonempty_type A).
Proof. exact (nonempty_cons_from_weakening weakening). Qed.
Theorem reused_tree_cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (tree_type A) ->
    typing Gamma (cons_value a xs) (tree_type A).
Proof. exact (tree_cons_from_weakening weakening). Qed.
Theorem nonempty_observers_typing :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    typing Gamma (head_term A) (arrow (nonempty_type A) A) /\
    typing Gamma (tail_term A) (arrow (nonempty_type A) (list_type A)).
Proof. exact (observers_from_weakening weakening). Qed.
Theorem nonempty_widening :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    sub Gamma (nonempty_type A) (list_type A) (to_list A).
Proof. exact (nonempty_widening_from_weakening weakening). Qed.
(* Small, bounded proof search for the concrete examples. Computation
   produces ordinary proofs through run_sound, alpha comparison, and the
   typing constructors; it does not assume any metatheory conjecture. *)
Create HintDb os_ground.

Lemma eval_conv : forall t u, eval t u -> conv t u.
Proof. intros t u H; induction H; eauto using conv. Qed.

Local Ltac os_compute :=
  match goal with
  | |- conv ?lhs ?rhs =>
    first [apply cv_refl | apply cv_alpha; vm_compute; reflexivity |
      let lhs' := eval vm_compute in (run 40 lhs) in
      let rhs' := eval vm_compute in (run 40 rhs) in
      eapply cv_trans with (u := lhs');
        [eapply eval_conv; exact (run_sound 40 lhs) |
         eapply cv_trans with (u := rhs');
           [first [apply cv_refl | apply cv_alpha; vm_compute; reflexivity | apply cv_compatible; constructor; os_compute] |
            apply cv_sym; eapply eval_conv; exact (run_sound 40 rhs)]]]
  end.

Local Ltac os_arg_type t Gamma :=
  lazymatch t with
  | TUnit => constr:(TUnitT)
  | TEZero => constr:(TEnumT (TConsE (TTag "") TNilE))
  | TESucc ?n =>
    let A := os_arg_type n Gamma in
    lazymatch A with TEnumT ?E => constr:(TEnumT (TConsE (TTag "") E)) end
  | TVar ?x =>
    let A := eval vm_compute in (lookup Gamma x) in
    lazymatch A with Some ?A => constr:(A) end
  end.

Local Ltac os_fresh Gamma tm ty :=
  let z := eval vm_compute in (fresh_id
    (vars tm ++ vars ty ++ map fst (VarMap.elements Gamma))) in
  constr:(z).

Local Ltac os_check fuel :=
  lazymatch fuel with
  | O => fail 1 "typing search exhausted"
  | S ?fuel =>
  first [solve [auto with os_ground] | lazymatch goal with
  | |- fresh_in _ _ => vm_compute; reflexivity
  | |- wf empty_ctx => apply wf_nil
  | |- wf (extend ?Gamma ?x ?A) =>
    eapply wf_cons; [os_check fuel | os_check fuel | os_check fuel]
  | |- typing ?Gamma ?tm ?ty =>
    let tm := eval cbv in tm in let ty := eval cbv in ty in
    change (typing Gamma tm ty);
    (tryif (match goal with _ : wf Gamma |- _ => idtac end) then idtac else
      let Hctx := fresh "Hctx" in assert (Hctx : wf Gamma) by os_check fuel);
    first [
      lazymatch tm with
      | TVar _ => apply ty_var; [os_check fuel | vm_compute; reflexivity]
      | TSort _ => apply ty_sort; os_check fuel
      | TUnitT =>
        lazymatch ty with TSort ?level => tryif is_evar level then unify level 0 else idtac end;
        apply ty_unitT; os_check fuel
      | TUnit => apply ty_unit; os_check fuel
      | TUId => apply ty_uid; os_check fuel
      | TTag _ => apply ty_tag; os_check fuel
      | TEnumU => apply ty_enumu; os_check fuel
      | TNilE => apply ty_nile; os_check fuel
      | TConsE _ _ => apply ty_conse; os_check fuel
      | TEnumT _ => apply ty_enumt; os_check fuel
      | TEZero => apply ty_zero; os_check fuel
      | TESucc _ => apply ty_succ; os_check fuel
      | TPi ?binder ?dom ?codom =>
        first [eapply ty_pi; os_check fuel | eapply ty_cumul; [eapply ty_pi; os_check fuel | cbn; lia] |
          let binder' := os_fresh Gamma tm ty in
          let codom' := eval vm_compute in (subst (TVar binder') binder codom) in
          eapply ty_alpha with (t := TPi binder' dom codom');
            [eapply ty_pi; os_check fuel | vm_compute; reflexivity]]
      | TSigma ?binder ?dom ?codom =>
        first [eapply ty_sigma; os_check fuel | eapply ty_cumul; [eapply ty_sigma; os_check fuel | cbn; lia] |
          let binder' := os_fresh Gamma tm ty in
          let codom' := eval vm_compute in (subst (TVar binder') binder codom) in
          eapply ty_alpha with (t := TSigma binder' dom codom');
            [eapply ty_sigma; os_check fuel | vm_compute; reflexivity]]
      | TPair _ _ => eapply ty_pair; os_check fuel
      | TIDesc _ => apply ty_idesc; os_check fuel
      | TIVar _ => apply ty_ivar; os_check fuel
      | TI1 => apply ty_i1; os_check fuel
      | TIBot => apply ty_ibot; os_check fuel
      | TIProd _ _ => apply ty_iprod; os_check fuel
      | TIPi _ _ => apply ty_ipi; os_check fuel
      | TISig _ _ => apply ty_isig; os_check fuel
      | TIChoice _ _ => apply ty_ichoice; os_check fuel
      | TInterp _ _ _ => apply ty_interp; os_check fuel
      | TClose _ _ _ => apply ty_close; os_check fuel
      | TIn _ => apply ty_in_close; os_check fuel
      | TEPi _ _ _ => apply ty_epi; os_check fuel
      | TLam ?binder ?body =>
        lazymatch ty with TPi ?tybinder ?dom ?codom =>
          first [unify binder tybinder; eapply ty_lam; os_check fuel |
            let body' := eval vm_compute in (subst (TVar tybinder) binder body) in
            eapply ty_alpha with (t := TLam tybinder body');
              [eapply ty_lam; os_check fuel | vm_compute; reflexivity] |
            let binder' := os_fresh Gamma tm ty in
            let codom' := eval vm_compute in (subst (TVar binder') tybinder codom) in
            let body' := eval vm_compute in (subst (TVar binder') binder body) in
            eapply ty_conv with (A := TPi binder' dom codom');
              [eapply ty_alpha with (t := TLam binder' body');
                 [eapply ty_lam; os_check fuel | vm_compute; reflexivity] |
               os_check fuel | apply cv_alpha; vm_compute; reflexivity]]
        end
      | TApp (TLam ?binder ?body) ?arg =>
        let argTy := lazymatch body with
        | TSwitch _ ?en _ _ (TVar binder) => constr:(TEnumT en)
        | _ => os_arg_type arg Gamma
        end in
        eapply ty_app with (x := binder) (A := argTy) (B := ty); os_check fuel
      | TApp (TClose ?indexTy ?defn ?recdefn) ?arg =>
        eapply ty_app with (x := fresh [indexTy]) (A := indexTy) (B := TSort 0);
          os_check fuel
      | TSwitch _ _ _ _ _ =>
        eapply ty_conv; [apply ty_switch; os_check fuel | os_check fuel | os_compute]
      end |
      let ty' := eval vm_compute in (run 40 ty) in
      tryif constr_eq ty ty' then fail else
        eapply ty_conv with (A := ty');
          [os_check fuel | os_check fuel | os_compute]]
  end]
  end.

Lemma list_def_unit : typing empty_ctx (list_def TUnitT) (Def TUnitT).
Proof. os_check 60. Qed.

Lemma nonempty_def_unit : typing empty_ctx (nonempty_def TUnitT) (Def TUnitT).
Proof. os_check 60. Qed.

#[local] Hint Resolve list_def_unit nonempty_def_unit : os_ground.

Lemma nil_unit : typing empty_ctx nil_value (list_type TUnitT).
Proof. os_check 60. Qed.

#[local] Hint Resolve nil_unit : os_ground.

Theorem singleton_source_elaborates :
  elab_check empty_ctx (singleton_source TUnit) (nonempty_type TUnitT)
    (singleton TUnit).
Proof.
  eapply ec_conversion; [apply es_ann | exists 0; os_check 60 | apply cv_refl].
  - exists 0; os_check 60.
  - eapply ec_constructor with
      (rs := nonempty_rows TUnitT) (n := 0) (D := cons_code TUnitT).
    + repeat split; os_check 60.
    + constructor.
      * unfold row_input. split; [os_check 60|]. split.
        -- repeat constructor; cbn; tauto.
        -- constructor; [cbn; os_check 60 | constructor].
      * os_check 60.
      * os_compute.
    + reflexivity.
    + let ty := eval vm_compute in
        (run 40 (TInterp TUnitT (cons_code TUnitT) (carrier TUnitT (list_def TUnitT)))) in
      eapply ec_target_conversion with (A := ty).
      * eapply ec_pair; [exists 0; os_check 60 | apply ec_core; os_check 60 | apply ec_core; os_check 60].
      * exists 0; os_check 60.
      * os_compute.
Qed.
Theorem no_uniform_list_downcast :
  ~ exists c, typing empty_ctx c
      (TPi 0 (TSort 0) (arrow (list_type (TVar 0)) (nonempty_type (TVar 0)))).
Proof.
  intros [c Hc].
  assert (Hbot : typing empty_ctx Bot (TSort 0)) by os_check 60.
  destruct (nonempty_observers_typing empty_ctx Bot Hbot) as [Hhead _].
  apply (consistency (TApp (head_term Bot) (TApp (TApp c Bot) nil_value))).
  eapply ty_app with (x := fresh [nonempty_type Bot; Bot])
    (A := nonempty_type Bot) (B := Bot); [os_check 60 | exact Hhead |].
  eapply ty_app with (x := fresh [list_type Bot; nonempty_type Bot])
    (A := list_type Bot) (B := nonempty_type Bot); [os_check 60 | | os_check 60].
  change (typing empty_ctx (TApp c Bot)
    (subst Bot 0 (arrow (list_type (TVar 0)) (nonempty_type (TVar 0))))).
  eapply ty_app with (x := 0) (A := TSort 0)
    (B := arrow (list_type (TVar 0)) (nonempty_type (TVar 0)));
    [os_check 60 | exact Hc | exact Hbot].
Qed.
Theorem self_restricted_list_empty :
  forall A,
    typing empty_ctx A (TSort 0) ->
    forall x, ~ typing empty_ctx x (endless_type A).

Proof.
  apply (endless_from_rules weakening preservation normalization_eval).
  intros t A Ht.
  destruct (accessible_run t (normalization _ _ _ Ht)) as [fuel Hnone].
  exists (run fuel t); split.
  - eapply preservation_eval; [exact Ht|apply run_sound].
  - intros u Hu. destruct (step_has_next _ _ Hu) as [v Hv]; congruence.
Qed.
