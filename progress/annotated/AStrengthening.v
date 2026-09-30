(* Annotation-sensitive strengthening. A removed binder must be absent
   from the entire term, including every type annotation. The reconstructed
   type may be more precise; raw comparison records that difference. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AContextInsertion.
Require nameless.DBOperatorFormations.
Import ListNotations.
Module RO := nameless.DBOperatorFormations.
Module RCore := nameless.DBCore.

Ltac raw_subst_macros := repeat first
  [rewrite RS.subst_arrow in * | rewrite RS.subst_Def in * |
   rewrite RS.subst_Family in * | rewrite RS.subst_motive in * |
   rewrite RS.subst_recursive_method in * |
   rewrite RS.subst_close_case_method in * |
   rewrite RS.subst_close_motive in * |
   rewrite RS.subst_mu_ind_method in * |
   rewrite RS.subst_close_ind_method in *].
Ltac raw_lift_macros := repeat first
  [rewrite RW.lift_arrow in * | rewrite RW.lift_Def in * |
   rewrite RW.lift_Family in * | rewrite RW.lift_motive in * |
   rewrite RW.lift_recursive_method in * |
   rewrite RW.lift_close_case_method in * |
   rewrite RW.lift_close_motive in * |
   rewrite RW.lift_mu_ind_method in * |
   rewrite RW.lift_close_ind_method in *].
Ltac normalize_lower :=
  repeat rewrite <- RB.lift_subst_zero_comm in *;
  raw_subst_macros;
  cbn [Raw.subst Raw.MuAt Raw.CloseAt Raw.payload Raw.carrier] in *;
  repeat rewrite RB.subst_lift_cancel in *;
  repeat rewrite RB.subst_subst_zero_comm in *;
  repeat rewrite RB.subst_lift_cancel in *.
Ltac raw_form := first [
  match goal with
  | HB : RT.typing (?A :: ?G) ?B (Raw.TSort ?k),
    Ha : RT.typing ?G ?a ?A |- RT.type_wf ?G (Raw.subst ?a 0 ?B) =>
    exists k; exact (RS.substitution _ _ _ _ _ HB Ha)
  end |
  unfold RT.type_wf; eexists;
  eauto 7 using RT.ty_sort, RT.ty_pi, RT.ty_sigma, RT.ty_unitT, RT.ty_uid,
    RT.ty_enumu, RT.ty_enumt, RT.ty_conse, RT.ty_idesc, RT.ty_interp, RT.ty_iall,
    RT.ty_epi, RO.def_formation, DT.family_formation, DT.mu_at_formation,
    DT.close_at_formation, DT.total_formation, nameless.DBInductionBeta.motive_formation,
    nameless.DBInductionBeta.payload_formation, DT.smart_mui, DT.smart_close, nameless.DBInductionBeta.def_application,
    RO.recursive_method_formation, RO.mu_method_formation,
    RO.close_method_formation, RO.close_motive_formation,
    RO.close_case_method_formation, DT.regular_application,
    RO.sort_codomain_formation, nameless.DBConstructorGeneration.arrow_formation,
    RT.wf_cons, RW.typing_context, RS.substitution].

Ltac recover_premise :=
  match goal with
  | IH : forall (c : nat) (G : Raw.ctx) (u : term),
      insertion c G ?D -> RT.wf G -> lift 1 ?cut ?t = lift 1 c u ->
      exists S, typing G u S /\ RC.type_comparison (Raw.lift 1 c S) ?T,
    HI : insertion ?cut ?G ?D, HW : RT.wf ?G |- _ =>
    let HC := fresh "Hchecked" in
    assert (HC : typing G t (Raw.subst Raw.TUnit cut T)) by
      (eapply recovered_lower_typing; [exact (IH cut G t HI HW eq_refl)|
         normalize_lower; solve [raw_form]]);
    clear IH;
    normalize_lower;
    let HR := fresh "Herased" in pose proof (typing_erasure _ _ _ HC) as HR
  end.
Ltac insert_binder :=
  match goal with
  | IH : forall (c : nat) (G : Raw.ctx) (u : term),
      insertion c G (Raw.lift 1 ?cut (erase ?A) :: ?D) -> _,
    HI : insertion ?cut ?G ?D,
    HA : typing ?G ?A (Raw.TSort ?k), HW : RT.wf ?G |- _ =>
    tryif (match goal with
      _ : insertion (S cut) (erase A :: G) (Raw.lift 1 cut (erase A) :: D) |- _ => idtac
    end) then fail else
    let HI' := fresh "Hinserted" in
    let HW' := fresh "Hextended" in
    pose proof (insert_under _ _ _ (erase A) HI) as HI';
    assert (HW' : RT.wf (erase A :: G)) by
      (eapply RT.wf_cons; [exact HW|exact (typing_erasure _ _ _ HA)])
  end.

Theorem typing_strengthening_comparison : forall Delta t T, typing Delta t T ->
  forall c Gamma u, insertion c Gamma Delta -> RT.wf Gamma -> t = lift 1 c u ->
  exists S, typing Gamma u S /\ RC.type_comparison (Raw.lift 1 c S) T.
Proof.
  intros Delta t T H; induction H; intros cut Theta u HI HW HE.
  all: try solve [
    destruct (IHtyping cut Theta u HI HW HE) as [S [HS HC]];
    exists S; split; [exact HS|eapply RC.comparison_right_conversion; eassumption]].
  all: try solve [
    destruct (IHtyping cut Theta u HI HW HE) as [S [HS HC]];
    exists S; split; [exact HS|eapply RC.comparison_transitive; [exact HC|
      apply RC.comparison_universe; constructor; assumption]]].
  all: destruct u; cbn [lift] in HE;
    repeat match type of HE with context [if ?b then _ else _] => destruct b eqn:? end;
    try discriminate; inversion HE; subst; clear HE;
    repeat rewrite erase_lift in *.
  all: repeat first [recover_premise | insert_binder].
  all: try solve [eexists; split; [econstructor; eassumption|
    raw_lift_macros; cbn [Raw.lift Raw.MuAt Raw.CloseAt Raw.payload Raw.carrier];
    repeat rewrite RB.lift_subst_zero_comm; cbn [Raw.lift];
    apply RC.cmp_conversion, RCore.cv_refl]].
  all: try solve [
    assert (HS : nth_error Gamma (RW.shift_index cut n0) = Some A) by
      (unfold RW.shift_index; rewrite Heqb; exact H0);
    destruct (insertion_lookup _ _ _ HI _ _ HS) as [B [HB HE]];
    exists (Raw.lift (S n0) 0 B); split;
    [eapply ty_var; eassumption|rewrite HE;
      unfold RW.shift_index; rewrite Heqb; apply RC.cmp_conversion, RCore.cv_refl]].

Qed.

Print Assumptions typing_strengthening_comparison.
