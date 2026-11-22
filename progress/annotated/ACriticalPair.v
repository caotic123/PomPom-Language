(* Annotated reduction is not confluent on the nose. Beta and eta overlap
   on an application whose function is a cumulatively widened eta redex.
   The two reducts keep different application annotations, are both
   normal, and erase to the same raw term. Confluence for the annotated
   core therefore has to be stated modulo annotations. *)
From Stdlib Require Import List Arith.
Require Import annotated.AFullPreservation.
Import ListNotations.

Definition fun_ctx := [Raw.arrow Raw.TUnitT (Raw.TSort 0)].

(* (lambda x : Unit. f x : Sort 0) used at Unit -> Sort 1. *)
Definition widened_redex :=
  TApp TUnitT (TSort 1)
    (TLam TUnitT (TSort 0) (TApp TUnitT (TSort 0) (TVar 1) (TVar 0))) TUnit.
Definition beta_reduct := TApp TUnitT (TSort 0) (TVar 0) TUnit.
Definition eta_reduct := TApp TUnitT (TSort 1) (TVar 0) TUnit.

Lemma fun_ctx_wf : RT.wf fun_ctx.
Proof.
  eapply RT.wf_cons; [constructor|].
  unfold Raw.arrow; cbn [Raw.lift].
  apply RT.ty_pi with (j := 0) (k := 1).
  - apply RT.ty_unitT; constructor.
  - apply RT.ty_sort, (RT.wf_cons _ _ 0); [constructor|apply RT.ty_unitT; constructor].
Qed.

Lemma unit_fun_ctx_wf : RT.wf (Raw.TUnitT :: fun_ctx).
Proof.
  apply (RT.wf_cons _ _ 0); [exact fun_ctx_wf|apply RT.ty_unitT, fun_ctx_wf].
Qed.

Theorem widened_redex_typing : typing fun_ctx widened_redex (Raw.TSort 1).
Proof.
  pose proof fun_ctx_wf as HW; pose proof unit_fun_ctx_wf as HW'.
  assert (Hlam : typing fun_ctx
    (TLam TUnitT (TSort 0) (TApp TUnitT (TSort 0) (TVar 1) (TVar 0)))
    (Raw.TPi Raw.TUnitT (Raw.TSort 0))).
  { change (Raw.TPi Raw.TUnitT (Raw.TSort 0)) with
      (Raw.TPi (erase TUnitT) (erase (TSort 0))).
    apply ty_lam with (j := 0) (k := 1).
    - apply ty_unitT, HW.
    - apply ty_sort, HW'.
    - change (erase (TSort 0)) with
        (Raw.subst (erase (TVar 0)) 0 (erase (TSort 0))).
      apply ty_app with (j := 0) (k := 1).
      + apply ty_unitT, HW'.
      + apply ty_sort, (RT.wf_cons _ _ 0); [exact HW'|apply RT.ty_unitT, HW'].
      + exact (ty_var _ 1 _ HW' eq_refl).
      + exact (ty_var _ 0 _ HW' eq_refl). }
  change (Raw.TSort 1) with (Raw.subst (erase TUnit) 0 (erase (TSort 1))).
  apply ty_app with (j := 0) (k := 2).
  - apply ty_unitT, HW.
  - apply ty_sort, HW'.
  - eapply ty_cumul_fun with (j := 1) (k := 2); [exact Hlam| | |
      apply RT.ul_refl|apply RT.ul_sort; repeat constructor].
    + apply RT.ty_pi with (j := 0) (k := 1); [apply RT.ty_unitT, HW|apply RT.ty_sort, HW'].
    + apply RT.ty_pi with (j := 0) (k := 2); [apply RT.ty_unitT, HW|apply RT.ty_sort, HW'].
  - apply ty_unit, HW.
Qed.

Theorem widened_redex_beta : reduction widened_redex beta_reduct.
Proof. apply step_root, root_beta. Qed.

Theorem widened_redex_eta : reduction widened_redex eta_reduct.
Proof.
  apply step_context, cp_TApp_f, step_eta.
  exact (eta_contract_root TUnitT (TSort 0) TUnitT (TSort 0) (TVar 0)).
Qed.

Lemma atom_normal : forall t u, structural_step t u ->
  match t with TVar _ | TSort _ | TUnitT | TUnit => False | _ => True end.
Proof.
  intros t u H; destruct H as [t u R|t u R|t u R]; destruct R; exact I.
Qed.

Lemma variable_application_normal : forall k n u,
  ~ reduction (TApp TUnitT (TSort k) (TVar n) TUnit) u.
Proof.
  intros k n u H; unfold reduction in H.
  inversion H as [t v R|t v R|t v R]; subst.
  - inversion R.
  - inversion R.
  - inversion R; subst;
      match goal with HS : structural_step _ _ |- _ => exact (atom_normal _ _ HS) end.
Qed.

Theorem reducts_distinct : beta_reduct <> eta_reduct.
Proof. discriminate. Qed.

Theorem reducts_same_erasure : erase beta_reduct = erase eta_reduct.
Proof. reflexivity. Qed.

Lemma normal_reduces : forall k n w,
  reduces (TApp TUnitT (TSort k) (TVar n) TUnit) w ->
  w = TApp TUnitT (TSort k) (TVar n) TUnit.
Proof.
  intros k n w H; inversion H as [|t u v HR]; subst; [reflexivity|].
  exfalso; exact (variable_application_normal _ _ _ HR).
Qed.

Theorem annotated_reduction_not_confluent :
  ~ (forall t u v, reduces t u -> reduces t v ->
      exists w, reduces u w /\ reduces v w).
Proof.
  intro H.
  destruct (H widened_redex beta_reduct eta_reduct) as [w [Hu Hv]].
  - econstructor; [exact widened_redex_beta|constructor].
  - econstructor; [exact widened_redex_eta|constructor].
  - apply normal_reduces in Hu, Hv; rewrite Hu in Hv; discriminate.
Qed.

Print Assumptions widened_redex_typing.
Print Assumptions annotated_reduction_not_confluent.
