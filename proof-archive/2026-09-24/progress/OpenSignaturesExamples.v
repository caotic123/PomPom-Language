(* Concrete definitions and executable reduction checks.
   These checks prove only closed syntactic computations by reflexivity.
   Typing and metatheory claims are separately stated as conjectures. *)
From Stdlib Require Import List String.
Require Export OpenSignaturesElaboration.
Import ListNotations.
Open Scope string_scope.

Definition nil_code := TI1.
Definition cons_code A := TISig A (TLam (TIVar TUnit)).
Definition fork_code := TIProd (TIVar TUnit) (TIVar TUnit).

Definition list_rows A : row := [("nil",nil_code); ("cons",cons_code A)].
Definition nonempty_rows A : row := [("cons",cons_code A)].
Definition padded_rows A : row := [("nil",TIBot); ("cons",cons_code A)].
Definition tree_rows A : row :=
  [("nil",nil_code); ("cons",cons_code A); ("fork",fork_code)].

(* signature's schemes live under the unit-index binder. *)
Definition list_def A := signature TUnitT (list_rows (lift 1 0 A)).
Definition nonempty_def A := signature TUnitT (nonempty_rows (lift 1 0 A)).
Definition padded_def A := signature TUnitT (padded_rows (lift 1 0 A)).
Definition tree_def A := signature TUnitT (tree_rows (lift 1 0 A)).

Definition list_type A := CloseAt TUnitT (list_def A) (list_def A) TUnit.
Definition nonempty_type A :=
  CloseAt TUnitT (nonempty_def A) (list_def A) TUnit.
Definition padded_type A :=
  CloseAt TUnitT (padded_def A) (list_def A) TUnit.
Definition tree_type A := CloseAt TUnitT (tree_def A) (tree_def A) TUnit.
Definition endless_type A :=
  CloseAt TUnitT (nonempty_def A) (nonempty_def A) TUnit.

Definition nil_value := TIn (TPair TEZero TUnit).
Definition cons_value a xs :=
  TIn (TPair (TESucc TEZero) (TPair a xs)).
Definition nonempty_value a xs :=
  TIn (TPair TEZero (TPair a xs)).
Definition singleton a := nonempty_value a nil_value.

Definition head_term A :=
  TLam (case_term 0 TUnitT (nonempty_def (lift 1 0 A))
    (list_def (lift 1 0 A)) TUnit (lift 1 0 A)
    (nonempty_rows (lift 1 0 A)) [TLam (TFst (TVar 0))] (TVar 0)).
Definition tail_term A :=
  TLam (case_term 0 TUnitT (nonempty_def (lift 1 0 A))
    (list_def (lift 1 0 A)) TUnit (list_type (lift 1 0 A))
    (nonempty_rows (lift 1 0 A)) [TLam (TSnd (TVar 0))] (TVar 0)).

Definition nonempty_to_list_payload A :=
  row_map 0 TUnitT (nonempty_rows A) (carrier TUnitT (list_def A))
    (payload TUnitT (list_def A) (list_def A) TUnit)
    [retag_handler 1].
Definition to_list A :=
  close_coercion TUnitT (nonempty_def A) (list_def A)
    (list_def A) TUnit (nonempty_to_list_payload A).

Definition compact_to_padded_payload A :=
  row_map 0 TUnitT (nonempty_rows A) (carrier TUnitT (list_def A))
    (payload TUnitT (padded_def A) (list_def A) TUnit)
    [retag_handler 1].
Definition to_padded A :=
  close_coercion TUnitT (nonempty_def A) (padded_def A)
    (list_def A) TUnit (compact_to_padded_payload A).
Definition padded_to_compact_payload A :=
  row_map 0 TUnitT (padded_rows A) (carrier TUnitT (list_def A))
    (payload TUnitT (nonempty_def A) (list_def A) TUnit)
    [dead_handler 0 (payload TUnitT (nonempty_def A) (list_def A) TUnit)
       (TLam (TVar 0));
     retag_handler 0].
Definition to_compact A :=
  close_coercion TUnitT (padded_def A) (nonempty_def A)
    (list_def A) TUnit (padded_to_compact_payload A).

(* Expected-type directed source introduction and singleton. *)
Definition singleton_source a :=
  EAnn (EConstructor "cons" (EPair (ECore a) (ECore nil_value)))
    (nonempty_type TUnitT).
Definition nonempty_signature_source A :=
  ESignature TUnitT (nonempty_rows (lift 1 0 A)).
Definition nonempty_application_source A :=
  EApp (EClose TUnitT (ECore (nonempty_def A)) (ECore (list_def A)))
    (ECore TUnit).
Definition head_source A :=
  EAnn (ELam (ECase (EVar 0) (lift 1 0 A)
    [("cons",ECore (TFst (TVar 0)))]))
    (arrow (nonempty_type A) A).

Example head_singleton_computes :
  run 100 (TApp (head_term TUnitT) (singleton TUnit)) = TUnit := eq_refl.
Example tail_singleton_computes :
  run 100 (TApp (tail_term TUnitT) (singleton TUnit)) = nil_value := eq_refl.
Example widening_changes_local_tag :
  run 100 (TApp (to_list TUnitT) (singleton TUnit)) =
    cons_value TUnit nil_value := eq_refl.
Example widening_keeps_the_list_tail :
  run 100 (TApp (to_list TUnitT)
    (nonempty_value TUnit (cons_value TUnit nil_value))) =
    cons_value TUnit (cons_value TUnit nil_value) := eq_refl.
Example compact_padded_roundtrip :
  run 200 (TApp (to_compact TUnitT)
    (TApp (to_padded TUnitT) (singleton TUnit))) =
    singleton TUnit := eq_refl.
Example bottom_interpretation_computes :
  run 10 (TInterp TUnitT TIBot (carrier TUnitT (list_def TUnitT))) =
    Bot := eq_refl.
Example close_types_do_not_unfold :
  next_step (list_type TUnitT) = None := eq_refl.
Example signature_application_keeps_its_type_parameter :
  run 10 (TApp (list_def (TVar 0)) TUnit) =
    row_code TUnitT (list_rows (TVar 0)) := eq_refl.

(* Capture check: c refers to an outer-context variable. B refers both to
   its bound argument and to the surrounding context. *)
Example dependent_codomain_keeps_outer_variables :
  coerced_codomain (TVar 0) (TApp (TVar 1) (TVar 0)) =
    TApp (TVar 1) (TApp (TVar 1) (TVar 0)) := eq_refl.
Example pi_coercion_inserts_function_below_argument :
  pi_coercion (TVar 0) (TApp (TVar 1) (TVar 0)) =
    TLam (TLam
      (TApp (TApp (TVar 2) (TVar 0))
        (TApp (TVar 1) (TApp (TVar 2) (TVar 0))))) := eq_refl.
