(* Concrete definitions use stable binding IDs. Generated IDs avoid all
   operands; adding a surrounding binder never shifts an existing reference. *)
From Stdlib Require Import List String.
Require Export OpenSignaturesElaboration.
Import ListNotations.
Open Scope string_scope.

Definition nil_code := TI1.
Definition cons_code A := TISig A (TLam (fresh [A]) (TIVar TUnit)).
Definition fork_code := TIProd (TIVar TUnit) (TIVar TUnit).

Definition list_rows A : row := [("nil",nil_code); ("cons",cons_code A)].
Definition nonempty_rows A : row := [("cons",cons_code A)].
Definition padded_rows A : row := [("nil",TIBot); ("cons",cons_code A)].
Definition tree_rows A : row :=
  [("nil",nil_code); ("cons",cons_code A); ("fork",fork_code)].

(* These signatures ignore their unit index. Their index IDs also avoid the
   generated binders inside the row code. *)
Definition unit_signature (rs : row) :=
  signature (fresh [TUnitT; row_code TUnitT rs]) TUnitT rs.
Definition list_def A := unit_signature (list_rows A).
Definition nonempty_def A := unit_signature (nonempty_rows A).
Definition padded_def A := unit_signature (padded_rows A).
Definition tree_def A := unit_signature (tree_rows A).

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
  let x := fresh [nonempty_type A; A] in
  let p := S x in
  TLam x (case_term 0 TUnitT (nonempty_def A)
    (list_def A) TUnit A (nonempty_rows A)
    [TLam p (TFst (TVar p))] (TVar x)).
Definition tail_term A :=
  let x := fresh [nonempty_type A; list_type A] in
  let p := S x in
  TLam x (case_term 0 TUnitT (nonempty_def A)
    (list_def A) TUnit (list_type A) (nonempty_rows A)
    [TLam p (TSnd (TVar p))] (TVar x)).

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
       (identity_for [A]);
     retag_handler 0].
Definition to_compact A :=
  close_coercion TUnitT (padded_def A) (nonempty_def A)
    (list_def A) TUnit (padded_to_compact_payload A).

(* Expected-type directed source introduction and singleton. *)
Definition singleton_source a :=
  EAnn (EConstructor "cons" (EPair (ECore a) (ECore nil_value)))
    (nonempty_type TUnitT).
Definition nonempty_signature_source A :=
  let rs := nonempty_rows A in
  ESignature (fresh [TUnitT; row_code TUnitT rs]) TUnitT rs.
Definition nonempty_application_source A :=
  EApp (EClose TUnitT (ECore (nonempty_def A)) (ECore (list_def A)))
    (ECore TUnit).
Definition head_source A :=
  let x := fresh [nonempty_type A; A] in
  let p := S x in
  EAnn (ELam x (ECase (EVar x) A
    [("cons",(p,ECore (TFst (TVar p))))]))
    (arrow (nonempty_type A) A).

Example singleton_head :
  run 80 (TApp (head_term TUnitT) (singleton TUnit)) = TUnit.
Proof. vm_compute. reflexivity. Qed.

Example singleton_tail :
  run 80 (TApp (tail_term TUnitT) (singleton TUnit)) = nil_value.
Proof. vm_compute. reflexivity. Qed.

Example singleton_retag :
  run 80 (TApp (to_list TUnitT) (singleton TUnit)) =
  cons_value TUnit nil_value.
Proof. vm_compute. reflexivity. Qed.

Example padded_roundtrip :
  run 160 (TApp (to_compact TUnitT)
    (TApp (to_padded TUnitT) (singleton TUnit))) = singleton TUnit.
Proof. vm_compute. reflexivity. Qed.

(* Open payload references retain their IDs while helper binders are freshened. *)
Example head_preserves_open_payload :
  run 80 (TApp (head_term (TVar 2)) (singleton (TVar 7))) = TVar 7.
Proof. vm_compute. reflexivity. Qed.
