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
(* A nonempty list keeps both labels of a list and hides nil: its payload is
   the empty description, so no nil value can be built and cons keeps its
   position. *)
Definition nonempty_rows A : row := [("nil",TIBot); ("cons",cons_code A)].
Definition tree_rows A : row :=
  [("nil",nil_code); ("cons",cons_code A); ("fork",fork_code)].

(* These signatures ignore their unit index. Their index IDs also avoid the
   generated binders inside the row code. *)
Definition unit_signature (rs : row) :=
  signature (fresh [TUnitT; row_code TUnitT rs]) TUnitT rs.
Definition list_def A := unit_signature (list_rows A).
Definition nonempty_def A := unit_signature (nonempty_rows A).
Definition tree_def A := unit_signature (tree_rows A).

Definition list_type A := CloseAt TUnitT (list_def A) (list_def A) TUnit.
Definition nonempty_type A :=
  CloseAt TUnitT (nonempty_def A) (list_def A) TUnit.
Definition tree_type A := CloseAt TUnitT (tree_def A) (tree_def A) TUnit.
Definition endless_type A :=
  CloseAt TUnitT (nonempty_def A) (nonempty_def A) TUnit.

Definition nil_value := TIn (TPair TEZero TUnit).
Definition cons_value a xs :=
  TIn (TPair (TESucc TEZero) (TPair a xs)).
(* The same term as cons_value: hiding a label does not move the others. *)
Definition nonempty_value a xs :=
  TIn (TPair (TESucc TEZero) (TPair a xs)).
Definition singleton a := nonempty_value a nil_value.

(* The witness that the hidden nil payload is empty, as dead_bot generates it. *)
Definition hidden_nil A :=
  identity_for [TUnitT; TIBot; carrier TUnitT (list_def A)].

Definition head_term A :=
  let x := fresh [nonempty_type A; A] in
  let p := S x in
  TLam x (case_term 0 TUnitT (nonempty_def A)
    (list_def A) TUnit A (nonempty_rows A)
    [dead_handler 0 A (hidden_nil A); TLam p (TFst (TVar p))] (TVar x)).
Definition tail_term A :=
  let x := fresh [nonempty_type A; list_type A] in
  let p := S x in
  TLam x (case_term 0 TUnitT (nonempty_def A)
    (list_def A) TUnit (list_type A) (nonempty_rows A)
    [dead_handler 0 (list_type A) (hidden_nil A); TLam p (TSnd (TVar p))] (TVar x)).

Definition nonempty_to_list_payload A :=
  row_map 0 TUnitT (nonempty_rows A) (carrier TUnitT (list_def A))
    (payload TUnitT (list_def A) (list_def A) TUnit)
    [dead_handler 0 (payload TUnitT (list_def A) (list_def A) TUnit) (hidden_nil A);
     retag_handler 1].
Definition to_list A :=
  close_coercion TUnitT (nonempty_def A) (list_def A)
    (list_def A) TUnit (nonempty_to_list_payload A).

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
(* The nil clause is omitted: its payload is empty. *)
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

(* A nonempty list is the same term as the list it denotes ... *)
Example singleton_is_cons :
  singleton TUnit = cons_value TUnit nil_value.
Proof. reflexivity. Qed.

(* ... and the coercion to lists returns the value it was given. *)
Example singleton_retag :
  run 80 (TApp (to_list TUnitT) (singleton TUnit)) =
  cons_value TUnit nil_value.
Proof. vm_compute. reflexivity. Qed.

(* Open payload references retain their IDs while helper binders are freshened. *)
Example head_preserves_open_payload :
  run 80 (TApp (head_term (TVar 2)) (singleton (TVar 7))) = TVar 7.
Proof. vm_compute. reflexivity. Qed.
