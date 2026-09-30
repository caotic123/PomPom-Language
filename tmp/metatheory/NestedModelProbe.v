Require Import nameless.DBUniverseModel nameless.DBIndexedCandidates.
Import Full.
Definition payload_family := term -> term -> Prop.
Definition desc_functor := payload_family -> term -> Prop.

Inductive small_atom : term -> (term -> Prop) -> Prop :=
| sa_unit : small_atom TUnitT full_SN
| sa_mu : forall IT D i RI F,
    type_interp small_atom IT RI -> RI i ->
    (forall j, RI j -> desc_meaning RI (TApp D j) (F j)) ->
    small_atom (TApp (TMuI IT D) i)
      (Indexed.mu RI (fun X j => F j X) i)
with desc_meaning : (term -> Prop) -> term -> desc_functor -> Prop :=
| dm_one : forall RI, desc_meaning RI TI1 (fun _ => full_SN)
| dm_var : forall RI i, RI i ->
    desc_meaning RI (TIVar i) (fun X => X i)
| dm_pi : forall RI A D RA Phi,
    type_interp small_atom A RA ->
    (forall a, RA a -> desc_meaning RI (TApp D a) (Phi a)) ->
    desc_meaning RI (TIPi A D)
      (fun X => dependent_function RA (fun a => Phi a X)).

Print Assumptions small_atom_ind.
Print desc_meaning_ind.
