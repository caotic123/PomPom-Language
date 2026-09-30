(* Parallel eta development cannot reintroduce a signature body once phi
   erasure has removed it.  This is deliberately a preservation lemma, not
   the false backward-reflection statement. *)

Require Import Progress _tmp_epstep _tmp_eta_shape.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma phi_erase_epstep_fixed_mut_parent :
  (forall t u (H : epstep t u),
      phi_erase t = t -> phi_erase u = u) /\
  (forall bs bs' (H : epbranches bs bs'),
      map (fun '(c,b) => (phi_erase c, phi_erase b)) bs = bs ->
      map (fun '(c,b) => (phi_erase c, phi_erase b)) bs' = bs').
Proof.
  apply epstep_epbranches_ind; cbn [phi_erase map]; intros.
  all: match goal with
       | E : _ = _ |- _ => inversion E; subst; clear E
       end; cbn [phi_erase map].
  all: try reflexivity.
  all: try solve [f_equal; eauto].
  all: try solve [repeat f_equal; eauto].
  - (* eta: fixedness of the eta expansion exposes fixedness of its head. *)
    repeat match goal with
    | E : TLam _ = TLam _ |- _ => injection E as E
    | E : TApp _ _ = TApp _ _ |- _ => injection E as E
    end.
    match goal with
    | E : lift 1 0 (phi_erase _) = lift 1 0 _ |- _ =>
        apply lift_one_injective in E; eauto
    end.
Qed.

Corollary phi_erase_epstep_target_fixed_parent : forall t u,
    epstep t u -> phi_erase t = t -> phi_erase u = u.
Proof. exact (proj1 phi_erase_epstep_fixed_mut_parent). Qed.

Corollary phi_erase_epbranches_target_fixed_parent : forall bs bs',
    epbranches bs bs' ->
    map (fun '(c,b) => (phi_erase c, phi_erase b)) bs = bs ->
    map (fun '(c,b) => (phi_erase c, phi_erase b)) bs' = bs'.
Proof. exact (proj2 phi_erase_epstep_fixed_mut_parent). Qed.

Print Assumptions phi_erase_epstep_target_fixed_parent.
Print Assumptions phi_erase_epbranches_target_fixed_parent.
