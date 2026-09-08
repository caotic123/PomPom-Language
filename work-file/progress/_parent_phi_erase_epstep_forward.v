(* Forward preservation of parallel eta reduction by phi erasure.  This does
   not assert the false converse reflection direction. *)

Require Import Progress _tmp_epstep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma phi_erase_epstep_forward_mut_parent :
  (forall t u, epstep t u ->
     epstep (phi_erase t) (phi_erase u)) /\
  (forall bs bs', epbranches bs bs' ->
     epbranches
       (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)
       (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn [phi_erase map]; intros;
    eauto using epstep, epbranches.
  rewrite phi_erase_lift. apply eps_eta. assumption.
Qed.

Corollary phi_erase_epstep_forward_parent : forall t u,
    epstep t u -> epstep (phi_erase t) (phi_erase u).
Proof. exact (proj1 phi_erase_epstep_forward_mut_parent). Qed.

Corollary phi_erase_epbranches_forward_parent : forall bs bs',
    epbranches bs bs' ->
    epbranches
      (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)
      (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs').
Proof. exact (proj2 phi_erase_epstep_forward_mut_parent). Qed.

Print Assumptions phi_erase_epstep_forward_parent.
Print Assumptions phi_erase_epbranches_forward_parent.
