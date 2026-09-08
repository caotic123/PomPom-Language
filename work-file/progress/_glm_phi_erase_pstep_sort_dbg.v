Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Goal
  (forall s u (H : pstep s u), forall t, phi_erase t = s ->
     exists t', pstep t t' /\ phi_erase t' = u) /\
  (forall bs bs' (H : pbranches bs bs'), forall bs0,
     map (fun '(c,b) => (phi_erase c, phi_erase b)) bs0 = bs ->
     exists bs0', pbranches bs0 bs0' /\
       map (fun '(c,b) => (phi_erase c, phi_erase b)) bs0' = bs').
Proof.
  apply pstep_pbranches_ind; cbn; intros.
  Show 3.
  Show 5.
  Show 43.
Abort.
