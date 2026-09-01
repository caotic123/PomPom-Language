Require Import Progress _tmp_epstep _tmp_epstep_subst _tmp_eta_tool
  _tmp_commute _work_pstep_lift_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Ltac invert_core_other :=
  match goal with
  | Hcore : pstep ?s ?t
      |- exists v, epstep ?t v /\ pstep ?u v =>
      inversion Hcore; subst; clear Hcore
  | Hcore : pbranches ?ss ?ts
      |- exists vs, epbranches ?ts vs /\ pbranches ?us vs =>
      inversion Hcore; subst; clear Hcore
  end.

Ltac take_eta_ind_commute :=
  match goal with
  | IH : forall z, pstep ?s z ->
        exists w, epstep z w /\ pstep ?t w,
    H : pstep ?s ?z |- _ =>
      let w := fresh "w" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH z H) as [w [He Hp]];
      clear IH
  | IH : forall zs, pbranches ?ss zs ->
        exists ws, epbranches zs ws /\ pbranches ?ts ws,
    H : pbranches ?ss ?zs |- _ =>
      let ws := fresh "ws" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH zs H) as [ws [He Hp]];
      clear IH
  end.

Lemma pstep_epstep_commute_eta_ind_mut :
  (forall s u (H : epstep s u), forall t, pstep s t ->
      exists v, epstep t v /\ pstep u v) /\
  (forall ss us (H : epbranches ss us), forall ts, pbranches ss ts ->
      exists vs, epbranches ts vs /\ pbranches us vs).
Proof.
  apply epstep_epbranches_ind.
  all: intros.
  all: invert_core_other.
  all: repeat invert_eta_known_shape.
  all: repeat take_eta_ind_commute.
  all: try solve [eexists; split; econstructor; eassumption].
  all: try solve [solve_computation_root].
  shelve. shelve.
  Show.
Abort.
