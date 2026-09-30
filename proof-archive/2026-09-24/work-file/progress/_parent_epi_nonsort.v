(* The two syntactic EPi root redexes cannot have a sort endpoint. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _parent_mueq_sort_stable.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma epi_nil_not_sort_parent : forall P j,
    ~ rtc cstep (TEPi TNilE P) (TSort j).
Proof.
  intros P j.
  eapply cstep_root_to_nonsort_parent with (q := TUnitT) (h := HUnitT).
  - apply rtc_one, pstep_cstep.
    exact (ps_epi_nil P P (pstep_refl P)).
  - constructor.
  - discriminate.
Qed.

Lemma epi_cons_not_sort_parent : forall tg E P j,
    ~ rtc cstep (TEPi (TConsE tg E) P) (TSort j).
Proof.
  intros tg E P j.
  eapply cstep_root_to_nonsort_parent with
    (q := TSigma (TApp P TEZero)
      (lift 1 0 (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))))
    (h := HSigma).
  - apply rtc_one, pstep_cstep.
    exact (ps_epi_cons tg tg E E P P
      (pstep_refl tg) (pstep_refl E) (pstep_refl P)).
  - constructor.
  - discriminate.
Qed.

Print Assumptions epi_nil_not_sort_parent.
Print Assumptions epi_cons_not_sort_parent.
