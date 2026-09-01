From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.
Lemma test_tsize_ind :
  forall (P : term -> Prop),
    (forall t, (forall u, tsize u < tsize t -> P u) -> P t) ->
    forall t, P t.
Proof.
  intros P H t.
  refine (@well_founded_induction nat lt lt_wf
           (fun n => forall u, tsize u = n -> P u)
           (fun n IH => _)
           (tsize t) t eq_refl).
  intros u Hn.
  apply H.
  intros v Hv.
  assert (Hv' : tsize v < n) by lia.
  exact (IH (tsize v) Hv' v eq_refl).
Qed.
Lemma test_tsize_case_bs_b : forall M Q bs c b,
    In (c,b) bs -> tsize b < tsize (TCase M Q bs).
Proof.
  intros M Q bs c b Hin.
  pose proof (bsize_in bs c b Hin) as H.
  pose proof (tsize_pos c) as Hc.
  change (tsize (TCase M Q bs)) with (S (tsize M + tsize Q + bsize bs)).
  lia.
Qed.
