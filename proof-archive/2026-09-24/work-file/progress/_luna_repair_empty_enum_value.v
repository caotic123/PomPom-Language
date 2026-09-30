Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.
Import Progress._luna_phi_erase_shapes.
Require Import _luna_repair_pi.
Require Import _parent_repair_muapp.

Lemma cjoin_erased_sort_empty_enum_luna : forall k,
    cjoin (phi_erase (TSort k)) (TEnumT TNilE) -> False.
Proof.
  intros k H.
  pose proof (cjoin_hshape_tags_parent _ _ _ _ H
    (phi_erase_hshape_luna (TSort k) HSort (hs_sort k)) (hs_enumt TNilE)) as E.
  discriminate E.
Qed.

Lemma erased_enum_clash_luna : forall T h,
    cjoin (phi_erase T) (TEnumT TNilE) ->
    hshape (phi_erase T) h -> h <> HEnumT -> False.
Proof.
  intros T h HJ HH Hneq.
  pose proof (cjoin_hshape_tags_parent _ _ _ _ HJ HH
    (hs_enumt TNilE)) as E.
  exact (Hneq E).
Qed.

Lemma no_value_empty_enum_luna : forall v T,
    value v -> check [] v T -> conv T (TEnumT TNilE) -> False.
Proof.
  intros v T Hv Hcheck Hconv.
  pose proof (canon_main [] v T Hcheck eq_refl Hv
    (TEnumT TNilE) HEnumT Hconv
    (whd_shape _ _ (hs_enumt TNilE))) as Hcanon.
  cbn in Hcanon.
  destruct Hcanon as [tg [E0 [Hbad Hshape]]].
  exact (conv_enumt_cons_nil_absurd tg E0 Hbad).
Qed.

Print Assumptions no_value_empty_enum_luna.

Lemma erased_empty_synth_value : forall t T,
    synth [] t T -> value t ->
    cjoin (phi_erase T) (TEnumT TNilE) -> False.
Proof.
  intros t T Hsyn Hv HJ.
  inversion Hsyn; subst; try solve [inversion Hv].
  all: try solve [
    eapply erased_enum_clash_luna; [exact HJ | cbn [phi_erase]; constructor | discriminate] ].
  all: try match goal with
  | HS : synth [] (TApp ?f ?a) ?C |- _ =>
      pose proof (value_app_synth_sort f a C Hv HS) as ->;
      eapply cjoin_erased_sort_empty_enum_luna; exact HJ
  end.
  pose proof (value_app_synth_sort _ _ _ Hv Hsyn) as Hsort.
  rewrite Hsort in HJ.
  exact (cjoin_erased_sort_empty_enum_luna 0 HJ).
Qed.

Print Assumptions erased_empty_synth_value.
