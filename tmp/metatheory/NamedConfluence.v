From Stdlib Require Import List.
Require Export EncodingReflection OpenSignaturesProgress.
Require ProofDB.DBConfluence.
Import ListNotations.

Theorem raw_conversion_joinability : forall t u, conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof.
  intros t u H.
  destruct (ProofDB.DBConfluence.conversion_joinable _ _ (encode_conversion _ _ H []))
    as [z [Htz Huz]].
  destruct (encode_reductions_inverse _ _ Htz t [] eq_refl) as [w [Htw Hw]].
  destruct (encode_reductions_inverse _ _ Huz u [] eq_refl) as [w' [Huw' Hw']].
  exists w, w'; repeat split; try assumption.
  apply encode_alpha_iff. congruence.
Qed.
Theorem raw_confluence : forall t u v, reduces t u -> reduces t v ->
  exists w w', reduces u w /\ reduces v w' /\ alpha_equiv w w'.
Proof.
  intros t u v Hu Hv. apply raw_conversion_joinability.
  eapply cv_trans with (u:=t).
  - apply cv_sym. exact (reduces_conv _ _ Hu).
  - exact (reduces_conv _ _ Hv).
Qed.
