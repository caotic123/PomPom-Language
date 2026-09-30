Require Import Progress SignatureConversion.
From Stdlib Require Import List.
Import ListNotations TypeRules.
Import Progress._work_cjoin.

Lemma signature_live_tag_transport_luna : forall S0 i0 S1 i1 c n bs,
    fconv (TApp (TMuS S0) i0) (TApp (TMuS S1) i1) ->
    enum_pos c n ->
    Forall (fun d => exists m, enum_pos d m) bs ->
    spine_mem c (labels (TApp S0 i0)) ->
    covers bs (labels (TApp S1 i1)) ->
    exists d, In d bs /\ enum_pos d n.
Proof.
  intros S0 i0 S1 i1 c n bs Hf Hpos Hbs Hmem Hcov.
  destruct (fconv_cjoin _ _ Hf) as [w [H0 H1]].
  destruct (cjoin_musapp_inv_luna _ _ _ _ (ex_intro _ w (conj H0 H1)))
    as [HS Hi].
  pose proof (cjoin_conv_bridge _ _ HS) as HSc.
  pose proof (cjoin_conv_bridge _ _ Hi) as Hic.
  apply erased_spine_covered_pos with
    (L1 := labels (TApp S0 i0)) (L2 := labels (TApp S1 i1))
    (bs := bs) (c := c) (n := n).
  - exact Hpos.
  - exact Hbs.
  - exact Hmem.
  - exact Hcov.
  - exact (cv_snd (cv_app HSc Hic)).
Qed.

Print Assumptions signature_live_tag_transport_luna.
