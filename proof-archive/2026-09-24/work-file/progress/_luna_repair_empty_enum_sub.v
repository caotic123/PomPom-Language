Require Import Progress.
Import _work_cjoin _work_cstep_invariants.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition erased_empty_enum (T : term) : Prop :=
  cjoin (phi_erase T) (TEnumT TNilE).

Lemma luna_cjoin_hshape_tag : forall t u h1 h2,
    cjoin t u -> hshape t h1 -> hshape u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 [w [Ht Hu]] Htshape Hushape.
  pose proof (rtc_cstep_hshape _ _ Ht h1 Htshape) as Hw1.
  pose proof (rtc_cstep_hshape _ _ Hu h2 Hushape) as Hw2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma luna_phi_erase_sort : forall k, hshape (phi_erase (TSort k)) HSort.
Proof. intros; cbn; constructor. Qed.

Lemma luna_phi_erase_pi : forall A B,
    hshape (phi_erase (TPi A B)) HPi.
Proof. intros; cbn; constructor. Qed.

Lemma luna_phi_erase_carrier : forall E Sf i,
    hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp.
Proof. intros; cbn [phi_erase Carrier]; constructor. Qed.

Lemma luna_phi_erase_musapp : forall Sf i,
    hshape (phi_erase (TApp (TMuS Sf) i)) HMuSApp.
Proof. intros; cbn; constructor. Qed.

Lemma erased_empty_enum_sub_back : forall G A B,
    sub G A B -> erased_empty_enum B -> erased_empty_enum A.
Proof.
  intros G A B Hsub. induction Hsub; intro Hempty.
  - unfold erased_empty_enum in *. eapply cjoin_trans;
      [apply conv_phi_cjoin; exact H | exact Hempty].
  - exact (IHHsub1 (IHHsub2 Hempty)).
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HSort = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_sort.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HPi = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_pi.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HMuIApp = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_carrier.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HMuSApp = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_musapp.
      - constructor. }
    discriminate Heq.
Qed.

Print Assumptions erased_empty_enum_sub_back.
