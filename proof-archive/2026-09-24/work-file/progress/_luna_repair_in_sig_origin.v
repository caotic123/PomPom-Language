Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants
  Progress._work_conv_whd_pos.

Lemma in_pair_origin_aux : forall G t T, check G t T -> forall c xs,
    t = TIn (TPair c xs) ->
    (exists R i IT,
       check G IT (TSort 0) /\
       check G R (TPi IT (TIDesc (lift 1 0 IT))) /\
       check G i IT /\
       check G (TPair c xs) (TInterp (TApp R i) (TMuI R)) /\
       conv (TApp (TMuI R) i) T) \/
    (exists Sf i IT E Phi,
       check G IT (TSort 0) /\ check G E TEnumU /\
       check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) /\
       check G i IT /\ check G c (Label E) /\
       eval (labels (TApp Sf i)) Phi /\ spine_mem c Phi /\
       check G xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) /\
       conv (TApp (TMuS Sf) i) T).
Proof.
  intros G t T HC; induction HC; intros c0 xs0 Eq; try discriminate; inversion Eq; subst.
  - inversion H.
  - inversion H.
  - destruct (IHHC c0 xs0 eq_refl) as [K | K].
    + destruct K as [R [i [IT [HIT [HR [Hi [Hx Hty]]]]]]].
      left; exists R, i, IT; repeat split; try assumption.
      eapply cv_trans; [exact Hty | apply cv_sym; exact H].
    + destruct K as [Sf [i [IT [E [Phi [HIT [HE [HSf [Hi [Hc [Hl [Hm [Hx Hty]]]]]]]]]]]]].
      right; exists Sf, i, IT, E, Phi; repeat split; try assumption.
      eapply cv_trans; [exact Hty | apply cv_sym; exact H].
  - left; exists R, i, IT; repeat split; eauto using cv_refl.
  - right; exists Sf, i, IT, E, Phi; repeat split; eauto using cv_refl.
Qed.

Print Assumptions in_pair_origin_aux.

Lemma in_pair_mus_origin : forall c xs Sf i,
    check [] (TIn (TPair c xs)) (TApp (TMuS Sf) i) ->
    exists S0 i0 IT0 E0 Phi0,
      check [] IT0 (TSort 0) /\ check [] E0 TEnumU /\
      check [] S0 (TPi IT0 (Sig (lift 1 0 IT0) (lift 1 0 E0))) /\
      check [] i0 IT0 /\ check [] c (Label E0) /\
      eval (labels (TApp S0 i0)) Phi0 /\ spine_mem c Phi0 /\
      check [] xs (TInterp (TApp (branches (TApp S0 i0)) c)
        (Carrier E0 S0)) /\
      conv (TApp (TMuS S0) i0) (TApp (TMuS Sf) i).
Proof.
  intros c xs Sf i H.
  destruct (in_pair_origin_aux [] (TIn (TPair c xs)) (TApp (TMuS Sf) i)
              H c xs eq_refl) as [KM | KS].
  - destruct KM as [R [i0 [IT0 [HIT0 [HR [Hi0 [Hx Hconv]]]]]]].
    exfalso.
    pose proof (conv_whd_proved _ _ _ _ Hconv
      (whd_shape _ _ (hs_muiapp R i0))
      (whd_shape _ _ (hs_musapp Sf i))) as K.
    discriminate K.
  - destruct KS as [S0 [i0 [IT0 [E0 [Phi0
      [HIT0 [HE0 [HS0 [Hi0 [Hc [HL [Hm [Hx Hconv]]]]]]]]]]]]].
    exists S0, i0, IT0, E0, Phi0.
    repeat split; assumption.
Qed.

Print Assumptions in_pair_mus_origin.
