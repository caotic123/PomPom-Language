(* ========================================================================== *)
(*  _glm_muapp_sort_origin.v — GLM worker 3: origin bundle for muapp_sort.   *)
(*                                                                            *)
(*  Owns the analysis of the [muapp_sort] conjecture (Progress.v) through     *)
(*  the [app_origin] decomposition of [check_app_origin].  No Abort, Admitted, *)
(*  Axiom, or Conjecture occurs in this file, and the targets [muapp_sort]    *)
(*  and [conv_enumt_inj] are never invoked.  Where Progress.v's [conv_whd]    *)
(*  would be used, we use the fully proved [conv_whd_proved] from             *)
(*  [_work_conv_whd_pos] instead.                                             *)
(*                                                                            *)
(*  Axiom accounting (Print Assumptions):                                     *)
(*    - sub_sort_source_whd_glm follows the mandated sub_transport route and  *)
(*      therefore inherits the single interface axiom Progress.conv_whd that  *)
(*      sub_transport itself stands on (see Progress.v su_sort/su_pi/...      *)
(*      cases);                                                               *)
(*    - sub_sort_source_whd_axfree_glm is the identical statement proved      *)
(*      closed under the global context, and everything downstream of the     *)
(*      bundle that can be routed through it (ao_chk residue, inversions)     *)
(*      is axiom-free as well.                                                *)
(*                                                                            *)
(*  Bundle:                                                                   *)
(*    (1) sub_sort_source_whd_glm  — a subtype of a sort whd-classifies only  *)
(*        as a sort (via sub_transport + conv_whd_proved).                    *)
(*    (2) ao_syn_branch_glm        — the ao_syn branch of app_origin closes.  *)
(*    (3) ao_chk analysis          — Pi/codomain inversion helpers that ARE   *)
(*        valid, the exact residue of the ao_chk branch, and the documented   *)
(*        first missing premise (see the banner above ao_chk analysis).       *)
(* ========================================================================== *)

Require Import Progress _work_conv_whd_pos.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  Conversion-side disjointness helpers (conv_whd_proved only).              *)
(* ========================================================================== *)

Lemma glm_conv_sort_pi_r_glm : forall j A B, conv (TPi A B) (TSort j) -> False.
Proof.
  intros j A B Hc.
  assert (Habs : HPi = HSort).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; constructor | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

Lemma glm_conv_sort_pi_l_glm : forall j A B, conv (TSort j) (TPi A B) -> False.
Proof.
  intros j A B Hc. eapply glm_conv_sort_pi_r_glm; eapply cv_sym; exact Hc.
Qed.

Lemma glm_conv_musapp_sort_glm : forall j Sf i,
    conv (TApp (TMuS Sf) i) (TSort j) -> False.
Proof.
  intros j Sf i Hc.
  assert (Habs : HMuSApp = HSort).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; constructor | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

Lemma glm_conv_carrierapp_sort_glm : forall j E Sf i,
    conv (TApp (Carrier E Sf) i) (TSort j) -> False.
Proof.
  intros j E Sf i Hc.
  assert (Habs : HMuIApp = HSort).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; unfold Carrier; constructor
      | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

(* Subtyping transports sort-convertibility of the source: if S ⊑ B and S is
   convertible to a sort, then B is convertible to a sort.  The μˢ-headed
   sources (su_forget, su_sig) are refuted because a stuck μ application
   carries the HMuSApp class, not the sort class; the Pi case is refuted by
   the disjointness lemma above. *)
Lemma glm_sub_sort_source_conv_glm : forall G S B, sub G S B ->
    forall j, conv S (TSort j) -> exists k, conv B (TSort k).
Proof.
  intros G S B Hsub. induction Hsub
    as [G0 A B0 Hc
    |G0 A B0 C H1 IH1 H2 IH2
    |G0 j0 k0 Hle
    |G0 A0 A1 B0 B1 Hdom IHdom Hcod IHcod
    |G0 Sf i IT E Hf1 Hf2 Hf3 Hf4
    |G0 S1 S2 i IT E Phi1 Phi2 Hg1 Hg2 Hg3 Hg4 Hg5 Hg6 Hg7 Hg8 Hg9];
    intros j Hcj.
  - (* su_conv *) exists j. eapply cv_trans; [apply cv_sym; exact Hc | exact Hcj].
  - (* su_trans *)
    destruct (IH1 j Hcj) as [k0 Hk0].
    exact (IH2 k0 Hk0).
  - (* su_sort *) exists k0. apply cv_refl.
  - (* su_pi *) exfalso. eapply glm_conv_sort_pi_r_glm; exact Hcj.
  - (* su_forget *) exfalso. eapply glm_conv_musapp_sort_glm; exact Hcj.
  - (* su_sig *) exfalso. eapply glm_conv_musapp_sort_glm; exact Hcj.
Qed.

(* Dually: subtyping towards a sort-convertible target keeps the source
   sort-convertible.  The Pi case is refuted by conv/Pi disjointness; the
   mu-Sig-forget target unfolds to a mu-I application whose class is not the
   sort class.  (Axiom-free.) *)
Lemma glm_sub_sort_target_conv_glm : forall G S T, sub G S T ->
    forall k, conv T (TSort k) -> exists j, conv S (TSort j).
Proof.
  intros G S T Hsub. induction Hsub
    as [G0 A B0 Hc
    |G0 A B0 C H1 IH1 H2 IH2
    |G0 j0 k0 Hle
    |G0 A0 A1 B0 B1 Hdom IHdom Hcod IHcod
    |G0 Sf i IT E Hf1 Hf2 Hf3 Hf4
    |G0 S1 S2 i IT E Phi1 Phi2 Hg1 Hg2 Hg3 Hg4 Hg5 Hg6 Hg7 Hg8 Hg9];
    intros k Hck.
  - (* su_conv *) exists k. eapply cv_trans; [exact Hc | exact Hck].
  - (* su_trans *)
    destruct (IH2 k Hck) as [j0 Hj0].
    exact (IH1 j0 Hj0).
  - (* su_sort *) exists j0. apply cv_refl.
  - (* su_pi *) exfalso. eapply glm_conv_sort_pi_r_glm; exact Hck.
  - (* su_forget *) exfalso. eapply glm_conv_carrierapp_sort_glm; exact Hck.
  - (* su_sig *) exfalso. eapply glm_conv_musapp_sort_glm; exact Hck.
Qed.

(* A sort-convertible source whd-classifies only as a sort.  Direct from
   conv_whd_proved, no subtyping needed. *)
Lemma conv_sort_target_whd_glm : forall j T U h,
    conv (TSort j) T -> conv T U -> whd U h -> h = HSort.
Proof.
  intros j T U h HcT HcU Hw.
  symmetry. eapply conv_whd_proved;
    [eapply cv_trans; [exact HcT | exact HcU]
    | apply whd_shape; constructor | exact Hw].
Qed.

(* ========================================================================== *)
(*  (1) Sorts have no proper subtypes up to whd classification.               *)
(* ========================================================================== *)

(* If B is a subtype of Set_j and U (convertible with B) has weak head
   class h, then h is the sort class.

   Proof shape (as instructed): [sub_transport] transports the whd class of
   U back to the source TSort j, either directly (conv TSort j U) or through
   a witness U' carrying a non-sort class; in every case [conv_whd_proved]
   forces the sort class of TSort j to equal the witness class, and every
   non-sort outcome (HPi, HMuSApp, HMuIApp) is discarded by discrimination.

   Dependency note: [sub_transport] (Progress.v) itself stands on the
   interface Conjecture [Progress.conv_whd], so this lemma inherits that
   single axiom; the axiom-free twin [sub_sort_source_whd_axfree_glm] below
   proves the identical statement from [conv_whd_proved] alone. *)
Lemma sub_sort_source_whd_glm : forall G j B U h,
    sub G (TSort j) B -> conv B U -> whd U h -> h = HSort.
Proof.
  intros G j B U h Hsub Hc Hw.
  destruct (sub_transport G (TSort j) B Hsub U h Hc Hw)
    as [HcS | [[Hh [U' [HcU' Hw']]] | [Hh [U' [HcU' Hw']]]]].
  - (* su-source convertible to U: TSort j itself has the sort class *)
    symmetry. eapply conv_whd_proved;
      [exact HcS | apply whd_shape; constructor | exact Hw].
  - (* class preserved with witness *)
    destruct Hh as [Hh | [Hh | Hh]].
    + exact Hh.
    + exfalso. rewrite Hh in Hw'. assert (Habs : HSort = HPi).
      { eapply conv_whd_proved;
          [exact HcU' | apply whd_shape; constructor | exact Hw']. }
      discriminate Habs.
    + exfalso. rewrite Hh in Hw'. assert (Habs : HSort = HMuSApp).
      { eapply conv_whd_proved;
          [exact HcU' | apply whd_shape; constructor | exact Hw']. }
      discriminate Habs.
  - (* mu-I class with witness: impossible against the sort class *)
    rewrite Hh. destruct Hw' as [Hw' | Hw'].
    + exfalso. assert (Habs : HSort = HMuIApp).
      { eapply conv_whd_proved;
          [exact HcU' | apply whd_shape; constructor | exact Hw']. }
      discriminate Habs.
    + exfalso. assert (Habs : HSort = HMuSApp).
      { eapply conv_whd_proved;
          [exact HcU' | apply whd_shape; constructor | exact Hw']. }
      discriminate Habs.
Qed.

(* Axiom-free twin of (1): identical statement, proved from the closed
   induction helper [glm_sub_sort_source_conv_glm] plus [conv_whd_proved]
   only — Print Assumptions: "Closed under the global context". *)
Lemma sub_sort_source_whd_axfree_glm : forall G j B U h,
    sub G (TSort j) B -> conv B U -> whd U h -> h = HSort.
Proof.
  intros G j B U h Hsub Hc Hw.
  destruct (glm_sub_sort_source_conv_glm G (TSort j) B Hsub j (cv_refl (TSort j)))
    as [k Hck].
  eapply conv_sort_target_whd_glm; [apply cv_sym, Hck | exact Hc | exact Hw].
Qed.

(* Two immediate corollaries: sorts and Pi types are unrelated by sub in
   either direction. *)
Lemma glm_sub_sort_pi_target_glm : forall G j A B,
    sub G (TSort j) (TPi A B) -> False.
Proof.
  intros G j A B Hsub.
  assert (Habs : HPi = HSort).
  { eapply sub_sort_source_whd_axfree_glm;
      [exact Hsub | apply cv_refl | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

Lemma glm_sub_pi_sort_target_glm : forall G A B k,
    sub G (TPi A B) (TSort k) -> False.
Proof.
  intros G A B k Hsub.
  destruct (glm_sub_sort_target_conv_glm G (TPi A B) (TSort k) Hsub k
              (cv_refl (TSort k))) as [j Hcj].
  exfalso. eapply glm_conv_sort_pi_r_glm; exact Hcj.
Qed.

(* And a sub-based transport for downstream use: a sort-convertible T
   whd-classifies any subtype U of it only as a sort. *)
Lemma sub_sort_target_whd_glm : forall j T U h,
    conv (TSort j) T -> sub [] T U -> whd U h -> h = HSort.
Proof.
  intros j T U h HcT HsubT Hw.
  eapply sub_sort_source_whd_axfree_glm with (B := U).
  - eapply su_trans; [apply su_conv; exact HcT | exact HsubT].
  - apply cv_refl.
  - exact Hw.
Qed.

(* ========================================================================== *)
(*  (2) The ao_syn branch of app_origin closes.                               *)
(* ========================================================================== *)

(* A value application synthesizes exactly Set_0 (value_app_synth_sort), so
   its check-target is a subtype of Set_0 and (1) applies.  (Swapping
   sub_sort_source_whd_glm for its axiom-free twin, which has the identical
   statement, makes this lemma closed under the global context as well.) *)
Lemma ao_syn_branch_glm : forall f a X T U h,
    value (TApp f a) -> synth [] (TApp f a) X -> sub [] X T ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros f a X T U h Hv Hsyn Hsub Hc Hw.
  pose proof (value_app_synth_sort f a X Hv Hsyn) as HX.
  rewrite HX in Hsub.
  eapply sub_sort_source_whd_axfree_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  (3) The ao_chk branch: valid Pi/codomain inversion helpers.               *)
(* ========================================================================== *)

(* Checking a μ-former forces the μ-former's own synthesis (sy_mui / sy_mus:
   a Pi ending in Set_0) to be related to the checked target.  The ch_expand
   case (expected type normalized by conversion) is absorbed by induction
   over the check derivation, so this inversion is complete.  At a Pi target
   this yields exactly the Pi/codomain comparison used in the ao_chk analysis
   below. *)
Lemma check_mui_synth_glm : forall G t T,
    check G t T ->
    forall R, t = TMuI R ->
    exists IT, synth G (TMuI R) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/ sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Rq Ht; subst; try discriminate.
  - (* ch_conv *)
    inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - (* ch_sub *)
    inversion H; subst. eexists. split; [eassumption | right; eassumption].
  - (* ch_expand *)
    destruct (IHHck Rq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + left. eapply cv_trans; [exact Hrel | apply cv_sym; exact H].
    + right. eapply su_trans; [exact Hrel | apply su_conv, cv_sym, H].
Qed.

Lemma check_mus_synth_glm : forall G t T,
    check G t T ->
    forall Sf, t = TMuS Sf ->
    exists IT, synth G (TMuS Sf) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/ sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Sfq Ht; subst; try discriminate.
  - (* ch_conv *)
    inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - (* ch_sub *)
    inversion H; subst. eexists. split; [eassumption | right; eassumption].
  - (* ch_expand *)
    destruct (IHHck Sfq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + left. eapply cv_trans; [exact Hrel | apply cv_sym; exact H].
    + right. eapply su_trans; [exact Hrel | apply su_conv, cv_sym, H].
Qed.

(* ------------------------------------------------------------------ *)
(*  The ao_chk residue, exactly.                                       *)
(*                                                                     *)
(*  app_origin has two constructors.  ao_syn is closed by (2).  For     *)
(*  ao_chk the premises are                                            *)
(*      check [] (TPi A B) (TSort k),  check [] f (TPi A B),            *)
(*      check [] a A,  X = subst a 0 B,                                *)
(*  and the goal h = HSort (with conv T U, whd U h, sub [] X T) holds   *)
(*  as soon as the instantiated codomain is sort-convertible — see      *)
(*  ao_chk_sort_glm below.  The check premises alone do NOT yield that  *)
(*  premise; the first exact missing premise is documented after the    *)
(*  residue lemma.                                                      *)
(* ------------------------------------------------------------------ *)

Lemma app_origin_sort_split_glm : forall f a X T U h,
    app_origin f a X -> value (TApp f a) -> sub [] X T -> conv T U -> whd U h ->
    h = HSort \/
    exists A B k, X = subst a 0 B /\
      check [] (TPi A B) (TSort k) /\ check [] f (TPi A B) /\ check [] a A.
Proof.
  intros f a X T U h Hor Hv Hsub Hc Hw.
  destruct Hor as [C Hsyn | A B k Hk Hf Ha].
  - left. eapply ao_syn_branch_glm; eassumption.
  - right. exists A, B, k.
    split; [reflexivity | split; [exact Hk | split; [exact Hf | exact Ha]]].
Qed.

(* The ao_chk branch closes given exactly ONE extra premise: the
   instantiated codomain subst a 0 B is convertible to a sort.  (The check
   premises are carried to record the branch's signature; the sort-
   convertibility premise subsumes what they would have to deliver.) *)
Lemma ao_chk_sort_glm : forall f a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] f (TPi A B) -> check [] a A ->
    (exists j, conv (subst a 0 B) (TSort j)) ->
    sub [] (subst a 0 B) T -> conv T U -> whd U h -> h = HSort.
Proof.
  intros f a A B k T U h Hk Hf Ha [j Hcj] Hsub Hc Hw.
  eapply sub_sort_source_whd_axfree_glm with (B := U).
  - eapply su_trans;
      [apply su_conv; apply cv_sym; exact Hcj |].
    eapply su_trans; [exact Hsub | apply su_conv; exact Hc].
  - apply cv_refl.
  - exact Hw.
Qed.

(* ------------------------------------------------------------------ *)
(*  DOCUMENTED FIRST MISSING PREMISE FOR ao_chk  (assumed nowhere in this  *)
(*  file; the only axiom anywhere here is the interface Conjecture          *)
(*  Progress.conv_whd inherited by the mandated sub_transport route of (1),  *)
(*  and the axfree twin covers every use of the statement).                  *)
(*                                                                     *)
(*  Proof attempt for ao_chk (f a value):                               *)
(*    step 1. value (TApp f a) forces f = TMuI R or f = TMuS Sf          *)
(*            (inversion of value; no other constructor makes an         *)
(*            application a value).                                      *)
(*    step 2. By check_mui_synth_glm (resp. check_mus_synth_glm),       *)
(*            check [] (TMuI R) (TPi A B) yields                         *)
(*              synth [] (TMuI R) (TPi IT (TSort 0))  and                *)
(*              conv (TPi IT (TSort 0)) (TPi A B)                        *)
(*                 \/ sub [] (TPi IT (TSort 0)) (TPi A B).               *)
(*            This step is fully proved above.                           *)
(*    step 3. BLOCKED.  To conclude conv (subst a 0 B) (TSort j) — the   *)
(*            premise ao_chk_sort_glm needs — step 2's relation must     *)
(*            be injected through the Pi.  The first exact missing       *)
(*            premise is Pi-codomain injectivity of conversion:          *)
(*                                                                     *)
(*              (P1) forall A0 B0 A1 B1,                                *)
(*                   conv (TPi A0 B0) (TPi A1 B1) -> conv B0 B1.        *)
(*                                                                     *)
(*            (In the ch_sub case of step 2 the analogous sub-level      *)
(*            premise 'sub [] (TPi IT (TSort 0)) (TPi A B) ->            *)
(*            conv (TSort 0) B' is also unavailable: sub_transport only  *)
(*            transports whd classes and, applied here, would need a     *)
(*            whd of B, which arbitrary codomains do not have.)          *)
(*                                                                     *)
(*    step 4. Even granting (P1), one further stated-but-unproved        *)
(*            fact is needed to instantiate the injectivity result at    *)
(*            the application: substitution-compatibility of conv,       *)
(*            exactly the predicate                                      *)
(*              conv_subst_compatible                                    *)
(*            of _luna_mueq_subst.v (conv t t' -> conv u u' -> conv      *)
(*            (subst u k t) (subst u' k t')), which is only *stated*     *)
(*            there, never proved.  With (P1) + that,                    *)
(*            conv (TSort 0) B gives conv (subst a 0 B) (TSort 0) and    *)
(*            ao_chk_sort_glm finishes the branch.                       *)
(*                                                                     *)
(*  This matches the header of Progress.v: muapp_sort stands on         *)
(*  'Pi-injectivity + substitution-compatibility'; neither is proved    *)
(*  in the repo (conv_pi injectivity is not even stated;                *)
(*  conv_subst_compatible is stated in _luna_mueq_subst.v only).         *)
(*                                                                     *)
(*  Note the branch is not vacuous: without these premises the ao_chk   *)
(*  branch cannot be closed because a codomain B with a non-sort whd    *)
(*  class (e.g. a Pi) would make h = HSort plainly false; the premises  *)
(*  check [] f (TPi A B) with value (TApp f a) must rule that out, and  *)
(*  ruling it out is exactly (P1)'s content.                            *)
(* ------------------------------------------------------------------ *)
