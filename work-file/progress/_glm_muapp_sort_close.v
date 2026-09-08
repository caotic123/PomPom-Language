(* ========================================================================== *)
(*  _glm_muapp_sort_close.v — GLM worker 3: closing layer for muapp_sort.     *)
(*                                                                            *)
(*  This file completes the typing-side proof of [muapp_sort] parametrically, *)
(*  reducing it to exactly two conversion interfaces:                         *)
(*                                                                            *)
(*    - [conv_pi_codomain_compatible_glm] — Pi-codomain injectivity of conv   *)
(*      (the (P1) premise documented in _glm_muapp_sort_origin.v);            *)
(*    - [conv_subst_compatible] — the substitution compatibility stated in    *)
(*      [_luna_mueq_subst.v] (the step-4 premise documented there).           *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort; no Progress.v conjecture*)
(*  is used anywhere (where Progress.v would invoke [conv_whd] we use the     *)
(*  fully proved [conv_whd_proved] of _work_conv_whd_pos.v, and the closed    *)
(*  lemmas of _glm_muapp_sort_origin.v — in particular the axiom-free twins). *)
(*                                                                            *)
(*  Architecture (each step a small named lemma):                             *)
(*                                                                            *)
(*    (0) conv-vs-Pi disjointness for stuck applications (muI/muS/Carrier).   *)
(*    (1) The subtyping-level Pi-codomain extraction.  The honest strongest   *)
(*        form is                                                             *)
(*           sub G (TPi IT (TSort 0)) (TPi A B) -> exists j, conv B (TSort j) *)
(*        NOT 'conv (TSort 0) B': cumulativity gives                          *)
(*           sub [] (TPi IT (TSort 0)) (TPi A (TSort 1))                      *)
(*        (su_pi with premise sub [A] (TSort 0) (TSort 1) by su_sort, e.g.    *)
(*        IT = A = TSort 0), while conv (TSort 0) (TSort 1) is underivable    *)
(*        (no step/congruence/eta/phi rule relates distinct sorts and         *)
(*        conv_whd_proved only forces the shared HSort class).  The           *)
(*        exists-form is exactly what the final theorem consumes (after       *)
(*        conv_subst_compatible transports it under the argument).            *)
(*        Handling of su_trans/su_pi is honest via the invariant              *)
(*        [pi_cod_sort_inv_glm]: 'every Pi convertible to X has a sort-       *)
(*        convertible codomain'.  It is the conv-side shadow of the syntactic *)
(*        source: it survives su_conv/su_trans verbatim, is vacuous at sorts  *)
(*        and stuck mu-applications (disjointness of (0)), and at su_pi it is *)
(*        re-established from the rule's own sub-promise                     *)
(*        sub (A'::G) B B' plus the invariant's refl-instantiation on the     *)
(*        source codomain through the closed lemma                           *)
(*        [glm_sub_sort_source_conv_glm] (subtyping transports sort-          *)
(*        convertibility of the source to the target).  No whd of B is ever   *)
(*        assumed — sub_transport (and its inherited interface axiom) is not  *)
(*        used at all; only conv_whd_proved and closed structural inductions. *)
(*    (2) The two ao_chk branch closers (muI-former / muS-former), each       *)
(*        reducing to [ao_chk_sort_glm] of the origin bundle.                 *)
(*    (3) [muapp_sort_from_compat_glm] — the required conditional theorem.    *)
(*                                                                            *)
(*  Axiom accounting: [Print Assumptions muapp_sort_from_compat_glm] reports  *)
(*  "Closed under the global context" — the two compatibilities are binders   *)
(*  of the theorem, not axioms.                                               *)
(* ========================================================================== *)

Require Import Progress _work_conv_whd_pos _glm_muapp_sort_origin.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* NOTE on [conv_subst_compatible]: the definition below is reproduced
   character-for-character from [_luna_mueq_subst.v].  That file currently
   does not compile in this environment (its [mueq_subst_var] proof cites
   [Nat.lt_trichotomy] without importing PeanoNat; Rocq 9.1 does not expose
   that name in its import scope), so its .vo is absent and it cannot be
   Required here.  Since we own none of it, the statement — which is all
   this file consumes — is restated verbatim; if _luna_mueq_subst.v is
   repaired the two definitions are convertible by reflexivity. *)
Definition conv_subst_compatible : Prop :=
  forall t t' u u', conv t t' -> conv u u' -> forall k,
    conv (subst u k t) (subst u' k t').

(* The exactly-two conversion interfaces. *)
Definition conv_pi_codomain_compatible_glm : Prop :=
  forall A0 B0 A1 B1, conv (TPi A0 B0) (TPi A1 B1) -> conv B0 B1.

(* ========================================================================== *)
(*  (0) A stuck mu-application never converts with a Pi.                      *)
(* ========================================================================== *)

Lemma glm_conv_muiapp_pi_glm : forall R i A B,
    conv (TApp (TMuI R) i) (TPi A B) -> False.
Proof.
  intros R i A B Hc.
  assert (Habs : HMuIApp = HPi).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; constructor | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

Lemma glm_conv_musapp_pi_glm : forall Sf i A B,
    conv (TApp (TMuS Sf) i) (TPi A B) -> False.
Proof.
  intros Sf i A B Hc.
  assert (Habs : HMuSApp = HPi).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; constructor | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

Lemma glm_conv_carrierapp_pi_glm : forall E Sf i A B,
    conv (TApp (Carrier E Sf) i) (TPi A B) -> False.
Proof.
  intros E Sf i A B Hc.
  assert (Habs : HMuIApp = HPi).
  { eapply conv_whd_proved;
      [exact Hc | apply whd_shape; unfold Carrier; constructor
      | apply whd_shape; constructor]. }
  discriminate Habs.
Qed.

(* ========================================================================== *)
(*  (1) The subtyping-level Pi-codomain extraction.                           *)
(* ========================================================================== *)

(* The conv-side invariant: every Pi convertible to X has a sort-convertible
   codomain.  (For X a syntactic Pi this is equivalent, via the compatibility
   premise at refl, to 'the codomain of X is sort-convertible'.) *)
Definition pi_cod_sort_inv_glm (X : term) : Prop :=
  forall A B, conv X (TPi A B) -> exists j, conv B (TSort j).

(* Introduction at a syntactic Pi with a sort-convertible codomain. *)
Lemma pi_cod_sort_inv_intro_glm :
  conv_pi_codomain_compatible_glm ->
  forall A0 B0 j, conv B0 (TSort j) -> pi_cod_sort_inv_glm (TPi A0 B0).
Proof.
  intros Hcomp A0 B0 j Hj A B Hc.
  exists j. eapply cv_trans.
  - apply cv_sym. apply (Hcomp A0 B0 A B Hc).
  - exact Hj.
Qed.

(* Elimination at a syntactic Pi (refl instantiation). *)
Lemma pi_cod_sort_inv_pi_elim_glm :
  forall A B, pi_cod_sort_inv_glm (TPi A B) -> exists j, conv B (TSort j).
Proof.
  intros A B H. exact (H A B (cv_refl (TPi A B))).
Qed.

(* The invariant is preserved by every sub rule.  This is the honest
   su_trans/su_pi handling: su_conv/su_trans transport it along the
   derivation; su_sort and the mu-target rules leave the goal vacuous
   (disjointness of (0)); su_pi rebuilds it from the rule's sub-promise
   on the codomain through glm_sub_sort_source_conv_glm. *)
Lemma sub_pi_cod_sort_inv_glm :
  conv_pi_codomain_compatible_glm ->
  forall G X Y, sub G X Y -> pi_cod_sort_inv_glm X -> pi_cod_sort_inv_glm Y.
Proof.
  intros Hcomp G X Y Hsub.
  induction Hsub; intros Hinv.
  - (* su_conv: conv X Y, so a Pi convertible to Y is convertible to X *)
    intros P Q Hc. exact (Hinv P Q (cv_trans H Hc)).
  - (* su_trans: chain the invariant through the middle *)
    exact (IHHsub2 (IHHsub1 Hinv)).
  - (* su_sort: the target is a sort; conv sort-vs-Pi is impossible *)
    intros P Q Hc. exfalso. eapply glm_conv_sort_pi_l_glm; exact Hc.
  - (* su_pi *)
    destruct (pi_cod_sort_inv_pi_elim_glm _ _ Hinv) as [j Hj].
    destruct (glm_sub_sort_source_conv_glm _ B B' Hsub2 j Hj) as [j' Hj'].
    eapply pi_cod_sort_inv_intro_glm; [exact Hcomp | exact Hj'].
  - (* su_forget: the target is a stuck Carrier application *)
    intros P Q Hc. exfalso. eapply glm_conv_carrierapp_pi_glm; exact Hc.
  - (* su_sig: the target is a stuck mu-S application *)
    intros P Q Hc. exfalso. eapply glm_conv_musapp_pi_glm; exact Hc.
Qed.

(* The extraction lemma, in its honest strongest form. *)
Lemma sub_pisort0_cod_sort_glm :
  conv_pi_codomain_compatible_glm ->
  forall G IT A B, sub G (TPi IT (TSort 0)) (TPi A B) ->
  exists j, conv B (TSort j).
Proof.
  intros Hcomp G IT A B Hsub.
  eapply pi_cod_sort_inv_pi_elim_glm.
  eapply sub_pi_cod_sort_inv_glm; [exact Hcomp | exact Hsub |].
  eapply pi_cod_sort_inv_intro_glm; [exact Hcomp | apply cv_refl].
Qed.

(* The requested shape conv (TSort 0) B holds under the extra hypothesis that
   B is sort-convertible only at level 0 in the relevant sense; formally we
   package the residual information the way the application consumes it:
   the codomain, substituted under the argument, is sort-convertible.  This
   is precisely where conv_subst_compatible enters (subst a 0 (TSort j) = TSort j). *)
Lemma subst_cod_sort_glm :
  conv_subst_compatible ->
  forall a B j, conv B (TSort j) -> conv (subst a 0 B) (TSort j).
Proof.
  intros Hsubst a B j Hj.
  eapply cv_sym.
  change (conv (subst a 0 (TSort j)) (subst a 0 B)).
  eapply Hsubst; [apply cv_sym; exact Hj | apply cv_refl].
Qed.

(* ========================================================================== *)
(*  (2) The ao_chk branch closers for the two value mu-formers.               *)
(* ========================================================================== *)

Lemma ao_chk_mui_sort_glm :
  conv_pi_codomain_compatible_glm -> conv_subst_compatible ->
  forall R a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp Hsubst R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl) as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - (* conv case: Pi-injectivity at the source, then substitute *)
      exists 0.
      eapply cv_sym.
      change (conv (subst a 0 (TSort 0)) (subst a 0 B)).
      eapply Hsubst.
      + eapply Hcomp; exact Hrel.
      + apply cv_refl.
    - (* sub case: the extraction lemma, then substitute *)
      destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. eapply subst_cod_sort_glm; [exact Hsubst | exact Hj]. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Lemma ao_chk_mus_sort_glm :
  conv_pi_codomain_compatible_glm -> conv_subst_compatible ->
  forall Sf a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp Hsubst Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl) as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0.
      eapply cv_sym.
      change (conv (subst a 0 (TSort 0)) (subst a 0 B)).
      eapply Hsubst.
      + eapply Hcomp; exact Hrel.
      + apply cv_refl.
    - destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. eapply subst_cod_sort_glm; [exact Hsubst | exact Hj]. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  (3) The required conditional theorem.                                     *)
(* ========================================================================== *)

(* value (TApp f a) forces f to be one of the two mu-formers. *)
Lemma value_app_mu_inv_glm : forall f a, value (TApp f a) ->
    (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf).
Proof.
  intros f a Hv. inversion Hv; subst.
  - left. eexists. reflexivity.
  - right. eexists. reflexivity.
Qed.

Theorem muapp_sort_from_compat_glm :
  conv_pi_codomain_compatible_glm ->
  conv_subst_compatible ->
  forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros Hcomp Hsubst f a T U h Hchk Hv Hc Hw.
  destruct (check_app_origin [] (TApp f a) T Hchk eq_refl f a eq_refl)
    as [X [Hor Hsub]].
  destruct (app_origin_sort_split_glm f a X T U h Hor Hv Hsub Hc Hw)
    as [Hdone | [A [B [k [HX [Hk [Hf Ha]]]]]]].
  - (* ao_syn: the synthesis branch, closed in the origin bundle *)
    exact Hdone.
  - (* ao_chk: the value application's head is a mu-former *)
    subst X.
    destruct (value_app_mu_inv_glm _ _ Hv) as [[R Hf'] | [Sf Hf']].
    + rewrite Hf' in Hf.
      eapply ao_chk_mui_sort_glm; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_glm; eassumption.
Qed.

(* Assumption audit anchors (run interactively):
   Print Assumptions muapp_sort_from_compat_glm.
   Print Assumptions sub_pisort0_cod_sort_glm.
   Print Assumptions ao_chk_mui_sort_glm.
   Print Assumptions ao_chk_mus_sort_glm. *)
