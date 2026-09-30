Require Import Progress _tmp_epstep _tmp_eta_shape _tmp_epstep_inv
  _tmp_eta_tool _tmp_epstep_subst _tmp_epstep_diamond.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ====================================================================== *)
(*  Chunk 1 — conv_pos by direct induction on conv.                        *)
(*  Invariant: convertibility propagates enum_pos positions.              *)
(* ====================================================================== *)

Lemma enum_pos_inv : forall u m, enum_pos u m ->
    (u = TEZero /\ m = 0) \/
    (exists c0 m1, u = TESucc c0 /\ m = S m1 /\ enum_pos c0 m1).
Proof. intros u m H; inversion H; subst; [left; auto | right; eauto]. Qed.

(* no step enters an enum_pos term from a non-enum_pos term *)
Lemma step_enum_pos_stable : forall t u,
    step t u -> forall m, enum_pos u m -> enum_pos t m.
Proof.
  intros t u H. induction H; intros m Hu.
  all: destruct (enum_pos_inv _ _ Hu)
         as [[Hu1 Hu2] | [c0 [m1 [Hu1 [Hu2 Hc]]]]].
  all: try (rewrite Hu1 in H; exfalso; solve [inversion H]).
  - all: try match goal with
    | Hs : step _ (TESucc _) |- _ => idtac "FOUND"; inversion Hs; subst
    end.
    all: idtac "NOMATCH". Show. Abort.
Qed.

Lemma conv_pos_aux :
  (forall t u, conv t u ->
      (forall c n, t = c -> enum_pos c n -> enum_pos u n) /\
      (forall c n, u = c -> enum_pos c n -> enum_pos t n)) /\
  True.
Proof.
  split.
  2: exact I.
  intros t u H. induction H.
  - (* cv_step *)
    split; intros c n Heq Hpos; subst.
    + exfalso. eapply pos_step_normal; [exact Hpos | exact H].
    + apply (step_enum_pos_stable t u H n Hpos).
  - (* cv_refl *)
    split; intros c n Heq Hpos; subst; exact Hpos.
  - (* cv_sym *)
    destruct IHconv as [IHf IHr]. split; [exact IHr | exact IHf].
  - (* cv_trans *)
    destruct IHconv1 as [IHf1 _]. destruct IHconv2 as [IHf2 _].
    split; intros c n Heq Hpos; subst.
    + apply IHf2. apply IHf1. exact Hpos.
    + apply IHf2. apply IHf1. exact Hpos.
  - (* cv_eta: TLam-headed, never TEZero/TESucc *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_phi: TApp-headed *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_pi *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_lam *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_app *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_sigma *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_pair *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_fst *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_snd *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_conse *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_enumt *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_esucc *)
    split; intros c n Heq; subst.
    + destruct Hpos as [-> | [x [n0 [-> Hx]]]].
      * constructor.
      * constructor. apply IHconv. exact Hx.
    + destruct Hpos as [-> | [x [n0 [-> Hx]]]].
      * constructor.
      * constructor. apply IHconv. exact Hx.
  - (* cv_epi *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_switch *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_idesc *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_ivar *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_iprod *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_ipi *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_isig *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_ichoice *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_interp *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_mui *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_mus *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_in *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_ind *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_iall *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_hyps *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_list *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_lnil *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_lcons *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_case *)
    split; intros c n Heq; subst; discriminate.
  - (* cv_case_br *)
    split; intros c n Heq; subst; discriminate.
Qed.

Theorem conv_pos : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.
Proof.
  intros c d n m Hcd Hc Hd.
  destruct (proj1 (proj1 conv_pos_aux c d Hcd c n eq_refl Hc)) as Hdn.
  eapply enum_pos_functional; [exact Hdn | exact Hd].
Qed.
