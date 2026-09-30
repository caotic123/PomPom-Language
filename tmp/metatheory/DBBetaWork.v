From Stdlib Require Import List Arith Bool Lia.
Require Export DBContextConversionWork DBGenerationWork.
Import ListNotations.

Lemma convert_type : forall Gamma t A B,
  typing Gamma t A -> type_wf Gamma B -> conv A B -> typing Gamma t B.
Proof. intros Gamma t A B Ht [k HB] HC; eapply ty_conv;eassumption. Qed.
Lemma substitution_argument_conversion : forall B a b,
  conv a b -> conv (subst a 0 B) (subst b 0 B).
Proof.
  intros B a b HC. eapply cv_trans with (u:=TApp (TLam B) a).
  - apply cv_sym, cv_step, st_root;reflexivity.
  - eapply cv_trans with (u:=TApp (TLam B) b).
    + apply cv_compatible, cp_TApp; auto using cv_refl.
    + apply cv_step, st_root;reflexivity.
Qed.
Theorem beta_preservation : forall Gamma A B b a k,
  typing Gamma (TPi A B) (TSort k) -> typing Gamma (TLam b) (TPi A B) -> typing Gamma a A ->
  typing Gamma (subst a 0 b) (subst a 0 B).
Proof.
  intros Gamma A B b a k HPi Hlam Ha.
  destruct (lambda_generation _ _ _ Hlam _ eq_refl) as [C [D [l [HCD [Hb HC]]]]].
  apply conversion_pi in HC; destruct HC as [HAC HBD].
  destruct (pi_components _ _ _ HPi _ _ eq_refl) as [j [m [HA HB]]].
  destruct (pi_components _ _ _ HCD _ _ eq_refl) as [j' [m' [HC HD]]].
  assert (Ha' : typing Gamma a C) by (eapply ty_conv; [exact Ha|exact HC|now apply cv_sym]).
  eapply ty_conv.
  - exact (substitution _ _ _ _ _ Hb Ha').
  - exact (substitution _ _ _ _ _ HB Ha).
  - now apply conversion_subst.
Qed.
Theorem fst_preservation : forall Gamma A B a b k,
  typing Gamma (TSigma A B) (TSort k) -> typing Gamma (TPair a b) (TSigma A B) -> typing Gamma a A.
Proof.
  intros Gamma A B a b k HS Hp.
  destruct (pair_generation _ _ _ Hp _ _ eq_refl) as [C [D [l [HCD [Ha [Hb HC]]]]]].
  apply conversion_sigma in HC; destruct HC as [HAC HBD].
  destruct (sigma_components _ _ _ HS _ _ eq_refl) as [j [m [HA HB]]].
  eapply ty_conv;eassumption.
Qed.
Theorem snd_preservation : forall Gamma A B a b k,
  typing Gamma (TSigma A B) (TSort k) -> typing Gamma (TPair a b) (TSigma A B) ->
  typing Gamma b (subst (TFst (TPair a b)) 0 B).
Proof.
  intros Gamma A B a b k HS Hp.
  destruct (pair_generation _ _ _ Hp _ _ eq_refl) as [C [D [l [HCD [Ha [Hb HC]]]]]].
  apply conversion_sigma in HC; destruct HC as [HAC HBD].
  destruct (sigma_components _ _ _ HS _ _ eq_refl) as [j [m [HA HB]]].
  eapply ty_conv; [exact Hb| |].
  - exact (substitution _ _ _ _ _ HB (smart_fst _ _ _ _ _ HS Hp)).
  - eapply cv_trans; [apply conversion_subst;exact HBD|].
    apply substitution_argument_conversion, cv_sym, cv_step, st_root;reflexivity.
Qed.
