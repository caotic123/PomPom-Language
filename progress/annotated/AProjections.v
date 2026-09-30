(* Pair inversion and projection computations keep explicit Sigma annotations. *)
From Stdlib Require Import List Arith.
Require Export annotated.AGeneration.
Import ListNotations.
Module RG := nameless.DBGeneration.

Lemma comparison_sigma_source : forall A B T,
  RC.type_comparison (Raw.TSigma A B) T ->
  RCore.conv (Raw.TSigma A B) T.
Proof.
  intros A B T H; inversion H; subst; auto.
  all: exfalso; match goal with
    HC : RCore.conv (Raw.TSigma _ _) _ |- _ =>
    pose proof (RG.conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate
  end.
Qed.

Lemma pair_generation : forall Gamma t T, typing Gamma t T -> forall A B a b,
  t = TPair A B a b -> exists j k,
  typing Gamma A (Raw.TSort j) /\
  typing (erase A :: Gamma) B (Raw.TSort k) /\
  typing Gamma a (erase A) /\
  typing Gamma b (Raw.subst (erase a) 0 (erase B)) /\
  RC.type_comparison (Raw.TSigma (erase A) (erase B)) T.
Proof.
  intros Gamma t T H; induction H; intros AA BB first second HE; try discriminate.
  - inversion HE; subst; exists j, k; repeat split; try assumption.
    apply RC.cmp_conversion, RCore.cv_refl.
  - destruct (IHtyping _ _ _ _ HE) as [j [l [HA [HB [Ha [Hb HC]]]]]].
    exists j, l; repeat split; try assumption.
    eapply RC.comparison_right_conversion; eassumption.
  - destruct (IHtyping _ _ _ _ HE) as [l [m [HA [HB [Ha [Hb HC]]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_sort; assumption.
  - destruct (IHtyping _ _ _ _ HE) as [l [m [HA [HB [Ha [Hb HC]]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_pi; assumption.
Qed.

Theorem fst_preservation : forall Gamma t T, typing Gamma t T ->
  forall A B C D a b, t = TFst A B (TPair C D a b) -> typing Gamma a T.
Proof.
  intros Gamma t T H; induction H; intros AA BB CC DD first second HE; try discriminate.
  all: try solve [eapply ty_conv; [eapply IHtyping; exact HE|eassumption|eassumption]].
  all: try solve [eapply ty_cumul; [eapply IHtyping; exact HE|eassumption]].
  all: try solve [eapply ty_cumul_fun; [eapply IHtyping; exact HE|eassumption|eassumption|eassumption|eassumption]].
  inversion HE; subst.
  destruct (pair_generation _ _ _ H1 _ _ _ _ eq_refl)
    as [l [m [HC [HD [Ha [Hb Hpair]]]]]].
  apply comparison_sigma_source in Hpair.
  destruct (RG.conversion_sigma _ _ _ _ Hpair) as [Hdom Hcod].
  eapply ty_conv; [exact Ha|exact (typing_erasure _ _ _ H)|exact Hdom].
Qed.

Theorem snd_preservation : forall Gamma t T, typing Gamma t T ->
  forall A B C D a b, t = TSnd A B (TPair C D a b) -> typing Gamma b T.
Proof.
  intros Gamma t T H; induction H; intros AA BB CC DD first second HE; try discriminate.
  all: try solve [eapply ty_conv; [eapply IHtyping; exact HE|eassumption|eassumption]].
  all: try solve [eapply ty_cumul; [eapply IHtyping; exact HE|eassumption]].
  all: try solve [eapply ty_cumul_fun; [eapply IHtyping; exact HE|eassumption|eassumption|eassumption|eassumption]].
  inversion HE; subst.
  destruct (pair_generation _ _ _ H1 _ _ _ _ eq_refl)
    as [l [m [HC [HD [Ha [Hb Hpair]]]]]].
  apply comparison_sigma_source in Hpair.
  destruct (RG.conversion_sigma _ _ _ _ Hpair) as [Hdom Hcod].
  eapply comparison_typing; [exact Hb| |].
  - apply RC.cmp_conversion; eapply RCore.cv_trans.
    + apply RS.conversion_subst; exact Hcod.
    + apply nameless.DBBeta.substitution_argument_conversion,
        RCore.cv_sym, RCore.cv_step, RCore.st_root; reflexivity.
  - eapply type_correctness with (t := TSnd AA BB (TPair CC DD first second)).
    eapply ty_snd; eassumption.
Qed.

Print Assumptions fst_preservation.
Print Assumptions snd_preservation.
