(* Compatible beta, eta, and projection preservation. Primitive operator
   root computations still have to be added before this is full preservation. *)
Require Export annotated.ACompatible annotated.ABeta annotated.AProjections
  annotated.AEtaPreservation.

Theorem structural_root_preservation : forall Gamma t u T,
  typing Gamma t T -> structural_root t u -> typing Gamma u T.
Proof.
  intros Gamma t u T HT HR; destruct HR.
  - eapply beta_preservation; exact HT.
  - eapply fst_preservation; [exact HT|reflexivity].
  - eapply snd_preservation; [exact HT|reflexivity].
Qed.

Theorem structural_step_preservation : forall t u,
  structural_step t u -> forall Gamma T, typing Gamma t T -> typing Gamma u T.
Proof.
  fix IH 3; intros t u HR Gamma T HT; destruct HR.
  - eapply structural_root_preservation; eassumption.
  - eapply eta_root_preservation; eassumption.
  - eapply compatible_preservation; [exact HT|].
    destruct H; constructor; split;
      [now apply structural_step_conversion|intros; eapply IH; eassumption].
Qed.

Print Assumptions structural_step_preservation.
