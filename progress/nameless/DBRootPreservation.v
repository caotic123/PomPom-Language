(* Every root computation rule preserves its declarative type. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEnumBeta.

Theorem root_preservation : forall Gamma t T,
  typing Gamma t T -> forall u, root_step t = Some u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros u Hr; try discriminate.
  - destruct f; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply beta_preservation; eassumption.
  - destruct p; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply fst_preservation; eassumption.
  - destruct p; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply snd_preservation; eassumption.
  - eapply ty_conv; [eapply IHtyping1; exact Hr|eassumption|eassumption].
  - eapply ty_cumul; [eapply IHtyping; exact Hr|eassumption].
  - eapply epi_beta; eassumption.
  - eapply switch_beta; eassumption.
  - eapply interp_beta; eassumption.
  - eapply iall_beta; eassumption.
  - eapply hyps_beta; eassumption.
  - destruct x; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply ind_beta; eassumption.
  - destruct x; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply close_case_beta with (IT:=IT) (F:=F) (G:=G) (i:=i) (k:=k); eassumption.
  - destruct x; cbn [root_step] in Hr; try discriminate; inversion Hr; subst.
    eapply close_ind_beta; eassumption.
  - eapply ty_cumul_fun; [eapply IHtyping1; exact Hr|eassumption|eassumption|eassumption|eassumption].
Qed.

Lemma lambda_root_preservation : forall Gamma t T,
  typing Gamma t T -> forall b b', t = TLam b -> root_step b = Some b' ->
  typing Gamma (TLam b') T.
Proof.
  intros Gamma t T H; induction H; intros body body' Heq Hr; try discriminate.
  - inversion Heq; subst. eapply ty_lam; [eassumption|eapply root_preservation; eassumption].
  - eapply ty_conv; [eapply IHtyping1; eassumption|eassumption|eassumption].
  - eapply ty_cumul; [eapply IHtyping; eassumption|eassumption].
  - eapply ty_cumul_fun; [eapply IHtyping1; eassumption|eassumption|eassumption|eassumption|eassumption].
Qed.

Lemma eta_lambda_preservation : forall Gamma b T,
  typing Gamma (TLam (TApp (lift 1 0 (TLam b)) (TVar 0))) T -> typing Gamma (TLam b) T.
Proof.
  intros Gamma b T H. eapply lambda_root_preservation; [exact H|reflexivity|].
  cbn [lift root_step]. now rewrite subst_eta_beta_cancel.
Qed.
