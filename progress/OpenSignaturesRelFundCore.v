(* Fundamental lemma, core cases: every typing rule preserves relatedness
   of instances under related closing environments. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelSubst.
Import ListNotations.

Definition FP Gamma t A := forall g1 g2, closing2 Gamma g1 g2 ->
  rel_at (instantiate g1 t) (instantiate g2 t) (instantiate g1 A) (instantiate g2 A).

Lemma FP_sort : forall Gamma X k g1 g2, FP Gamma X (TSort k) -> closing2 Gamma g1 g2 ->
  ty_rel k (instantiate g1 X) (instantiate g2 X).
Proof.
  intros Gamma X k g1 g2 H Hc; pose proof (H _ _ Hc) as H'.
  rewrite !instantiate_sort in H'; apply rel_at_sort, H'.
Qed.

Lemma inst_universe_le : forall g X Y, env_closed g -> universe_le X Y ->
  universe_le (instantiate g X) (instantiate g Y).
Proof.
  induction g as [|[y u] g IH]; intros X Y Hg H; [exact H|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [instantiate].
  apply IH; [exact Hg'|apply universe_le_subst; [exact H|exact Hu]].
Qed.

Ltac envs Hc := let H1 := fresh "Hg1" in let H2 := fresh "Hg2" in
  destruct (closing2_closed _ _ _ Hc) as [H1 H2].

Lemma fund_var : forall Gamma x A, wf Gamma -> lookup Gamma x = Some A -> FP Gamma (TVar x) A.
Proof. intros Gamma x A _ H g1 g2 Hc; eapply closing2_lookup; eassumption. Qed.

Lemma fund_sort : forall Gamma k, FP Gamma (TSort k) (TSort (S k)).
Proof. intros Gamma k g1 g2 _; rewrite !instantiate_sort; apply sem_sort. Qed.

Lemma fund_pi : forall Gamma x A B j k, fresh_in Gamma x ->
  FP Gamma A (TSort j) -> typing (extend Gamma x A) B (TSort k) -> FP (extend Gamma x A) B (TSort k) ->
  FP Gamma (TPi x A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma x A B j k Hx IA HB IB g1 g2 Hc. envs Hc.
  destruct (closing2_away _ _ _ _ Hc Hx) as [Ha1 Ha2].
  rewrite !instantiate_pi by assumption. rewrite !instantiate_sort. apply rel_at_sort.
  apply sem_pi; [eapply FP_sort; eassumption|].
  intros a1 a2 Hc1 Hc2 Ha.
  assert (Hc' : closing2 (extend Gamma x A) ((x, a1) :: g1) ((x, a2) :: g2)).
  { apply closing2_extend; try assumption. eapply typing_context; exact HB. }
  eapply ty_rel_conv; [eapply FP_sort; [exact IB|exact Hc']| |];
    apply inst_cons_conv; assumption.
Qed.

Lemma fund_sigma : forall Gamma x A B j k, fresh_in Gamma x ->
  FP Gamma A (TSort j) -> typing (extend Gamma x A) B (TSort k) -> FP (extend Gamma x A) B (TSort k) ->
  FP Gamma (TSigma x A B) (TSort (Nat.max j k)).
Proof.
  intros Gamma x A B j k Hx IA HB IB g1 g2 Hc. envs Hc.
  destruct (closing2_away _ _ _ _ Hc Hx) as [Ha1 Ha2].
  rewrite !inst_sigma by assumption. rewrite !(drop_away _ x) by assumption. rewrite !instantiate_sort.
  apply rel_at_sort. apply sem_sigma; [eapply FP_sort; eassumption|].
  intros a1 a2 Hc1 Hc2 Ha.
  assert (Hc' : closing2 (extend Gamma x A) ((x, a1) :: g1) ((x, a2) :: g2)).
  { apply closing2_extend; try assumption. eapply typing_context; exact HB. }
  eapply ty_rel_conv; [eapply FP_sort; [exact IB|exact Hc']| |];
    apply inst_cons_conv; assumption.
Qed.

Lemma fund_lam : forall Gamma x A B b k, fresh_in Gamma x ->
  FP Gamma (TPi x A B) (TSort k) -> typing (extend Gamma x A) b B -> FP (extend Gamma x A) b B ->
  FP Gamma (TLam x b) (TPi x A B).
Proof.
  intros Gamma x A B b k Hx IP Hb Ib g1 g2 Hc. envs Hc.
  destruct (closing2_away _ _ _ _ Hc Hx) as [Ha1 Ha2].
  pose proof (FP_sort _ _ _ _ _ IP Hc) as HP.
  rewrite !instantiate_pi in HP by assumption.
  rewrite !instantiate_lam, !instantiate_pi by assumption.
  eapply sem_lam; [exact HP|]. intros a1 a2 Hc1 Hc2 Ha.
  assert (Hc' : closing2 (extend Gamma x A) ((x, a1) :: g1) ((x, a2) :: g2)).
  { apply closing2_extend; try assumption. eapply typing_context; exact Hb. }
  eapply rel_at_conv; [exact (Ib _ _ Hc')| | | |]; apply inst_cons_conv; assumption.
Qed.

Lemma fund_app : forall Gamma x A B f a k, FP Gamma (TPi x A B) (TSort k) ->
  typing Gamma f (TPi x A B) -> FP Gamma f (TPi x A B) -> typing Gamma a A -> FP Gamma a A ->
  FP Gamma (TApp f a) (subst a x B).
Proof.
  intros Gamma x A B f a k _ Hf If Ha Ia g1 g2 Hc. envs Hc.
  pose proof (If _ _ Hc) as Hf'. rewrite !inst_pi in Hf' by assumption.
  destruct (inst_closed_typed _ _ _ _ _ Hc Ha) as [Hca1 Hca2].
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hf' (Ia _ _ Hc) Hca1 Hca2) as H.
  rewrite !instantiate_app.
  eapply rel_at_conv; [exact H|apply cv_refl|apply cv_refl| |];
    apply cv_alpha, alpha_sym, inst_subst; assumption.
Qed.

Lemma fund_pair : forall Gamma x A B a b k, FP Gamma (TSigma x A B) (TSort k) ->
  typing Gamma a A -> FP Gamma a A -> typing Gamma b (subst a x B) -> FP Gamma b (subst a x B) ->
  FP Gamma (TPair a b) (TSigma x A B).
Proof.
  intros Gamma x A B a b k IS Ha Ia Hb Ib g1 g2 Hc. envs Hc.
  pose proof (FP_sort _ _ _ _ _ IS Hc) as HS. rewrite !inst_sigma in HS by assumption.
  destruct (inst_closed_typed _ _ _ _ _ Hc Ha) as [Hca1 Hca2].
  destruct (inst_closed_typed _ _ _ _ _ Hc Hb) as [Hcb1 Hcb2].
  rewrite !inst_tpair, !inst_sigma by assumption.
  eapply sem_pair; [exact HS|exact Hca1|exact Hca2|exact Hcb1|exact Hcb2|exact (Ia _ _ Hc)|].
  eapply rel_at_conv; [exact (Ib _ _ Hc)|apply cv_refl|apply cv_refl| |];
    apply cv_alpha, inst_subst; assumption.
Qed.

Lemma fund_fst : forall Gamma x A B p k, FP Gamma (TSigma x A B) (TSort k) ->
  FP Gamma p (TSigma x A B) -> FP Gamma (TFst p) A.
Proof.
  intros Gamma x A B p k _ Ip g1 g2 Hc. envs Hc.
  pose proof (Ip _ _ Hc) as Hp. rewrite !inst_sigma in Hp by assumption.
  rewrite !inst_fst. eapply sem_fst; exact Hp.
Qed.

Lemma fund_snd : forall Gamma x A B p k, FP Gamma (TSigma x A B) (TSort k) ->
  FP Gamma p (TSigma x A B) -> FP Gamma (TSnd p) (subst (TFst p) x B).
Proof.
  intros Gamma x A B p k _ Ip g1 g2 Hc. envs Hc.
  pose proof (Ip _ _ Hc) as Hp. rewrite !inst_sigma in Hp by assumption.
  rewrite !inst_snd. eapply rel_at_conv; [eapply sem_snd; exact Hp|apply cv_refl|apply cv_refl| |].
  - apply cv_alpha, alpha_sym. eapply alpha_trans; [apply inst_subst; exact Hg1|].
    rewrite inst_fst; apply alpha_refl.
  - apply cv_alpha, alpha_sym. eapply alpha_trans; [apply inst_subst; exact Hg2|].
    rewrite inst_fst; apply alpha_refl.
Qed.

Lemma fund_alpha : forall Gamma t u A, FP Gamma t A -> alpha_equiv t u -> FP Gamma u A.
Proof.
  intros Gamma t u A It Ha g1 g2 Hc.
  eapply rel_at_conv; [exact (It _ _ Hc)| | |apply cv_refl|apply cv_refl];
    apply cv_alpha, instantiate_alpha, Ha.
Qed.

Lemma fund_conv : forall Gamma t A B, FP Gamma t A -> conv A B -> FP Gamma t B.
Proof.
  intros Gamma t A B It HC g1 g2 Hc.
  eapply rel_at_conv; [exact (It _ _ Hc)|apply cv_refl|apply cv_refl| |];
    apply instantiate_conversion, HC.
Qed.

Lemma fund_cumul : forall Gamma t j k, FP Gamma t (TSort j) -> j <= k -> FP Gamma t (TSort k).
Proof.
  intros Gamma t j k It Hjk g1 g2 Hc; pose proof (It _ _ Hc) as H.
  rewrite !instantiate_sort in *. eapply sem_universe_cumul; eassumption.
Qed.

Lemma fund_cumul_fun : forall Gamma f x A B C D k,
  FP Gamma f (TPi x A B) -> FP Gamma (TPi x C D) (TSort k) ->
  universe_le C A -> universe_le B D -> FP Gamma f (TPi x C D).
Proof.
  intros Gamma f x A B C D k If IP HCA HBD g1 g2 Hc. envs Hc.
  pose proof (If _ _ Hc) as Hf. pose proof (FP_sort _ _ _ _ _ IP Hc) as HP.
  rewrite !inst_pi in Hf, HP |- * by assumption.
  eapply sem_cumul_fun; [exact Hf|exact HP| | | |];
    apply inst_universe_le; try assumption; apply drop_closed; assumption.
Qed.
