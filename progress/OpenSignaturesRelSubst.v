(* Instantiation commutes with substitution up to alpha-equivalence. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelDerived.
Import ListNotations.

Lemma alpha_refl : forall t, alpha_equiv t t.
Proof. intros; apply alpha_eqb_refl. Qed.
Lemma alpha_sym : forall t u, alpha_equiv t u -> alpha_equiv u t.
Proof. intros t u H; apply alpha_eqb_in_sym, H. Qed.
Lemma alpha_trans : forall t u v, alpha_equiv t u -> alpha_equiv u v -> alpha_equiv t v.
Proof. intros t u v H1 H2; eapply alpha_eqb_in_trans; eassumption. Qed.

Lemma subst_alpha_both : forall a a' x B B', alpha_equiv a a' -> alpha_equiv B B' ->
  alpha_equiv (subst a x B) (subst a' x B').
Proof.
  intros a a' x B B' Ha HB; unfold subst; apply substitute_alpha; [exact HB|].
  intros v _; destruct (Nat.eqb v x); [exact Ha|apply alpha_refl].
Qed.

Lemma subst_subst_closed : forall u y a x B, closed u -> y <> x ->
  alpha_equiv (subst u y (subst a x B)) (subst (subst u y a) x (subst u y B)).
Proof.
  intros u y a x B Hu Hne; unfold subst at 1 2 4.
  eapply alpha_trans; [apply substitute_compose|].
  eapply alpha_trans; [|apply alpha_sym, substitute_compose].
  apply substitute_alpha; [apply alpha_refl|]. intros v _.
  destruct (Nat.eqb v x) eqn:Ex.
  - apply Nat.eqb_eq in Ex; subst v. rewrite (proj2 (Nat.eqb_neq x y)) by auto.
    cbn [substitute]. rewrite Nat.eqb_refl. apply alpha_refl.
  - destruct (Nat.eqb v y) eqn:Ey.
    + cbn [substitute]. rewrite Ey.
      change (alpha_equiv u (subst (subst u y a) x u)). rewrite subst_not_free by (unfold closed in Hu; rewrite Hu; tauto).
      apply alpha_refl.
    + cbn [substitute]. rewrite Ey, Ex. apply alpha_refl.
Qed.

Lemma subst_subst_same : forall u a x B,
  alpha_equiv (subst u x (subst a x B)) (subst (subst u x a) x B).
Proof.
  intros u a x B; unfold subst at 1 2.
  eapply alpha_trans; [apply substitute_compose|].
  apply substitute_alpha; [apply alpha_refl|]. intros v _.
  destruct (Nat.eqb v x) eqn:Ex; [apply alpha_refl|].
  cbn [substitute]. rewrite Ex. apply alpha_refl.
Qed.

Lemma drop_cons_same : forall x u g, drop x ((x, u) :: g) = drop x g.
Proof. intros; unfold drop; cbn; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma drop_cons_other : forall x y u g, y <> x -> drop x ((y, u) :: g) = (y, u) :: drop x g.
Proof. intros; unfold drop; cbn; rewrite (proj2 (Nat.eqb_neq y x)) by assumption; reflexivity. Qed.

Lemma inst_subst : forall g a x B, env_closed g ->
  alpha_equiv (instantiate g (subst a x B)) (subst (instantiate g a) x (instantiate (drop x g) B)).
Proof.
  induction g as [|[y u] g IH]; intros a x B Hg; [apply alpha_refl|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [snd] in Hu.
  destruct (Nat.eq_dec y x) as [->|Hne].
  - rewrite drop_cons_same; cbn [instantiate].
    eapply alpha_trans; [apply instantiate_alpha, subst_subst_same|].
    apply IH, Hg'.
  - rewrite drop_cons_other by exact Hne; cbn [instantiate].
    eapply alpha_trans; [apply instantiate_alpha, subst_subst_closed; assumption|].
    apply IH, Hg'.
Qed.

Lemma closing2_away : forall Gamma g1 g2 x, closing2 Gamma g1 g2 -> fresh_in Gamma x ->
  closed_away g1 x /\ closed_away g2 x.
Proof.
  intros Gamma g1 g2 x H Hx; induction H; [split; constructor|].
  assert (Hne : x0 <> x) by (intro; subst; unfold fresh_in in Hx; rewrite lookup_extend_same in Hx; discriminate).
  assert (Hx' : fresh_in Gamma x) by (unfold fresh_in in *; rewrite lookup_extend_other in Hx by exact Hne; exact Hx).
  destruct (IHclosing2 Hx'); split; constructor; cbn; auto.
Qed.

Lemma drop_away : forall g x, closed_away g x -> drop x g = g.
Proof.
  intros g x H; induction H as [|[y u] g [Hne _] _ IH]; [reflexivity|].
  rewrite drop_cons_other by exact Hne; rewrite IH; reflexivity.
Qed.

Lemma inst_subst_away : forall g a x B, env_closed g -> closed_away g x ->
  conv (instantiate g (subst a x B)) (subst (instantiate g a) x (instantiate g B)).
Proof.
  intros g a x B Hg Ha; apply cv_alpha. rewrite <- (drop_away g x Ha) at 3. apply inst_subst, Hg.
Qed.

(* Extending related environments under a fresh binder. *)
Lemma closing2_extend : forall Gamma g1 g2 x A a1 a2, closing2 Gamma g1 g2 ->
  fresh_in Gamma x -> wf (extend Gamma x A) -> closed a1 -> closed a2 ->
  rel_at a1 a2 (instantiate g1 A) (instantiate g2 A) ->
  closing2 (extend Gamma x A) ((x, a1) :: g1) ((x, a2) :: g2).
Proof.
  intros Gamma g1 g2 x A a1 a2 H Hx Hwf H1 H2 Ha; apply c2_cons; try assumption.
  eapply (extension_domain_formation named_weakening named_type_correctness named_beta_preservation);
    [eapply closing2_wf; exact H|exact Hx|exact Hwf].
Qed.

Lemma inst_cons_conv : forall g x a t, env_closed g -> closed_away g x -> closed a ->
  conv (instantiate ((x, a) :: g) t) (subst a x (instantiate g t)).
Proof.
  intros g x a t Hg Hx Ha; cbn [instantiate]. apply cv_alpha.
  apply instantiate_commute; [exact Hx|exact Ha].
Qed.
