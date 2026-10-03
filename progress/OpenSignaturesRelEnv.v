(* Related closing environments for the fundamental lemma. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelInst.
Import ListNotations.

Inductive closing2 : ctx -> env -> env -> Prop :=
| c2_nil : closing2 empty_ctx [] []
| c2_cons : forall Gamma g1 g2 x A u1 u2,
    fresh_in Gamma x -> wf (extend Gamma x A) -> type_wf Gamma A -> closing2 Gamma g1 g2 ->
    closed u1 -> closed u2 -> rel_at u1 u2 (instantiate g1 A) (instantiate g2 A) ->
    closing2 (extend Gamma x A) ((x, u1) :: g1) ((x, u2) :: g2).

Lemma closing2_wf : forall Gamma g1 g2, closing2 Gamma g1 g2 -> wf Gamma.
Proof. intros Gamma g1 g2 H; destruct H; [apply wf_nil|assumption]. Qed.

Lemma closing2_closed : forall Gamma g1 g2, closing2 Gamma g1 g2 -> env_closed g1 /\ env_closed g2.
Proof. intros Gamma g1 g2 H; induction H; [split; constructor|destruct IHclosing2; split; constructor; assumption]. Qed.

Lemma closing2_dom : forall Gamma g1 g2, closing2 Gamma g1 g2 ->
  forall y A, lookup Gamma y = Some A -> In y (map fst g1) /\ In y (map fst g2).
Proof.
  intros Gamma g1 g2 H; induction H; intros y B Hy.
  - unfold lookup, empty_ctx in Hy; rewrite BindingMapFacts.empty_o in Hy; discriminate.
  - destruct (Nat.eq_dec x y) as [->|Hne]; [cbn; tauto|].
    rewrite lookup_extend_other in Hy by exact Hne.
    destruct (IHclosing2 _ _ Hy); cbn; tauto.
Qed.

Lemma inst_closed : forall Gamma g1 g2 t, closing2 Gamma g1 g2 -> scoped Gamma t ->
  closed (instantiate g1 t) /\ closed (instantiate g2 t).
Proof.
  intros Gamma g1 g2 t H Hs; destruct (closing2_closed _ _ _ H) as [H1 H2]; split;
    apply closed_of_no_free; intros y Hy.
  - destruct (inst_free _ _ _ H1 Hy) as [Hf Hd]. destruct (Hs y Hf) as [A HA].
    apply Hd, (closing2_dom _ _ _ H _ _ HA).
  - destruct (inst_free _ _ _ H2 Hy) as [Hf Hd]. destruct (Hs y Hf) as [A HA].
    apply Hd, (closing2_dom _ _ _ H _ _ HA).
Qed.
Lemma inst_closed_typed : forall Gamma g1 g2 t A, closing2 Gamma g1 g2 -> typing Gamma t A ->
  closed (instantiate g1 t) /\ closed (instantiate g2 t).
Proof. intros; eapply inst_closed; [eassumption|eapply typing_scoped; eassumption]. Qed.

Lemma closing2_lookup : forall Gamma g1 g2, closing2 Gamma g1 g2 ->
  forall x A, lookup Gamma x = Some A ->
  rel_at (instantiate g1 (TVar x)) (instantiate g2 (TVar x)) (instantiate g1 A) (instantiate g2 A).
Proof.
  intros Gamma g1 g2 H; induction H; intros y B Hy.
  - unfold lookup, empty_ctx in Hy; rewrite BindingMapFacts.empty_o in Hy; discriminate.
  - pose proof (closing2_wf _ _ _ H2) as Hwf.
    destruct (Nat.eq_dec x y) as [->|Hne].
    + rewrite lookup_extend_same in Hy; inversion Hy; subst B.
      destruct H1 as [k Hk].
      assert (Hnf : ~ In y (free_vars A)) by (eapply typing_fresh_not_free; eassumption).
      cbn [instantiate]. rewrite !subst_var_same, !(subst_not_free A) by exact Hnf.
      rewrite !instantiate_closed by assumption. exact H5.
    + rewrite lookup_extend_other in Hy by exact Hne.
      assert (Hnf : ~ In x (free_vars B)) by (eapply wf_type_fresh_not_free; eassumption).
      cbn [instantiate]. rewrite !subst_var_other by (intro; apply Hne; auto).
      rewrite !(subst_not_free B) by exact Hnf. apply IHclosing2, Hy.
Qed.
