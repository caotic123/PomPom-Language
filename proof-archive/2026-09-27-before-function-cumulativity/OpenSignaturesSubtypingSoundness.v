(* Checked derived rules with explicit metatheory premises. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Export OpenSignaturesCoercionTyping OpenSignaturesTransport.
Import ListNotations.

Section SubtypingTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable regular : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Variable preserve : forall Gamma t u A,
  typing Gamma t A -> reduction t u -> typing Gamma u A.
Variable dead_typed : forall Gamma IT D X d,
  dead Gamma IT D X d -> typing Gamma d (arrow (TInterp IT D X) Bot).

Lemma compose_coercion_typing : forall Gamma A B C c d,
  type_wf Gamma A -> type_wf Gamma C ->
  typing Gamma c (arrow A B) -> typing Gamma d (arrow B C) ->
  typing Gamma (compose_coercion c d) (arrow A C).
Proof.
  intros Gamma A B C c d [j HA] [k HC] Hc Hd.
  pose proof (typing_context _ _ _ HA) as Hctx.
  unfold compose_coercion. eapply arrow_intro_fresh; [exact weaken|exact HA|exact HC|].
  intros y Hy Hfree.
  change (typing (extend Gamma y A)
    (TApp (subst (TVar y) (fresh [c; d]) d)
      (TApp (subst (TVar y) (fresh [c; d]) c)
        (if fresh [c; d] =? fresh [c; d] then TVar y else TVar (fresh [c; d])))) C).
  rewrite Nat.eqb_refl, !subst_fresh by (apply fresh_not_free; cbn; auto).
  eapply arrow_apply_regular with (A := B); [exact regular|eapply weaken; eassumption|].
  eapply arrow_apply_regular with (A := A); [exact regular|eapply weaken; eassumption|].
  apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
Qed.

Lemma bottom_coercion_typing : forall Gamma A k,
  typing Gamma A (TSort k) ->
  typing Gamma (TLam (fresh [A]) (abort k A (TVar (fresh [A])))) (arrow Bot A).
Proof.
  intros Gamma A k HA. pose proof (typing_context _ _ _ HA) as Hctx.
  assert (Hbot : typing Gamma Bot (TSort 0)) by (apply ty_enumt, ty_nile; exact Hctx).
  eapply arrow_intro_fresh; [exact weaken|exact Hbot|exact HA|].
  intros y Hy Hfree.
  change (typing (extend Gamma y Bot)
    (TSwitch k TNilE (subst (TVar y) (fresh [A]) (constant A)) TUnit
      (if fresh [A] =? fresh [A] then TVar y else TVar (fresh [A]))) A).
  rewrite Nat.eqb_refl, subst_fresh by (rewrite constant_free_vars; apply fresh_not_free; cbn; auto).
  apply abort_from_weakening; [exact weaken|eapply weaken; eassumption|].
  apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
Qed.

Lemma close_coercion_typing : forall Gamma IT F H G i q,
  close_input Gamma IT F G i -> close_input Gamma IT H G i ->
  typing Gamma q (arrow (payload IT F G i) (payload IT H G i)) ->
  typing Gamma (close_coercion IT F H G i q) (arrow (CloseAt IT F G i) (CloseAt IT H G i)).
Proof.
  intros Gamma IT F H G i q Hin Hout Hq.
  destruct Hin as [HIT [HF [HG Hi]]]. destruct Hout as [_ [HH _]].
  pose proof (typing_context _ _ _ HIT) as Hctx.
  assert (HS : typing Gamma (CloseAt IT F G i) (TSort 0)) by now apply close_at_formation.
  assert (HT : typing Gamma (CloseAt IT H G i) (TSort 0)) by now apply close_at_formation.
  pose (x := fresh [IT; F; H; G; i; q]).
  assert (HxIT : ~ In x (free_vars IT)) by (apply fresh_not_free; cbn; tauto).
  assert (HxF : ~ In x (free_vars F)) by (apply fresh_not_free; cbn; tauto).
  assert (HxG : ~ In x (free_vars G)) by (apply fresh_not_free; cbn; tauto).
  assert (Hxi : ~ In x (free_vars i)) by (apply fresh_not_free; cbn; tauto).
  assert (Hxq : ~ In x (free_vars q)) by (apply fresh_not_free; cbn; tauto).
  assert (HxQ : ~ In x (free_vars (constant (payload IT F G i)))).
  { rewrite constant_free_vars. unfold payload, carrier. cbn [free_vars].
    repeat rewrite in_app_iff. tauto. }
  unfold close_coercion. fold x. eapply arrow_intro_fresh; [exact weaken|exact HS|exact HT|].
  intros y Hy Hfree.
  change (typing (extend Gamma y (CloseAt IT F G i))
    (TIn (TApp (subst (TVar y) x q)
      (TCloseCase 0 (subst (TVar y) x IT) (subst (TVar y) x F) (subst (TVar y) x G)
        (subst (TVar y) x i) (subst (TVar y) x (constant (payload IT F G i)))
        (subst (TVar y) x identity) (if x =? x then TVar y else TVar x)))) (CloseAt IT H G i)).
  rewrite Nat.eqb_refl.
  rewrite (subst_fresh q) by exact Hxq.
  rewrite (subst_fresh IT) by exact HxIT.
  rewrite (subst_fresh F) by exact HxF.
  rewrite (subst_fresh G) by exact HxG.
  rewrite (subst_fresh i) by exact Hxi.
  rewrite (subst_fresh (constant (payload IT F G i))) by exact HxQ.
  rewrite (subst_fresh identity) by (cbn; tauto).
  apply ty_in_close; try solve [eapply weaken; eassumption].
  eapply arrow_apply_regular; [exact regular|eapply weaken; eassumption|].
  apply unroll_from_weakening; [exact weaken| |].
  - repeat split; eapply weaken; eassumption.
  - apply ty_var; [eapply wf_cons; eassumption|apply lookup_extend_same].
Qed.

Theorem subtyping_from_rules : forall Gamma A B c,
  sub Gamma A B c -> typing Gamma c (arrow A B).
Proof.
  intros Gamma A B c Hsub. induction Hsub.
  - destruct H as [j HA]. destruct H0 as [k HB]. eapply identity_for_typing; eassumption.
  - destruct (subtyping_formations _ _ _ _ Hsub1) as [HA _].
    destruct (subtyping_formations _ _ _ _ Hsub2) as [_ HC].
    apply compose_coercion_typing with (B := B); assumption.
  - now apply bottom_coercion_typing.
  - eapply pi_coercion_typing; eassumption.
  - apply close_coercion_typing; try assumption.
    apply description_subtyping_from_rules; assumption.
Qed.

End SubtypingTyping.
