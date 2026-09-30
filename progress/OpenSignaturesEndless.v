(* A normal endless list would contain a smaller inhabitant of the same type. *)
From Stdlib Require Import List Arith Bool Lia Wf_nat.
Require Export OpenSignaturesNamedCanonical OpenSignaturesObservers.
Import ListNotations.

Definition step_normal t := forall u, ~ step t u.
Lemma normal_evaluation : forall t u, step_normal t -> eval t u -> t = u.
Proof. intros t u Hn He; destruct He; auto. exfalso; eapply Hn; eassumption. Qed.
Lemma normal_context : forall C : term -> term,
  (forall t u, step t u -> step (C t) (C u)) ->
  forall t, step_normal (C t) -> step_normal t.
Proof. unfold step_normal; intros C HC t Hn u Hu; eapply Hn; eauto. Qed.
Lemma normal_in : forall t, step_normal (TIn t) -> step_normal t.
Proof. apply (normal_context TIn); auto using st_TIn_x. Qed.
Lemma normal_pair_snd : forall a b, step_normal (TPair a b) -> step_normal b.
Proof. intro a; apply (normal_context (TPair a)); auto using st_TPair_b. Qed.

Lemma product_value_shape : forall Gamma A B v,
  typing Gamma v (product A B) -> value v -> exists a b, v = TPair a b.
Proof.
  intros Gamma A B v Hty Hv.
  destruct (canonical_representation raw_join_typed _ _ _ Hty Hv) as [T [HT [HF [HC Hcan]]]].
  destruct (canonical_type_head _ _ Hcan) as [h Hh].
  assert (h = h_sigma) by (eapply raw_head; [exact HC|exact Hh|reflexivity]).
  subst h; inversion Hcan; subst; cbn [term_head] in Hh; try discriminate; eauto.
Qed.

Definition named_size t := nameless.DBParallelBase.tsize (encode [] t).

Section EndlessEmpty.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable preserve : forall Gamma t u A, typing Gamma t A -> step t u -> typing Gamma u A.
Variable normalize : forall t A, typing empty_ctx t A -> exists v, eval t v /\ value v.

Lemma normal_value : forall t A,
  typing empty_ctx t A -> step_normal t -> value t.
Proof.
  intros t A Ht Hn. destruct (progress_from_conversion raw_join_typed _ _ _ Ht eq_refl) as [Hv|[u Hu]];
    [exact Hv|exfalso;eapply Hn;eassumption].
Qed.

Lemma normal_endless_empty : forall t A,
  typing empty_ctx A (TSort 0) -> step_normal t -> ~ typing empty_ctx t (endless_type A).
Proof.
  induction t using (well_founded_induction (well_founded_ltof _ named_size)).
  intros A HA Hnormal Ht.
  assert (Hrow : row_view empty_ctx TUnitT (TApp (nonempty_def A) TUnit) (nonempty_rows A)).
  { constructor.
    - now apply nonempty_rows_typing.
    - apply def_application; [exact weaken|apply ty_unitT;exact wf_nil| |apply ty_unit;exact wf_nil].
      exact (proj1 (proj2 (list_definitions_from_weakening weaken _ _ HA))).
    - apply unit_signature_application. }
  destruct (canonical_named_from_rules weaken preserve normalize _ _ _ _ _ _ Ht Hrow)
    as [name [D [n [xs [Hnth [He Hxs]]]]]].
  destruct n as [|[|n]]; cbn [nonempty_rows nth_error] in Hnth; try discriminate.
  inversion Hnth; subst name D.
  pose proof (normal_evaluation _ _ Hnormal He) as E; subst t.
  assert (Hxsnormal : step_normal xs) by (eapply normal_pair_snd, normal_in; exact Hnormal).
  assert (Hendless : typing empty_ctx (endless_type A) (TSort 0)).
  { apply close_at_formation; [apply ty_unitT;exact wf_nil| | |apply ty_unit;exact wf_nil];
      exact (proj1 (proj2 (list_definitions_from_weakening weaken _ _ HA))). }
  assert (Hprod : typing empty_ctx xs (product A (endless_type A))).
  { eapply ty_conv; [exact Hxs|exact (product_formation weaken _ _ _ 0 0 HA Hendless)|].
    apply cons_payload_product. }
  destruct (product_value_shape _ _ _ _ Hprod (normal_value _ _ Hprod Hxsnormal)) as [a [tail ->]].
  assert (Htail : typing empty_ctx tail (endless_type A)).
  { eapply preserve with (t:=TSnd (TPair a tail)).
    - exact (product_projection_typing weaken _ _ _ _ false HA Hendless Hprod).
    - apply st_root;reflexivity. }
  eapply H with (y:=tail); [|exact HA|eapply normal_pair_snd;exact Hxsnormal|exact Htail].
  unfold ltof, named_size. cbn [encode nameless.DBParallelBase.tsize enum_position]. lia.
Qed.

Theorem endless_from_rules :
  (forall t A, typing empty_ctx t A -> exists v, typing empty_ctx v A /\ step_normal v) ->
  forall A, typing empty_ctx A (TSort 0) -> forall x, ~ typing empty_ctx x (endless_type A).
Proof.
  intros normalizer A HA x Hx. destruct (normalizer _ _ Hx) as [v [Hv Hn]].
  exact (normal_endless_empty v A HA Hn Hv).
Qed.
End EndlessEmpty.
