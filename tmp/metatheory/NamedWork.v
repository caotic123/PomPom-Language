From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesDeadTyping OpenSignaturesRowTyping.
Import ListNotations.

Lemma eval_transitive : forall t u v, eval t u -> eval u v -> eval t v.
Proof. intros t u v H; induction H; eauto using eval. Qed.
Lemma eval_congruence : forall C : term -> term,
  (forall t u, step t u -> step (C t) (C u)) ->
  forall t u, eval t u -> eval (C t) (C u).
Proof. intros C HC t u H; induction H; eauto using eval. Qed.
Lemma eval_conversion : forall t u, eval t u -> conv t u.
Proof. intros t u H; induction H; eauto using conv. Qed.
Lemma eval_reductions : forall t u, eval t u -> reduces t u.
Proof. intros t u H; induction H; eauto using reduces, step_reduction. Qed.

Lemma enum_value_shape : forall Gamma E v,
  typing Gamma v (TEnumT E) -> value v -> v = TEZero \/ exists n, v = TESucc n.
Proof.
  intros Gamma E v Hty Hv.
  destruct (canonical_representation raw_join_typed _ _ _ Hty Hv) as [T [HT [HF [HC Hcan]]]].
  destruct (canonical_type_head _ _ Hcan) as [h Hh].
  assert (h = h_enumt) by (eapply raw_head; [exact HC|exact Hh|reflexivity]).
  subst h; inversion Hcan; subst; cbn [term_head] in Hh; try discriminate; eauto.
Qed.

Lemma typing_succ_principal : forall Gamma t T, typing Gamma t T -> forall n,
  t = TESucc n -> exists tag E, typing Gamma tag TUId /\ typing Gamma E TEnumU /\
    typing Gamma n (TEnumT E) /\ conv (TEnumT (TConsE tag E)) T.
Proof.
  intros Gamma t T H; induction H; intros m Heq; try discriminate.
  - subst u; unfold alpha_equiv, alpha_eqb in H0; destruct t;
      cbn [alpha_eqb_in] in H0; try discriminate.
    destruct (IHtyping _ eq_refl) as [tag [E [Htag [HE [Hn HC]]]]].
    exists tag,E; repeat split; try assumption. eapply ty_alpha; eassumption.
  - destruct (IHtyping1 _ Heq) as [tag [E [Htag [HE [Hn HC]]]]].
    exists tag,E; repeat split; try assumption; eapply cv_trans; eassumption.
  - destruct (IHtyping _ Heq) as [tag [E [Htag [HE [Hn HC]]]]].
    exfalso; pose proof (raw_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - inversion Heq; subst. exists tag,E; repeat split; auto using cv_refl.
Qed.

Section NamedCanonical.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable preserve : forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A.
Variable normalize : forall t A, typing empty_ctx t A -> exists v, eval t v /\ value v.

Lemma eval_typing : forall Gamma t u A,
  typing Gamma t A -> eval t u -> typing Gamma u A.
Proof. intros; eapply typing_reduces; [exact preserve|eapply eval_reductions; eassumption|eassumption]. Qed.

Lemma enum_normal_form : forall rs t,
  typing empty_ctx t (TEnumT (row_enum rs)) ->
  exists n name D, nth_error rs n = Some (name,D) /\ eval t (enum_position n).
Proof.
  induction rs as [|[tag D] rs IH]; intros t Ht.
  - destruct (normalize _ _ Ht) as [v [He Hv]]. exfalso.
    eapply (bottom_no_value raw_join_typed); [eapply eval_typing; eassumption|exact Hv].
  - destruct (normalize _ _ Ht) as [v [He Hv]].
    assert (Hvt : typing empty_ctx v (TEnumT (row_enum ((tag,D)::rs)))) by (eapply eval_typing; eassumption).
    destruct (enum_value_shape _ _ _ Hvt Hv) as [->|[n ->]].
    + exists 0,tag,D; split; [reflexivity|exact He].
    + destruct (typing_succ_principal _ _ _ Hvt _ eq_refl) as [tag' [E [Htag [HE [Hn HC]]]]].
      apply conv_enum, conv_conse in HC; destruct HC as [_ HC].
      assert (Hn' : typing empty_ctx n (TEnumT (row_enum rs))).
      { eapply ty_conv; [exact Hn|apply ty_enumt, row_enum_typing, wf_nil|].
        apply cv_compatible, cp_TEnumT; exact HC. }
      destruct (IH _ Hn') as [m [name [C [Hm Hnm]]]].
      exists (S m),name,C; split; [exact Hm|].
      eapply eval_transitive; [exact He|].
      apply (eval_congruence TESucc); auto using st_TESucc_n.
Qed.

Lemma choice_value_shape : forall Gamma IT E D X v,
  typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
  typing Gamma D (arrow (TEnumT E) (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma v (TInterp IT (TIChoice E D) X) -> value v ->
  exists a b, v = TPair a b.
Proof.
  intros Gamma IT E D X v HIT HE HD HX Hv Hval.
  assert (HF : type_wf Gamma (TInterp IT (TIChoice E D) X))
    by (exists 0; apply ty_interp; auto using ty_ichoice).
  destruct (value_type_exposes raw_join_typed _ _ _ _ Hv HF Hval (exposes_interp_choice IT E D X))
    as [T [HC Hhead]].
  inversion HC; subst; cbn [term_head] in Hhead; try discriminate; eauto.
Qed.

Theorem canonical_named_from_rules : forall IT F G i t rs,
  typing empty_ctx t (CloseAt IT F G i) ->
  row_view empty_ctx IT (TApp F i) rs ->
  exists name D n xs,
    nth_error rs n = Some (name,D) /\
    eval t (TIn (TPair (enum_position n) xs)) /\
    typing empty_ctx xs (TInterp IT D (carrier IT G)).
Proof.
  intros IT F G i t rs Ht Hview.
  destruct (normalize _ _ Ht) as [v [Htv Hv]].
  assert (Hvt : typing empty_ctx v (CloseAt IT F G i)) by (eapply eval_typing; eassumption).
  destruct (canonical_close_from_rules weaken preserve _ _ _ _ _ Hvt Hv) as [p [-> Hp]].
  destruct (typing_in_regularity _ _ _ Hvt _ eq_refl) as [k Hform].
  destruct (typing_close_application weaken _ _ _ Hform _ _ _ _ eq_refl) as [HIT [HF [HG Hi]]].
  inversion Hview as [rs0 Hrow HD Hconv]; subst rs0.
  assert (HX : typing empty_ctx (carrier IT G) (Family IT)) by now apply ty_close.
  assert (Hbranches : typing empty_ctx (row_branches IT rs)
    (arrow (TEnumT (row_enum rs)) (TIDesc IT))).
  { apply row_branches_from_weakening; [exact weaken|exact HIT|exact (proj2 (proj2 Hrow))]. }
  assert (Hrowcode : typing empty_ctx (row_code IT rs) (TIDesc IT))
    by (apply row_code_from_weakening; assumption).
  assert (Hp' : typing empty_ctx p (TInterp IT (row_code IT rs) (carrier IT G))).
  { eapply ty_conv; [exact Hp|now apply ty_interp|now apply interp_conversion]. }
  destruct (normalize _ _ Hp') as [q [Hpq Hq]].
  assert (Hqt : typing empty_ctx q (TInterp IT (row_code IT rs) (carrier IT G)))
    by (eapply eval_typing; eassumption).
  destruct (choice_value_shape _ _ _ _ _ _ HIT (row_enum_typing _ rs wf_nil) Hbranches HX Hqt Hq)
    as [a [b ->]].
  assert (Ha : typing empty_ctx a (TEnumT (row_enum rs))).
  { eapply preserve with (t:=TFst (TPair a b)).
    - eapply interp_choice_fst; eauto using row_enum_typing, wf_nil.
    - apply red_root; reflexivity. }
  destruct (enum_normal_form _ _ Ha) as [n [name [D [Hnth Han]]]].
  assert (Hb : typing empty_ctx b
    (TInterp IT (TApp (row_branches IT rs) (TFst (TPair a b))) (carrier IT G))).
  { eapply preserve with (t:=TSnd (TPair a b)).
    - eapply interp_choice_snd; eauto using row_enum_typing, wf_nil.
    - apply red_root; reflexivity. }
  exists name,D,n,b; split; [exact Hnth|]. split.
  - eapply eval_transitive; [exact Htv|].
    apply (eval_congruence TIn); [auto using st_TIn_x|].
    eapply eval_transitive; [exact Hpq|].
    apply (eval_congruence (fun x => TPair x b)); auto using st_TPair_a.
  - eapply ty_conv; [exact Hb| |].
    + apply ty_interp; [exact HIT| |exact HX].
      destruct Hrow as [_ [_ Hcodes]]. apply Forall_forall with (x:=(name,D)) in Hcodes;
        [exact Hcodes|eapply nth_error_In;exact Hnth].
    + apply interp_conversion.
      eapply cv_trans with (u:=TApp (row_branches IT rs) (enum_position n)).
      * apply cv_compatible, cp_TApp; [apply cv_refl|].
        eapply cv_trans; [apply cv_step, st_root;reflexivity|now apply eval_conversion].
      * eapply row_branches_position; eassumption.
Qed.
End NamedCanonical.
