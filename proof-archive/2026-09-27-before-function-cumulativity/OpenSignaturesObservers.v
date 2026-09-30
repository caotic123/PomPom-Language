From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesExampleTyping OpenSignaturesCaseTyping.
Import ListNotations.

Local Ltac free_support :=
  cbn [free_vars] in *;
  repeat first [rewrite in_app_iff in *|rewrite in_remove_iff in *];
  cbn [In] in *; intuition congruence.

Lemma row_branches_fresh : forall IT rs x,
  ~ In x (free_vars IT) -> ~ In x (free_vars (row_tuple rs)) ->
  ~ In x (free_vars (row_branches IT rs)).
Proof.
  intros IT rs x HIT Hr. unfold row_branches. cbn [free_vars].
  rewrite row_enum_closed. free_support.
Qed.
Lemma handler_motive_fresh : forall IT rs X Y x,
  ~ In x (free_vars IT) -> ~ In x (free_vars (row_tuple rs)) ->
  ~ In x (free_vars X) -> ~ In x (free_vars Y) ->
  ~ In x (free_vars (handler_motive IT rs X Y)).
Proof.
  intros IT rs X Y x HIT Hr HX HY.
  pose proof (row_branches_fresh IT rs x HIT Hr) as Hb.
  unfold handler_motive. free_support.
Qed.
Lemma row_map_fresh : forall k IT rs X Y hs x,
  ~ In x (free_vars IT) -> ~ In x (free_vars (row_tuple rs)) ->
  ~ In x (free_vars X) -> ~ In x (free_vars Y) ->
  ~ In x (free_vars (tuple hs)) -> ~ In x (free_vars (row_map k IT rs X Y hs)).
Proof.
  intros k IT rs X Y hs x HIT Hr HX HY Hhs.
  pose proof (handler_motive_fresh IT rs X Y x HIT Hr HX HY) as HP.
  unfold row_map. cbn [free_vars]. rewrite row_enum_closed. free_support.
Qed.

Lemma signature_fresh : forall rs x,
  ~ In x (free_vars (row_tuple rs)) ->
  ~ In x (free_vars (unit_signature rs)).
Proof.
  intros rs x Hr.
  pose proof (row_branches_fresh TUnitT rs x ltac:(cbn;tauto) Hr) as Hb.
  unfold unit_signature, signature, row_code. cbn [free_vars]. rewrite row_enum_closed.
  free_support.
Qed.
Lemma cons_code_fresh : forall A x, ~ In x (free_vars A) ->
  ~ In x (free_vars (cons_code A)).
Proof. intros A x HA; unfold cons_code; free_support. Qed.
Lemma list_def_fresh : forall A x, ~ In x (free_vars A) ->
  ~ In x (free_vars (list_def A)).
Proof.
  intros A x HA. apply signature_fresh. unfold list_rows, row_tuple; cbn [map snd tuple free_vars].
  pose proof (cons_code_fresh A x HA). free_support.
Qed.
Lemma nonempty_def_fresh : forall A x, ~ In x (free_vars A) ->
  ~ In x (free_vars (nonempty_def A)).
Proof.
  intros A x HA. apply signature_fresh. unfold nonempty_rows, row_tuple; cbn [map snd tuple free_vars].
  pose proof (cons_code_fresh A x HA). free_support.
Qed.
Lemma list_type_fresh : forall A x, ~ In x (free_vars A) ->
  ~ In x (free_vars (list_type A)).
Proof.
  intros A x HA; pose proof (list_def_fresh A x HA).
  unfold list_type, CloseAt. free_support.
Qed.

Section ObserverTyping.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma case_function_typing : forall Gamma k IT F G i Y rs hs x,
  close_input Gamma IT F G i -> row_view Gamma IT (TApp F i) rs ->
  typing Gamma Y (TSort k) ->
  Forall2 (fun entry h => typing Gamma h
    (arrow (TInterp IT (snd entry) (carrier IT G)) Y)) rs hs ->
  ~ In x (free_vars IT) -> ~ In x (free_vars F) -> ~ In x (free_vars G) ->
  ~ In x (free_vars i) -> ~ In x (free_vars Y) ->
  ~ In x (free_vars (row_tuple rs)) -> ~ In x (free_vars (tuple hs)) ->
  typing Gamma (TLam x (case_term k IT F G i Y rs hs (TVar x)))
    (arrow (CloseAt IT F G i) Y).
Proof.
  intros Gamma k IT F G i Y rs hs x Hinput Hview HY Hhs
    HxIT HxF HxG Hxi HxY Hxrs Hxtuple.
  destruct Hinput as [HIT [HF [HG Hi]]].
  destruct Hview as [rs Hrows HD Hconv].
  assert (HC : typing Gamma (CloseAt IT F G i) (TSort 0)) by
    (now apply close_at_formation).
  assert (HX : typing Gamma (carrier IT G) (Family IT)) by (now apply ty_close).
  assert (HB : typing Gamma (payload IT F G i) (TSort 0)) by
    (apply payload_formation; [exact weaken|repeat split;assumption]).
  pose (b := row_map k IT rs (carrier IT G) Y hs).
  assert (Hb : typing Gamma b (arrow (payload IT F G i) Y)).
  { eapply ty_conv.
    - apply row_map_typing; [exact weaken|exact Hrows|exact HX|exact HY|].
      apply row_handlers_tuple; [exact weaken|exact Hrows|exact HX|exact HY|exact Hhs].
    - apply arrow_formation; [exact weaken|exact HB|exact HY].
    - apply arrow_conversion; [|apply cv_refl].
      apply cv_compatible, cp_TInterp; try apply cv_refl. now apply cv_sym. }
  assert (Hxb : ~ In x (free_vars b)).
  { apply row_map_fresh; try assumption. unfold carrier; free_support. }
  unfold case_term; fold b.
  pose (q := fresh [IT; F; G; i; Y; row_tuple rs; tuple hs; TVar x; b]). fold q.
  assert (HqY : ~ In q (free_vars Y)) by (apply fresh_not_free; cbn; tauto).
  assert (HxQ : ~ In x (free_vars (TLam q Y))) by free_support.
  eapply arrow_intro_fresh; [exact weaken|exact HC|exact HY|].
  intros z Hz Havoid.
  change (typing (extend Gamma z (CloseAt IT F G i))
    (TCloseCase k (subst (TVar z) x IT) (subst (TVar z) x F)
      (subst (TVar z) x G) (subst (TVar z) x i)
      (subst (TVar z) x (TLam q Y)) (subst (TVar z) x b)
      (if Nat.eqb x x then TVar z else TVar x)) Y).
  rewrite Nat.eqb_refl, !subst_fresh by assumption.
  apply close_case_constant_typing; [exact weaken| | |exact HqY| |].
  - repeat split; eapply weaken; eassumption.
  - eapply weaken; eassumption.
  - eapply weaken; eassumption.
  - apply ty_var; [eapply wf_cons; eauto using typing_context|apply lookup_extend_same].
Qed.
End ObserverTyping.

Section ConcreteObservers.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.

Lemma cons_payload_product : forall A X,
  conv (TInterp TUnitT (cons_code A) X) (product A (TApp X TUnit)).
Proof.
  intros A X. unfold cons_code.
  pose (z := fresh [TUnitT; A; TLam (fresh [A]) (TIVar TUnit); X]).
  eapply cv_trans; [apply cv_step, st_root;reflexivity|]. fold z.
  eapply cv_trans with (u:=TSigma z A (TApp X TUnit)).
  - apply cv_compatible, cp_TSigma; [apply cv_refl|].
    eapply cv_trans with (u:=TInterp TUnitT (TIVar TUnit) X).
    + apply cv_compatible, cp_TInterp; try apply cv_refl.
      apply cv_step, st_root; reflexivity.
    + apply cv_step, st_root;reflexivity.
  - apply cv_alpha, constant_sigma_alpha.
    + cbn [free_vars]; rewrite app_nil_r. apply fresh_not_free; cbn;tauto.
    + apply fresh_not_free; cbn;tauto.
Qed.
Lemma nonempty_payload_projection : forall Gamma A p,
  typing Gamma A (TSort 0) ->
  typing Gamma (TLam p (TFst (TVar p)))
    (arrow (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) A) /\
  typing Gamma (TLam p (TSnd (TVar p)))
    (arrow (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) (list_type A)).
Proof.
  intros Gamma A p HA.
  pose proof (typing_context _ _ _ HA) as Hctx.
  destruct (list_definitions_from_weakening weaken Gamma A HA) as [HL [HN HT]].
  assert (Hlist : typing Gamma (list_type A) (TSort 0)) by
    (apply close_at_formation; auto using ty_unitT, ty_unit).
  assert (Hpayload : typing Gamma
    (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) (TSort 0)).
  { apply ty_interp; [now apply ty_unitT|now apply cons_code_typing|apply ty_close; auto using ty_unitT]. }
  split; eapply arrow_intro_fresh; [exact weaken|exact Hpayload|exact HA| |exact weaken|exact Hpayload|exact Hlist|];
    intros z Hz Havoid;
    cbn [subst substitute]; rewrite Nat.eqb_refl.
  all: pose proof (weaken _ _ _ _ _ _ Hz HA Hpayload) as HA'.
  all: pose proof (weaken _ _ _ _ _ _ Hz Hlist Hpayload) as HL'.
  all: assert (HP : typing
    (extend Gamma z (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))))
    (product A (list_type A)) (TSort 0)) by
    (exact (product_formation weaken _ _ _ 0 0 HA' HL')).
  all: assert (Hzp : typing
    (extend Gamma z (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))))
    (TVar z) (product A (list_type A))).
  all: try solve [eapply ty_conv; [apply ty_var; [eapply wf_cons;eassumption|apply lookup_extend_same]|exact HP|apply cons_payload_product]].
  - eapply ty_fst; [exact HP|exact Hzp].
  - pose proof (@ty_snd _ (fresh [A; list_type A]) A (list_type A) (TVar z) 0 HP Hzp) as Hsnd.
    rewrite subst_fresh in Hsnd by (apply fresh_not_free; cbn;auto). exact Hsnd.
Qed.
Lemma nonempty_case_function : forall Gamma A Y x h,
  typing Gamma A (TSort 0) -> typing Gamma Y (TSort 0) ->
  typing Gamma h (arrow (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) Y) ->
  ~ In x (free_vars A) -> ~ In x (free_vars Y) -> ~ In x (free_vars h) ->
  typing Gamma (TLam x (case_term 0 TUnitT (nonempty_def A) (list_def A) TUnit
    Y (nonempty_rows A) [h] (TVar x))) (arrow (nonempty_type A) Y).
Proof.
  intros Gamma A Y x h HA HY Hh HxA HxY Hxh.
  pose proof (typing_context _ _ _ HA) as Hctx.
  destruct (list_definitions_from_weakening weaken Gamma A HA) as [HL [HN HT]].
  apply case_function_typing; [exact weaken| | |exact HY| | | | | |exact HxY| |].
  - repeat split; auto using ty_unitT, ty_unit.
  - constructor.
    + now apply nonempty_rows_typing.
    + apply def_application; auto using ty_unitT, ty_unit.
    + apply unit_signature_application.
  - constructor; [exact Hh|constructor].
  - cbn; tauto.
  - now apply nonempty_def_fresh.
  - now apply list_def_fresh.
  - cbn; tauto.
  - pose proof (cons_code_fresh A x HxA). unfold nonempty_rows, row_tuple.
    cbn [tuple map snd free_vars]. free_support.
  - cbn [tuple free_vars]. free_support.
Qed.

Lemma vars_list_parameter : forall A x, In x (vars A) -> In x (vars (list_type A)).
Proof.
  intros A x H. unfold list_type, CloseAt, list_def, unit_signature, signature,
    row_code, row_branches, row_tuple, list_rows, cons_code, nil_code.
  cbn [vars map snd tuple].
  repeat first [rewrite in_app_iff|progress cbn [In]]. tauto.
Qed.
Lemma list_observer_fresh : forall A,
  ~ In (fresh [nonempty_type A; list_type A]) (free_vars A).
Proof.
  intros A Hin. apply free_vars_in_vars in Hin. apply vars_list_parameter in Hin.
  apply (fresh_id_not_in (flat_map vars [nonempty_type A; list_type A])).
  apply in_flat_map; exists (list_type A); split; [cbn;auto|exact Hin].
Qed.

Theorem observers_from_weakening : forall Gamma A,
  typing Gamma A (TSort 0) ->
  typing Gamma (head_term A) (arrow (nonempty_type A) A) /\
  typing Gamma (tail_term A) (arrow (nonempty_type A) (list_type A)).
Proof.
  intros Gamma A HA.
  pose proof (typing_context _ _ _ HA) as Hctx.
  destruct (list_definitions_from_weakening weaken Gamma A HA) as [HL [HN HT]].
  assert (Hlist : typing Gamma (list_type A) (TSort 0)) by
    (apply close_at_formation; auto using ty_unitT, ty_unit).
  split.
  - unfold head_term. apply nonempty_case_function; try assumption.
    + apply (proj1 (nonempty_payload_projection Gamma A _ HA)).
    + apply fresh_not_free; cbn;auto.
    + apply fresh_not_free; cbn;auto.
    + free_support.
  - unfold tail_term. apply nonempty_case_function; try assumption.
    + apply (proj2 (nonempty_payload_projection Gamma A _ HA)).
    + apply list_observer_fresh.
    + apply fresh_not_free; cbn;auto.
    + free_support.
Qed.
End ConcreteObservers.
