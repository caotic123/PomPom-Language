(* Formation of dependent operator types uses one shared binder tactic. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBPreservation.
Import ListNotations.

Lemma def_formation : forall Gamma IT,
 typing Gamma IT (TSort 0) -> typing Gamma (Def IT) (TSort 1).
Proof.
 intros Gamma IT HI. change (TSort 1) with (TSort (Nat.max 0 1)).
 apply ty_pi; [exact HI|apply ty_idesc; exact (weakening _ _ _ _ _ HI HI)].
Qed.

Lemma family_application : forall Gamma IT X i,
 typing Gamma X (Family IT) -> typing Gamma i IT -> typing Gamma (TApp X i) (TSort 0).
Proof. intros Gamma IT X i HX Hi; exact (regular_application _ _ _ _ _ HX Hi). Qed.

Ltac lift_context_types :=
 rewrite ?lift_Def, ?lift_Family, ?lift_motive, ?lift_total, ?lift_recursive_method,
   ?lift_close_motive, ?lift_close_case_method, ?lift_close_ind_method, ?lift_mu_ind_method,
   ?lift_diagonal_motive, ?lift_arrow in *;
 cbn [lift MuAt CloseAt payload carrier] in *;
 rewrite ?lift_fuse_zero in * by lia.

Ltac type_operator :=
 eauto 7 using family_application, ty_interp, ty_iall, ty_idesc, ty_enumt, def_application, smart_close,
   smart_mui, close_at_formation, mu_at_formation, payload_formation, total_formation,
   motive_formation, def_formation, family_formation, diagonal_motive_typing,
   close_motive_application, motive_application, smart_in_close, smart_in_mui.
Ltac type_sort_one :=
 first [assumption | apply ty_sort; eauto using typing_context |
   solve [type_operator] | eapply ty_cumul with (j:=0); [solve [type_operator]|lia]].
Ltac form_binder :=
 match goal with |- typing ?G (TPi ?A ?B) (TSort 1) =>
   let HA := fresh "Hdomain" in assert (HA : typing G A (TSort 1)) by type_sort_one;
   apply ty_pi with (j:=1) (k:=1); [exact HA|];
   repeat match goal with H : typing G ?t ?T |- _ =>
     let Hnew := fresh "Hlifted" in pose proof (weakening _ _ _ _ _ H HA) as Hnew;
     (* Retain the domain proof until all other facts have been lifted. *)
     first [constr_eq H HA; fail 1 | clear H]
   end;
   let Hv := fresh "Hvariable" in assert (Hv : typing (A::G) (TVar 0) (lift 1 0 A))
     by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]);
   clear HA; lift_context_types
 end.

Lemma close_motive_formation : forall Gamma IT G,
 typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
 typing Gamma (close_motive IT G) (TSort 1).
Proof.
 intros Gamma IT G HI HG. unfold close_motive.
 do 3 form_binder. type_sort_one.
Qed.

Lemma recursive_method_formation : forall Gamma IT X P,
 typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) -> typing Gamma P (motive IT X) ->
 typing Gamma (recursive_method IT X P) (TSort 1).
Proof.
 intros Gamma IT X P HI HX HP. unfold recursive_method.
 do 2 form_binder. type_sort_one.
Qed.

Lemma mu_method_formation : forall Gamma IT D P,
 typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
 typing Gamma P (motive IT (TMuI IT D)) ->
 typing Gamma (mu_ind_method IT D P) (TSort 1).
Proof.
 intros Gamma IT D P HI HD HP. unfold mu_ind_method.
 do 3 form_binder. type_sort_one.
Qed.

Lemma close_method_formation : forall Gamma IT G P,
 typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
 typing Gamma P (close_motive IT G) ->
 typing Gamma (close_ind_method IT G P) (TSort 1).
Proof.
 intros Gamma IT G P HI HG HP. unfold close_ind_method.
 do 4 form_binder. type_sort_one.
Qed.

Lemma close_case_method_formation : forall Gamma k IT F G i Q,
 typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
 typing Gamma i IT -> typing Gamma Q (TPi (CloseAt IT F G i) (TSort k)) ->
 typing Gamma (close_case_method IT F G i Q) (TSort k).
Proof.
 intros Gamma k IT F G i Q HI HF HG Hi HQ.
 pose proof (payload_formation _ _ _ _ _ HI HF HG Hi) as HA.
 unfold close_case_method. change (TSort k) with (TSort (Nat.max 0 k)).
 apply ty_pi; [exact HA|].
 pose proof (weakening _ _ _ _ _ HI HA) as HI'.
 pose proof (weakening _ _ _ _ _ HF HA) as HF'.
 pose proof (weakening _ _ _ _ _ HG HA) as HG'.
 pose proof (weakening _ _ _ _ _ Hi HA) as Hi'.
 pose proof (weakening _ _ _ _ _ HQ HA) as HQ'.
 assert (Hv : typing (payload IT F G i::Gamma) (TVar 0) (lift 1 0 (payload IT F G i)))
   by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
 lift_context_types.
 exact (regular_application _ _ _ _ _ HQ' (smart_in_close _ _ _ _ _ _ HI' HF' HG' Hi' Hv)).
Qed.

Lemma sort_codomain_formation : forall Gamma A j k,
 typing Gamma A (TSort j) ->
 typing Gamma (TPi A (TSort k)) (TSort (Nat.max j (S k))).
Proof.
 intros. apply ty_pi; [assumption|apply ty_sort; eauto using wf_cons, typing_context].
Qed.
