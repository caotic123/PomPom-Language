(* Fundamental computability for the complete auxiliary typing judgment. *)
From Stdlib Require Import List Arith Lia.
Require Export nameless.DBSemanticCloseCase.
Import ListNotations Full.

Lemma instantiate_lift_three : forall t rho k,
  instantiate rho (S (S (S k))) (lift 3 0 t) = lift 3 0 (instantiate rho k t).
Proof. intros; exact (instantiate_lift t rho 3 0 k ltac:(lia)). Qed.
Lemma instantiate_lift_four : forall t rho k,
  instantiate rho (S (S (S (S k)))) (lift 4 0 t) = lift 4 0 (instantiate rho k t).
Proof. intros; exact (instantiate_lift t rho 4 0 k ltac:(lia)). Qed.
Ltac solve_instantiated_derived :=
  intros; repeat progress (cbn [instantiate arrow Def Family CloseAt MuAt carrier payload total motive
    recursive_method close_case_method close_motive diagonal_motive close_ind_method mu_ind_method];
    rewrite ?instantiate_lift_one, ?instantiate_lift_two, ?instantiate_lift_three, ?instantiate_lift_four);
    reflexivity.
Lemma instantiate_arrow : forall rho k A B,
  instantiate rho k (arrow A B) = arrow (instantiate rho k A) (instantiate rho k B).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_Def : forall rho k IT, instantiate rho k (Def IT) = Def (instantiate rho k IT).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_Family : forall rho k IT, instantiate rho k (Family IT) = Family (instantiate rho k IT).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_CloseAt : forall rho k IT D G i,
  instantiate rho k (CloseAt IT D G i) = CloseAt (instantiate rho k IT) (instantiate rho k D) (instantiate rho k G) (instantiate rho k i).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_MuAt : forall rho k IT D i,
  instantiate rho k (MuAt IT D i) = MuAt (instantiate rho k IT) (instantiate rho k D) (instantiate rho k i).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_payload : forall rho k IT D G i,
  instantiate rho k (payload IT D G i) = payload (instantiate rho k IT) (instantiate rho k D) (instantiate rho k G) (instantiate rho k i).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_motive : forall rho k IT X,
  instantiate rho k (motive IT X) = motive (instantiate rho k IT) (instantiate rho k X).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_recursive_method : forall rho k IT X P,
  instantiate rho k (recursive_method IT X P) = recursive_method (instantiate rho k IT) (instantiate rho k X) (instantiate rho k P).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_close_case_method : forall rho k IT D G i Q,
  instantiate rho k (close_case_method IT D G i Q) =
    close_case_method (instantiate rho k IT) (instantiate rho k D) (instantiate rho k G) (instantiate rho k i) (instantiate rho k Q).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_close_motive : forall rho k IT G,
  instantiate rho k (close_motive IT G) = close_motive (instantiate rho k IT) (instantiate rho k G).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_close_ind_method : forall rho k IT G P,
  instantiate rho k (close_ind_method IT G P) = close_ind_method (instantiate rho k IT) (instantiate rho k G) (instantiate rho k P).
Proof. solve_instantiated_derived. Qed.
Lemma instantiate_mu_ind_method : forall rho k IT D P,
  instantiate rho k (mu_ind_method IT D P) = mu_ind_method (instantiate rho k IT) (instantiate rho k D) (instantiate rho k P).
Proof. solve_instantiated_derived. Qed.
#[local] Hint Rewrite instantiate_arrow instantiate_Def instantiate_Family instantiate_CloseAt instantiate_MuAt
  instantiate_payload instantiate_motive instantiate_recursive_method instantiate_close_case_method
  instantiate_close_motive instantiate_close_ind_method instantiate_mu_ind_method instantiate_subst_zero : semantic_inst.
Lemma semantic_formed : forall A k, semantic_value A (TSort k) -> semantic_type A.
Proof. intros A k H; exists k; now apply semantic_value_sort. Qed.
#[local] Hint Resolve semantic_formed semantic_type_normalizing : semantic.
#[local] Hint Resolve semantic_sort semantic_unit_type semantic_unit_value semantic_uid_type semantic_tag
  semantic_enumu_type semantic_nile semantic_conse semantic_enumt semantic_zero semantic_succ semantic_epi semantic_switch
  semantic_idesc semantic_ivar semantic_i1 semantic_ibot semantic_iprod semantic_ipi semantic_isig semantic_ichoice
  semantic_interp semantic_mu semantic_in_mu semantic_iall semantic_hyps semantic_ind
  semantic_close semantic_in_close semantic_close_case semantic_close_ind : semantic.
Ltac solve_small_interpretation :=
  apply small_type_canonical; apply small_semantic_type; assumption.

Theorem semantic_fundamental : forall Gamma t A, typing Gamma t A ->
  forall rho, semantic_environment Gamma rho -> semantic_value (instantiate rho 0 t) (instantiate rho 0 A).
Proof.
  intros Gamma t A HT; induction HT; intros rho Henv.
  all: repeat match goal with
    IH : forall rho, semantic_environment ?G rho -> semantic_value _ _,
    HE : semantic_environment ?G ?r |- _ => specialize (IH r HE)
    end.
  all: autorewrite with semantic_inst in *.
  all: cbn [instantiate] in *.
  { change (semantic_value (instantiate rho 0 (TVar n)) (instantiate rho 0 (lift (S n) 0 A))).
    eapply semantic_environment_variable; eassumption. }
  { apply semantic_sort. }
  { apply semantic_value_sort, semantic_pi; [now apply semantic_value_sort|].
    intros a Ha; apply semantic_value_sort; rewrite instantiate_extension.
    apply IHHT2, semantic_environment_extend; assumption. }
  { apply semantic_value_sort, semantic_sigma; [now apply semantic_value_sort|].
    intros a Ha; apply semantic_value_sort; rewrite instantiate_extension.
    apply IHHT2, semantic_environment_extend; assumption. }
  { apply semantic_lambda; [eauto with semantic|].
    intros a Ha; rewrite !instantiate_extension.
    apply IHHT2, semantic_environment_extend; assumption. }
  { eapply semantic_application; [eassumption|eassumption|eauto with semantic]. }
  { eapply semantic_pair; [eauto with semantic|eassumption|eassumption]. }
  { eapply semantic_fst; eassumption. }
  { eapply semantic_snd; [eassumption|eauto with semantic]. }
  { eapply semantic_value_conversion; [eassumption|eauto with semantic|now apply conversion_instantiate]. }
  { eapply semantic_cumulative; eassumption. }
  all: try solve [eauto 4 with semantic].
  all: try solve [eauto 4 using small_type_canonical, small_semantic_type with semantic].
  all: try solve [eapply semantic_function_cumulative; [eassumption|eauto with semantic|constructor; now apply universe_le_instantiate]].
Qed.

Theorem semantic_environment_inhabited : forall Gamma, wf Gamma ->
  exists rho, semantic_environment Gamma rho.
Proof.
  intros Gamma H; induction H.
  - exists (fun _ => TVar 0); apply semantic_environment_empty.
  - destruct IHwf as [rho HE].
    exists (extend_substitution (TVar 0) rho); apply semantic_environment_extend; [exact HE|].
    apply semantic_variable; eapply semantic_formed with (k:=k).
    exact (semantic_fundamental _ _ _ H0 rho HE).
Qed.

Print Assumptions semantic_fundamental.
Print Assumptions semantic_environment_inhabited.

Theorem typing_full_normalization : forall Gamma t A, typing Gamma t A -> full_SN t.
Proof.
  intros Gamma t A HT.
  destruct (semantic_environment_inhabited _ (typing_context _ _ _ HT)) as [rho HE].
  apply (instantiation_reflects_normalization t rho 0).
  exact (proj1 (semantic_value_normalizing _ _ (semantic_fundamental _ _ _ HT rho HE))).
Qed.

Print Assumptions typing_full_normalization.
