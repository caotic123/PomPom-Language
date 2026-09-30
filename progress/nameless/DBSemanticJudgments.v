(* The semantic judgment used by the typing fundamental theorem. *)
From Stdlib Require Import Lia.
Require Export nameless.DBSemanticBinders.
Import Full.

Definition semantic_value t A := exists n, calculus_value n t A.
Definition semantic_type A := exists n, calculus_type n A.
Lemma semantic_value_normalizing : forall t A, semantic_value t A -> full_SN t /\ full_SN A.
Proof.
  intros t A [n [R [HT Ht]]]; split;
    [exact (candidate_normalizing (calculus_interp_candidate _ _ _ HT) Ht)
    |exact (type_interp_normalizing _ _ _ HT)].
Qed.
Lemma semantic_type_normalizing : forall A, semantic_type A -> full_SN A.
Proof. intros A [n HA]; exact (candidate_normalizing (calculus_type_candidate n) HA). Qed.
Lemma semantic_value_type : forall t A, semantic_value t A -> semantic_type A.
Proof. intros t A [n [R [HT Ht]]]; exists n,R; exact HT. Qed.
Lemma semantic_value_member : forall t A n R,
  semantic_value t A -> calculus_interp n A R -> R t.
Proof.
  intros t A n R [m [S [HS Ht]]] HR.
  apply (calculus_interp_unique _ _ _ _ _ _ HS HR (cv_refl _)); exact Ht.
Qed.
Lemma semantic_value_from_member : forall t A n R,
  calculus_interp n A R -> R t -> semantic_value t A.
Proof. intros; exists n,R; auto. Qed.
Lemma semantic_value_relevel : forall t A,
  semantic_value t A -> forall n, calculus_type n A -> calculus_value n t A.
Proof.
  intros t A H n HA; exists (calculus_elements n A); split;
    [now apply calculus_interp_canonical|eapply semantic_value_member; [exact H|now apply calculus_interp_canonical]].
Qed.
Lemma semantic_value_conversion : forall t A B,
  semantic_value t A -> semantic_type B -> conv A B -> semantic_value t B.
Proof.
  intros t A B [n [R [HT Ht]]] HB HC; exists n,R; split; [|exact Ht].
  eapply type_interp_conversion; [exact HT|now apply semantic_type_normalizing|exact HC].
Qed.
Lemma semantic_value_sort : forall A k, semantic_value A (TSort k) <-> calculus_type k A.
Proof.
  intros A k; split.
  - intros [n [R [HT HA]]]; apply (proj2 (calculus_sort_view _ _ _ _ HT (cv_refl _))); exact HA.
  - intros HA; exists (S k), (calculus_type k); split; [apply calculus_sort_interp; lia|exact HA].
Qed.
Lemma semantic_variable : forall A, semantic_type A -> forall v, semantic_value (TVar v) A.
Proof.
  intros A [n [R HR]] v; exists n,R; split; [exact HR|].
  exact (candidate_variable R (calculus_interp_candidate _ _ _ HR) v).
Qed.
Lemma semantic_sort : forall k, semantic_value (TSort k) (TSort (S k)).
Proof. intros k; apply semantic_value_sort; exists (calculus_type k); apply calculus_sort_interp; lia. Qed.

Lemma semantic_pi : forall A B j k,
  calculus_type j A -> (forall a, semantic_value a A -> calculus_type k (subst a 0 B)) ->
  calculus_type (Nat.max j k) (TPi A B).
Proof.
  intros A B j k HA HB; apply calculus_pi_formation; [exact HA|].
  intros a Ha; apply HB; exists j,(calculus_elements j A); split; [now apply calculus_interp_canonical|exact Ha].
Qed.
Lemma semantic_sigma : forall A B j k,
  calculus_type j A -> (forall a, semantic_value a A -> calculus_type k (subst a 0 B)) ->
  calculus_type (Nat.max j k) (TSigma A B).
Proof.
  intros A B j k HA HB; apply calculus_sigma_formation; [exact HA|].
  intros a Ha; apply HB; exists j,(calculus_elements j A); split; [now apply calculus_interp_canonical|exact Ha].
Qed.
Lemma semantic_lambda : forall A B b,
  semantic_type (TPi A B) ->
  (forall a, semantic_value a A -> semantic_value (subst a 0 b) (subst a 0 B)) ->
  semantic_value (TLam b) (TPi A B).
Proof.
  intros A B b [n [R HT]] Hb.
  destruct (calculus_pi_components _ _ _ _ HT) as (RA & RB & HA & HE & CB & CS & HB).
  pose proof (calculus_interp_candidate _ _ _ HA) as CA.
  exists n,R; split; [exact HT|]; apply HE.
  apply dependent_lambda_computable; [exact CA|exact CB|exact CS|].
  intros a Ha.
  assert (Hba : semantic_value (subst a 0 b) (subst a 0 B)) by
    (apply Hb; exists n,RA; auto).
  eapply semantic_value_member; [exact Hba|apply HB; [exact Ha|]].
  exact (proj2 (semantic_value_normalizing _ _ Hba)).
Qed.
Lemma semantic_application : forall A B f a,
  semantic_value f (TPi A B) -> semantic_value a A -> semantic_type (subst a 0 B) ->
  semantic_value (TApp f a) (subst a 0 B).
Proof.
  intros A B f a [n [R [HT Hf]]] Ha HBtype.
  destruct (calculus_pi_components _ _ _ _ HT) as (RA & RB & HA & HE & CB & CS & HB).
  pose proof (semantic_value_member _ _ _ _ Ha HA) as Hva.
  exists n,(RB a); split.
  - apply HB; [exact Hva|now apply semantic_type_normalizing].
  - exact (proj2 (proj1 (HE f) Hf) a Hva).
Qed.
Lemma semantic_pair : forall A B a b,
  semantic_type (TSigma A B) -> semantic_value a A -> semantic_value b (subst a 0 B) ->
  semantic_value (TPair a b) (TSigma A B).
Proof.
  intros A B a b [n [R HT]] Ha Hb.
  destruct (calculus_sigma_components _ _ _ _ HT) as (RA & RB & HA & HE & CB & CS & HB).
  pose proof (semantic_value_member _ _ _ _ Ha HA) as Hva.
  exists n,R; split; [exact HT|]; apply HE.
  apply dependent_pair_computable; [exact (calculus_interp_candidate _ _ _ HA)|exact CB|exact CS|exact Hva|].
  eapply semantic_value_member; [exact Hb|apply HB; [exact Hva|]].
  exact (proj2 (semantic_value_normalizing _ _ Hb)).
Qed.
Lemma semantic_fst : forall A B p,
  semantic_value p (TSigma A B) -> semantic_value (TFst p) A.
Proof.
  intros A B p [n [R [HT Hp]]].
  destruct (calculus_sigma_components _ _ _ _ HT) as (RA & RB & HA & HE & CB & CS & HB).
  exists n,RA; split; [exact HA|exact (proj1 (proj2 (proj1 (HE p) Hp)))].
Qed.
Lemma semantic_snd : forall A B p,
  semantic_value p (TSigma A B) -> semantic_type (subst (TFst p) 0 B) ->
  semantic_value (TSnd p) (subst (TFst p) 0 B).
Proof.
  intros A B p [n [R [HT Hp]]] HBtype.
  destruct (calculus_sigma_components _ _ _ _ HT) as (RA & RB & HA & HE & CB & CS & HB).
  destruct (proj1 (HE p) Hp) as [HS [HFst HSnd]].
  exists n,(RB (TFst p)); split; [apply HB; [exact HFst|now apply semantic_type_normalizing]|exact HSnd].
Qed.
Lemma semantic_cumulative : forall A j k,
  semantic_value A (TSort j) -> j <= k -> semantic_value A (TSort k).
Proof. intros A j k HA Hjk; apply semantic_value_sort; eapply calculus_type_cumulative; [exact Hjk|now apply semantic_value_sort]. Qed.

Print Assumptions semantic_lambda.
Print Assumptions semantic_application.
Print Assumptions semantic_pair.
Print Assumptions semantic_cumulative.
