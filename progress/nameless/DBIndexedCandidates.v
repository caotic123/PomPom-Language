(* Positive fixed points whose recursive references range over computable
   indices. No decidability or proof irrelevance for index validity is used. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBPositiveCandidates.
Import Full.

Lemma intersection_candidate : forall R S,
  candidate R -> candidate S -> candidate (fun t => R t /\ S t).
Proof.
  intros R S CR CS; constructor.
  - intros t [H _]; exact (candidate_normalizing CR H).
  - intros t u [HR HS] H; split; eapply candidate_reduct; eassumption.
  - intros t HN HR; split; apply candidate_neutral; try eassumption;
      intros u HU; apply (HR u HU).
Qed.

Definition rolled_elements (R : term -> Prop) :=
  saturated (fun z => exists u, z = TIn u /\ R u).
Lemma rolled_elements_candidate : forall R, candidate R -> candidate (rolled_elements R).
Proof.
  intros R CR; apply saturated_candidate; intros z [u [-> HU]].
  apply full_SN_in; exact (candidate_normalizing CR HU).
Qed.
Lemma rolled_elements_equiv : forall R S,
  predicate_equiv R S -> predicate_equiv (rolled_elements R) (rolled_elements S).
Proof.
  intros R S HE t; split; apply saturated_monotone; intros z [u [-> HU]];
    exists u; split; [reflexivity|now apply HE|reflexivity|now apply HE].
Qed.

Module Indexed.
Section FixedPoint.
Context {Index : Type}.
Variable valid : Index -> Prop.
Definition family := Index -> term -> Prop.
Definition candidates (X : family) := forall i, valid i -> candidate (X i).
Definition inclusion (X Y : family) := forall i, valid i -> forall t, X i t -> Y i t.
Definition prefixed (F : family -> family) (X : family) :=
  forall i, valid i -> forall t, F X i t -> X i (TIn t).
Definition mu (F : family -> family) i t :=
  forall X, candidates X -> prefixed F X -> X i t.

Variable F : family -> family.
Hypothesis F_monotone : forall X Y, inclusion X Y -> inclusion (F X) (F Y).
Hypothesis F_normalizing : forall i, valid i -> forall t,
  F (fun _ => full_SN) i t -> full_SN t.

Lemma normalizing_prefixed : prefixed F (fun _ => full_SN).
Proof. intros i Hi t H; apply full_SN_in; eapply F_normalizing; eassumption. Qed.
Theorem mu_candidate : candidates (mu F).
Proof.
  intros i Hi; constructor.
  - intros t H; exact (H (fun _ => full_SN)
      (fun _ _ => normalizing_candidate) normalizing_prefixed).
  - intros t u H HR X CX HX; exact (candidate_reduct (CX i Hi) (H X CX HX) HR).
  - intros t HN HR X CX HX; apply (candidate_neutral (CX i Hi) HN).
    intros u HU; exact (HR u HU X CX HX).
Qed.
Theorem mu_fold : prefixed F (mu F).
Proof.
  intros i Hi t HT X CX HX; apply HX; [exact Hi|].
  eapply F_monotone; [|exact Hi|exact HT].
  intros j Hj u Hu; exact (Hu X CX HX).
Qed.
Theorem mu_induction : forall X,
  candidates X -> prefixed F X -> inclusion (mu F) X.
Proof. intros X CX HX i Hi t H; exact (H X CX HX). Qed.
Definition rolled (X : family) i :=
  saturated (fun z => exists u, z = TIn u /\ F X i u).
Lemma rolled_mu_candidate : candidates (rolled (mu F)).
Proof.
  intros i Hi; apply saturated_candidate; intros t [u [-> HU]].
  apply full_SN_in; apply (F_normalizing i Hi).
  eapply F_monotone; [|exact Hi|exact HU].
  intros j Hj x HX; exact (candidate_normalizing (mu_candidate j Hj) HX).
Qed.
Lemma rolled_mu_inclusion : inclusion (rolled (mu F)) (mu F).
Proof.
  intros i Hi t H; apply (H (mu F i) (mu_candidate i Hi)).
  intros z [u [-> Hu]]; now apply mu_fold.
Qed.
Theorem mu_unfold : inclusion (mu F) (rolled (mu F)).
Proof.
  apply mu_induction; [exact rolled_mu_candidate|].
  intros i Hi t HT; apply saturated_intro; exists t; split; [reflexivity|].
  eapply F_monotone; [exact rolled_mu_inclusion|exact Hi|exact HT].
Qed.

Theorem mu_index_equiv : forall i j,
  valid i -> valid j ->
  (forall X, candidates X -> predicate_equiv (F X i) (F X j)) ->
  predicate_equiv (mu F i) (mu F j).
Proof.
  intros i j Hi Hj HE t; split; intro HT.
  - pose proof (mu_unfold i Hi t HT) as HU.
    apply (HU (mu F j) (mu_candidate j Hj)).
    intros z [u [-> HF]]; apply mu_fold; [exact Hj|].
    apply (HE _ mu_candidate u); exact HF.
  - pose proof (mu_unfold j Hj t HT) as HU.
    apply (HU (mu F i) (mu_candidate i Hi)).
    intros z [u [-> HF]]; apply mu_fold; [exact Hi|].
    apply (HE _ mu_candidate u); exact HF.
Qed.

(* Refinements support induction motives which additionally retain the
   original data membership required by dependent recursive calls. *)
Theorem mu_refinement : forall X,
  candidates X -> prefixed F (fun i t => mu F i t /\ X i t) ->
  inclusion (mu F) X.
Proof.
  intros X CX HX i Hi t HT.
  assert (HC : candidates (fun i t => mu F i t /\ X i t)).
  { intros j Hj; apply intersection_candidate; [apply mu_candidate|apply CX]; exact Hj. }
  exact (proj2 (mu_induction _ HC HX i Hi t HT)).
Qed.

(* Extending a partial family avoids choosing inhabitants of [valid i]. *)
Definition totalize (X : family) i t := full_SN t /\ (valid i -> X i t).
Lemma totalize_candidate : forall X, candidates X -> forall i, candidate (totalize X i).
Proof.
  intros X CX i; constructor.
  - intros t [H _]; exact H.
  - intros t u [HS HX] HR; split; [exact (Acc_inv HS HR)|].
    intro Hi; exact (candidate_reduct (CX i Hi) (HX Hi) HR).
  - intros t HN HR; split.
    + constructor; intros u HU; exact (proj1 (HR u HU)).
    + intro Hi; apply (candidate_neutral (CX i Hi) HN).
      intros u HU; exact (proj2 (HR u HU) Hi).
Qed.
Lemma totalize_equiv : forall X, candidates X -> forall i,
  valid i -> predicate_equiv (totalize X i) (X i).
Proof.
  intros X CX i Hi t; split; [intros [_ H]; exact (H Hi)|].
  intro H; split; [exact (candidate_normalizing (CX i Hi) H)|auto].
Qed.

Theorem mu_functor_equiv : forall G,
  (forall X, candidates X -> forall i, valid i -> predicate_equiv (F X i) (G X i)) ->
  forall i, predicate_equiv (mu F i) (mu G i).
Proof.
  intros G HE i t; split; intros HT X CX HX; apply (HT X CX).
  - intros j Hj u Hu; apply HX; [exact Hj|now apply (HE X CX j Hj u)].
  - intros j Hj u Hu; apply HX; [exact Hj|now apply (HE X CX j Hj u)].
Qed.
End FixedPoint.

Theorem mu_valid_equiv : forall {Index : Type} (valid valid' : Index -> Prop) F,
  (forall i, valid i <-> valid' i) ->
  forall i, predicate_equiv (mu valid F i) (mu valid' F i).
Proof.
  intros Index valid valid' F HE i t; split; intros HT X CX HX; apply (HT X).
  - intros j Hj; apply CX, HE; exact Hj.
  - intros j Hj u Hu; apply HX; [apply HE; exact Hj|exact Hu].
  - intros j Hj; apply CX, HE; exact Hj.
  - intros j Hj u Hu; apply HX; [apply HE; exact Hj|exact Hu].
Qed.

Theorem mu_model_equiv : forall {Index : Type} (valid valid' : Index -> Prop) F G,
  (forall i, valid i <-> valid' i) ->
  (forall X, candidates valid X -> forall i, valid i -> predicate_equiv (F X i) (G X i)) ->
  forall i, predicate_equiv (mu valid F i) (mu valid' G i).
Proof.
  intros Index valid valid' F G HV HF i t.
  pose proof (mu_functor_equiv valid F G HF i t) as HE.
  pose proof (mu_valid_equiv valid valid' G HV i t) as HI; tauto.
Qed.
End Indexed.

Print Assumptions Indexed.mu_candidate.
Print Assumptions Indexed.mu_unfold.
Print Assumptions Indexed.mu_refinement.
Print Assumptions Indexed.mu_functor_equiv.
