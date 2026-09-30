(* Candidate closure and positive fixed points for description-based data. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export FullReducibilityWork.
Import Full.

Definition saturated (seed : term -> Prop) t :=
  forall R, candidate R -> (forall u, seed u -> R u) -> R t.
Lemma saturated_intro : forall seed t, seed t -> saturated seed t.
Proof. intros seed t H R HR HI; now apply HI. Qed.
Lemma saturated_elim : forall seed R, candidate R ->
  (forall u, seed u -> R u) -> forall t, saturated seed t -> R t.
Proof. intros seed R HR HI t H; exact (H R HR HI). Qed.
Theorem saturated_candidate : forall seed,
  (forall t, seed t -> full_SN t) -> candidate (saturated seed).
Proof.
  intros seed HS; constructor.
  - intros t H; exact (H full_SN normalizing_candidate HS).
  - intros t u H HR R CR HI; apply (candidate_reduct CR (H R CR HI) HR).
  - intros t HN HR R CR HI; apply (candidate_neutral CR HN).
    intros u HU; exact (HR u HU R CR HI).
Qed.
Lemma saturated_monotone : forall seed seed',
  (forall t, seed t -> seed' t) -> forall t, saturated seed t -> saturated seed' t.
Proof. intros seed seed' H t HT R CR HI; apply (HT R CR); auto. Qed.
Lemma saturated_least : forall seed R,
  candidate R -> (forall t, seed t -> R t) ->
  forall t, saturated seed t -> R t.
Proof. exact saturated_elim. Qed.
Lemma full_SN_in : forall x, full_SN x -> full_SN (TIn x).
Proof.
  intros x H; induction H as [x H IH]; constructor; intros u HU.
  inversion HU; subst; [discriminate|now apply IH].
Qed.

Section PositiveFixedPoint.
Context {Index : Type}.
Definition family := Index -> term -> Prop.
Definition family_candidate (X : family) := forall i, candidate (X i).
Definition family_inclusion (X Y : family) := forall i t, X i t -> Y i t.
Variable F : family -> family.
Hypothesis F_monotone : forall X Y, family_inclusion X Y -> family_inclusion (F X) (F Y).
Hypothesis F_normalizing : forall i t, F (fun _ => full_SN) i t -> full_SN t.
Definition prefixed (X : family) := forall i t, F X i t -> X i (TIn t).
Definition positive_mu i t := forall X, family_candidate X -> prefixed X -> X i t.

Lemma normalizing_prefixed : prefixed (fun _ => full_SN).
Proof. intros i t H; apply full_SN_in; now apply F_normalizing with i. Qed.
Theorem positive_mu_candidate : family_candidate positive_mu.
Proof.
  intros i; constructor.
  - intros t H; exact (H (fun _ => full_SN) (fun _ => normalizing_candidate) normalizing_prefixed).
  - intros t u H HR X CX HX; exact (candidate_reduct (CX i) (H X CX HX) HR).
  - intros t HN HR X CX HX; apply (candidate_neutral (CX i) HN).
    intros u HU; exact (HR u HU X CX HX).
Qed.
Theorem positive_mu_fold : prefixed positive_mu.
Proof.
  intros i t HT X CX HX; apply HX; eapply F_monotone; [|exact HT].
  intros j u Hu; exact (Hu X CX HX).
Qed.
Theorem positive_mu_induction : forall X,
  family_candidate X -> prefixed X -> family_inclusion positive_mu X.
Proof. intros X CX HX i t H; exact (H X CX HX). Qed.
Definition rolled (X : family) i t := saturated (fun z => exists u, z = TIn u /\ F X i u) t.
Lemma rolled_mu_candidate : family_candidate (rolled positive_mu).
Proof.
  intros i; apply saturated_candidate; intros t [u [-> HU]].
  apply full_SN_in, F_normalizing with i.
  eapply F_monotone; [|exact HU].
  intros j x HX; exact (candidate_normalizing (positive_mu_candidate j) HX).
Qed.
Lemma rolled_mu_inclusion : family_inclusion (rolled positive_mu) positive_mu.
Proof.
  intros i t H; apply (H (positive_mu i) (positive_mu_candidate i)).
  intros z [u [-> Hu]]; now apply positive_mu_fold.
Qed.
Theorem positive_mu_unfold : family_inclusion positive_mu (rolled positive_mu).
Proof.
  apply positive_mu_induction; [exact rolled_mu_candidate|].
  intros i t HT; apply saturated_intro; exists t; split; [reflexivity|].
  eapply F_monotone; [exact rolled_mu_inclusion|exact HT].
Qed.
End PositiveFixedPoint.

Print Assumptions saturated_candidate.
Print Assumptions positive_mu_candidate.
Print Assumptions positive_mu_fold.
Print Assumptions positive_mu_unfold.
