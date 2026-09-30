(* Canonical enumeration predicates. The empty enumeration uses the least
   candidate, so interpreting its indices does not assume consistency. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDescriptionCandidates.
Import Full.

(* Enumeration codes retain computable tails, permitting structural proofs
   for dependent products and switching even before normalization. *)
Inductive enumeration_computable : term -> Prop :=
| ec_nil : enumeration_computable TNilE
| ec_cons : forall tag E, full_SN tag -> enumeration_computable E ->
    enumeration_computable (TConsE tag E)
| ec_reduct : forall E F, enumeration_computable E -> reduction E F ->
    enumeration_computable F
| ec_neutral : forall E, neutral E ->
    (forall F, reduction E F -> enumeration_computable F) -> enumeration_computable E.

Lemma full_SN_cons_enum : forall tag E,
  full_SN tag -> full_SN E -> full_SN (TConsE tag E).
Proof. apply full_SN_binary; description_components. Qed.
Theorem enumeration_computable_normalizing : forall E,
  enumeration_computable E -> full_SN E.
Proof.
  intros E H; induction H.
  - apply normal_form_accessible; intros u HU; inversion HU; discriminate.
  - now apply full_SN_cons_enum.
  - exact (Acc_inv IHenumeration_computable H0).
  - constructor; exact H1.
Qed.
Theorem enumeration_computable_candidate : candidate enumeration_computable.
Proof. constructor; [exact enumeration_computable_normalizing|exact ec_reduct|exact ec_neutral]. Qed.

Lemma conversion_normal_reductions : forall A B n,
  conv A B -> rtc reduction A n -> normal_form n -> rtc reduction B n.
Proof.
  intros A B n HC HR HN.
  assert (HC' : conv n B) by
    (eapply cv_trans; [apply cv_sym; exact (reductions_conversion _ _ HR)|exact HC]).
  destruct (conversion_joinable _ _ HC') as [m [Hm HB]].
  pose proof (normal_reductions_identity _ _ HN Hm); now subst m.
Qed.

Lemma full_SN_succ : forall n, full_SN n -> full_SN (TESucc n).
Proof. apply full_SN_unary; description_components. Qed.
Lemma full_SN_zero : full_SN TEZero.
Proof. apply normal_form_accessible; intros u H; inversion H; discriminate. Qed.

Definition empty_elements := saturated (fun _ => False).
Definition extended_elements (R : term -> Prop) :=
  saturated (fun t => t = TEZero \/ exists n, t = TESucc n /\ R n).
Lemma empty_elements_candidate : candidate empty_elements.
Proof. apply saturated_candidate; tauto. Qed.
Lemma extended_elements_candidate : forall R,
  candidate R -> candidate (extended_elements R).
Proof.
  intros R CR; apply saturated_candidate; intros t [->|[n [-> H]]].
  - exact full_SN_zero.
  - apply full_SN_succ; exact (candidate_normalizing CR H).
Qed.
Lemma extended_elements_equiv : forall R S,
  predicate_equiv R S -> predicate_equiv (extended_elements R) (extended_elements S).
Proof.
  intros R S HE t; split; apply saturated_monotone;
    intros z [Hz|[n [Hz Hn]]]; [now left|right; exists n; split; [exact Hz|now apply HE]
      |now left|right; exists n; split; [exact Hz|now apply HE]].
Qed.
Fixpoint enum_normal_elements (E : term) : term -> Prop :=
  match E with
  | TNilE => empty_elements
  | TConsE _ tail => extended_elements (enum_normal_elements tail)
  | _ => full_SN
  end.
Lemma enum_normal_elements_candidate : forall E, candidate (enum_normal_elements E).
Proof.
  induction E; cbn [enum_normal_elements];
    auto using normalizing_candidate, empty_elements_candidate, extended_elements_candidate.
Qed.
Definition enum_elements E t := full_SN t /\
  forall n, rtc reduction E n -> normal_form n -> enum_normal_elements n t.
Theorem enum_elements_candidate : forall E, candidate (enum_elements E).
Proof.
  intros E; constructor.
  - intros t [H _]; exact H.
  - intros t u [HS HT] HR; split; [exact (Acc_inv HS HR)|].
    intros n Hn HN; exact (candidate_reduct (enum_normal_elements_candidate n) (HT n Hn HN) HR).
  - intros t HN HR; split.
    + constructor; intros u HU; exact (proj1 (HR u HU)).
    + intros n Hn Hnf; apply (candidate_neutral (enum_normal_elements_candidate n) HN).
      intros u HU; exact (proj2 (HR u HU) n Hn Hnf).
Qed.
Lemma enum_elements_normal : forall E n,
  rtc reduction E n -> normal_form n ->
  predicate_equiv (enum_elements E) (enum_normal_elements n).
Proof.
  intros E n HR HN t; split; [intros [_ H]; exact (H n HR HN)|].
  intro HT; split; [exact (candidate_normalizing (enum_normal_elements_candidate n) HT)|].
  intros m HM Hm; assert (n = m) by (eapply normal_forms_join; [apply cv_refl|eassumption|eassumption|eassumption|eassumption]).
  now subst m.
Qed.
Theorem enum_elements_conversion : forall E F, conv E F ->
  predicate_equiv (enum_elements E) (enum_elements F).
Proof.
  intros E F HC t; split; intros [HS HT]; split; try exact HS;
    intros n HR HN; apply HT; [|exact HN| |exact HN];
    eapply conversion_normal_reductions; [apply cv_sym; exact HC|exact HR|exact HN|exact HC|exact HR|exact HN].
Qed.

Lemma cons_enum_reduction_components : forall tag E u, reduction (TConsE tag E) u ->
  (exists tag', reduction tag tag' /\ u = TConsE tag' E) \/
  (exists E', reduction E E' /\ u = TConsE tag E').
Proof. description_components. Qed.
Lemma normal_form_cons_enum : forall tag E,
  normal_form tag -> normal_form E -> normal_form (TConsE tag E).
Proof. exact (normal_form_binary TConsE cons_enum_reduction_components). Qed.
Lemma nil_enum_normal : normal_form TNilE.
Proof. intros u H; inversion H; discriminate. Qed.
Theorem enum_elements_empty : predicate_equiv (enum_elements TNilE) empty_elements.
Proof. apply (enum_elements_normal TNilE TNilE); [constructor|exact nil_enum_normal]. Qed.
Theorem enum_elements_cons : forall tag E, full_SN tag -> full_SN E ->
  predicate_equiv (enum_elements (TConsE tag E)) (extended_elements (enum_elements E)).
Proof.
  intros tag E Htag HE.
  destruct (normalize_full _ Htag) as [tag' [Rt Nt]].
  destruct (normalize_full _ HE) as [E' [RE NE]].
  pose proof (enum_elements_normal _ _ (red_star_TConsE _ _ _ _ Rt RE)
    (normal_form_cons_enum _ _ Nt NE)) as HC.
  pose proof (extended_elements_equiv _ _ (enum_elements_normal _ _ RE NE)) as HX.
  intro t; specialize (HC t); specialize (HX t); cbn [enum_normal_elements] in HC; tauto.
Qed.
Lemma enum_zero_computable : forall tag E,
  full_SN tag -> full_SN E -> enum_elements (TConsE tag E) TEZero.
Proof.
  intros tag E Htag HE; apply (enum_elements_cons _ _ Htag HE).
  apply saturated_intro; now left.
Qed.
Lemma enum_succ_computable : forall tag E n,
  full_SN tag -> full_SN E -> enum_elements E n -> enum_elements (TConsE tag E) (TESucc n).
Proof.
  intros tag E n Htag HE Hn; apply (enum_elements_cons _ _ Htag HE).
  apply saturated_intro; right; now exists n.
Qed.

Print Assumptions enum_elements_candidate.
Print Assumptions enum_elements_conversion.
Print Assumptions enum_elements_empty.
Print Assumptions enum_zero_computable.
Print Assumptions enum_succ_computable.
