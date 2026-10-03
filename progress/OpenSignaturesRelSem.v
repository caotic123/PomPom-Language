(* Semantic typing rules of the binary relational model, on closed terms.
   Each typing rule has a semantic counterpart; the fundamental lemma and
   the elaboration coherence proof are assembled from them. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelLevels.
Import ListNotations.

Lemma rel_equiv_l : forall R S t u, rel_equiv R S -> S t u -> R t u.
Proof. intros R S t u H; apply H. Qed.
Lemma rel_equiv_r : forall R S t u, rel_equiv R S -> R t u -> S t u.
Proof. intros R S t u H; apply H. Qed.

Definition ty_rel (k : nat) (A B : term) := exists R, interp k A B R.
Definition rel_at (t u A B : term) := exists k R, interp k A B R /\ R t u.
Definition canonT (k : nat) (A : term) : rel := fun t u => exists B R, interp k A B R /\ R t u.

Lemma canonT_equiv : forall k A B R, interp k A B R -> rel_equiv R (canonT k A).
Proof.
  intros k A B R H t u; split.
  - intros Ht; exists B, R; split; assumption.
  - intros [B' [R' [H' Ht]]]. exact (rel_equiv_l _ _ _ _ (interp_unique_left k k _ _ _ _ _ _ H H' (cv_refl _)) Ht).
Qed.
Lemma canonT_interp : forall k A B R, interp k A B R -> interp k A B (canonT k A).
Proof. intros k A B R H; eapply interp_equiv; [exact H|exact (canonT_equiv _ _ _ _ H)]. Qed.

Lemma rel_at_transfer : forall t u A B k A' B' S, rel_at t u A B -> interp k A' B' S ->
  conv A A' -> S t u.
Proof.
  intros t u A B k A' B' S [j [R [H Ht]]] H' Hc.
  exact (rel_equiv_r _ _ _ _ (interp_unique_left _ _ _ _ _ _ _ _ H H' Hc) Ht).
Qed.
Lemma rel_at_transfer_r : forall t u A B k A' B' S, rel_at t u A B -> interp k A' B' S ->
  conv B B' -> S t u.
Proof.
  intros t u A B k A' B' S [j [R [H Ht]]] H' Hc.
  exact (rel_equiv_r _ _ _ _ (interp_unique_right _ _ _ _ _ _ _ _ H H' Hc) Ht).
Qed.
Lemma rel_at_conv : forall t u A B t' u' A' B', rel_at t u A B ->
  conv t t' -> conv u u' -> conv A A' -> conv B B' -> rel_at t' u' A' B'.
Proof.
  intros t u A B t' u' A' B' [k [R [H Ht]]] H1 H2 H3 H4.
  exists k, R; split; [eapply interp_conv; eassumption|].
  eapply interp_conv_closed; eassumption.
Qed.
Lemma rel_at_types : forall t u A B, rel_at t u A B -> exists k, ty_rel k A B.
Proof. intros t u A B [k [R [H _]]]; exists k, R; exact H. Qed.
Lemma rel_at_sym : forall t u A B, rel_at t u A B -> rel_at u t B A.
Proof.
  intros t u A B [k [R [H Ht]]]; exists k, R; split; [apply interp_sym, H|].
  apply (interp_per _ _ _ _ H), Ht.
Qed.
Lemma rel_at_refl_left : forall t u A B, rel_at t u A B -> rel_at t t A A.
Proof.
  intros t u A B [k [R [H Ht]]]; exists k, R; split; [eapply interp_refl_left; eassumption|].
  eapply per_refl_left; [eapply interp_per; eassumption|exact Ht].
Qed.
Lemma rel_at_trans : forall t u v A B C, rel_at t u A B -> rel_at u v B C -> rel_at t v A C.
Proof.
  intros t u v A B C [k [R [H Ht]]] [j [S [H' Hu]]].
  exists (Nat.max k j), R; split; [eapply interp_trans_levels; [exact H|exact H'|apply cv_refl]|].
  eapply (proj2 (interp_per _ _ _ _ H)); [exact Ht|].
  exact (rel_equiv_r _ _ _ _ (interp_unique_left _ _ _ _ _ _ _ _ H' (interp_sym _ _ _ _ H) (cv_refl _)) Hu).
Qed.

Lemma ty_rel_cumul : forall j k A B, ty_rel j A B -> j <= k -> ty_rel k A B.
Proof. intros j k A B [R H] Hjk; exists R; eapply interp_cumulative; eassumption. Qed.
Lemma ty_rel_conv : forall k A B A' B', ty_rel k A B -> conv A A' -> conv B B' -> ty_rel k A' B'.
Proof. intros k A B A' B' [R H] HA HB; exists R; eapply interp_conv; eassumption. Qed.

(* ------------------------------------------------------------------ *)
(* Universes *)

Lemma sort_interp : forall k, interp (S k) (TSort k) (TSort k) (univ_rel k).
Proof. intro k; apply t2_atom; eapply a2_sort; [apply levels_lookup; lia|apply cv_refl|apply cv_refl]. Qed.

Lemma rel_at_sort : forall A B k, rel_at A B (TSort k) (TSort k) <-> ty_rel k A B.
Proof.
  intros A B k; split.
  - intros H. pose proof (rel_at_transfer _ _ _ _ _ _ _ _ H (sort_interp k) (cv_refl _)) as [R HR].
    exists R; exact HR.
  - intros [R HR]; exists (S k), (univ_rel k); split; [apply sort_interp|exists R; exact HR].
Qed.

Lemma sem_sort : forall k, rel_at (TSort k) (TSort k) (TSort (S k)) (TSort (S k)).
Proof. intro k; apply rel_at_sort; exists (univ_rel k); apply sort_interp. Qed.

Lemma sem_universe_cumul : forall A B j k, rel_at A B (TSort j) (TSort j) -> j <= k ->
  rel_at A B (TSort k) (TSort k).
Proof. intros A B j k H Hjk; apply rel_at_sort; eapply ty_rel_cumul; [apply rel_at_sort; exact H|exact Hjk]. Qed.

(* ------------------------------------------------------------------ *)
(* Dependent functions and pairs *)

Lemma sem_pi : forall x A1 B1 y A2 B2 j k,
  ty_rel j A1 A2 ->
  (forall a1 a2, closed a1 -> closed a2 -> rel_at a1 a2 A1 A2 ->
    ty_rel k (subst a1 x B1) (subst a2 y B2)) ->
  ty_rel (Nat.max j k) (TPi x A1 B1) (TPi y A2 B2).
Proof.
  intros x A1 B1 y A2 B2 j k [RA HA] HB.
  exists (pi_rel RA (fun a _ => canonT (Nat.max j k) (subst a x B1))).
  eapply t2_pi; [apply cv_refl|apply cv_refl|eapply interp_cumulative; [|exact HA]; lia|].
  intros a b Ha Hb Hab.
  destruct (HB a b Ha Hb (ex_intro _ j (ex_intro _ RA (conj HA Hab)))) as [RB HRB].
  apply canonT_interp with (R := RB). eapply interp_cumulative; [|exact HRB]; lia.
Qed.
Lemma sem_sigma : forall x A1 B1 y A2 B2 j k,
  ty_rel j A1 A2 ->
  (forall a1 a2, closed a1 -> closed a2 -> rel_at a1 a2 A1 A2 ->
    ty_rel k (subst a1 x B1) (subst a2 y B2)) ->
  ty_rel (Nat.max j k) (TSigma x A1 B1) (TSigma y A2 B2).
Proof.
  intros x A1 B1 y A2 B2 j k [RA HA] HB.
  exists (sigma_rel RA (fun a _ => canonT (Nat.max j k) (subst a x B1))).
  eapply t2_sigma; [apply cv_refl|apply cv_refl|eapply interp_cumulative; [|exact HA]; lia|].
  intros a b Ha Hb Hab.
  destruct (HB a b Ha Hb (ex_intro _ j (ex_intro _ RA (conj HA Hab)))) as [RB HRB].
  apply canonT_interp with (R := RB). eapply interp_cumulative; [|exact HRB]; lia.
Qed.

(* Inversion of an interpreted function type. *)
Lemma interp_pi_view : forall k A B R x U V, interp k A B R -> conv A (TPi x U V) ->
  exists x0 U0 V0 y0 U0' V0' RU RV,
    conv A (TPi x0 U0 V0) /\ conv B (TPi y0 U0' V0') /\ interp k U0 U0' RU /\
    (forall a b, closed a -> closed b -> RU a b -> interp k (subst a x0 V0) (subst b y0 V0') (RV a b)) /\
    rel_equiv R (pi_rel RU RV).
Proof.
  intros k A B R x U V H Hc; destruct (T2_view _ _ _ _ H) as
    [R' HA HR|x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR|x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR].
  - exfalso; eapply atom2_not_pi_l; eassumption.
  - exists x0, U0, V0, y0, U0', V0', RU, RV; repeat apply conj; assumption.
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact Ha]
      |reflexivity|reflexivity|discriminate].
Qed.
Lemma interp_sigma_view : forall k A B R x U V, interp k A B R -> conv A (TSigma x U V) ->
  exists x0 U0 V0 y0 U0' V0' RU RV,
    conv A (TSigma x0 U0 V0) /\ conv B (TSigma y0 U0' V0') /\ interp k U0 U0' RU /\
    (forall a b, closed a -> closed b -> RU a b -> interp k (subst a x0 V0) (subst b y0 V0') (RV a b)) /\
    rel_equiv R (sigma_rel RU RV).
Proof.
  intros k A B R x U V H Hc; destruct (T2_view _ _ _ _ H) as
    [R' HA HR|x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR|x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR].
  - exfalso; eapply atom2_not_sigma_l; eassumption.
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact Ha]
      |reflexivity|reflexivity|discriminate].
  - exists x0, U0, V0, y0, U0', V0', RU, RV; repeat apply conj; assumption.
Qed.

Lemma beta_conv : forall x b a, conv (TApp (TLam x b) a) (subst a x b).
Proof. intros; apply conv_root; reflexivity. Qed.

Lemma sem_lam : forall x b1 y b2 x' A1 B1 y' A2 B2 k,
  ty_rel k (TPi x' A1 B1) (TPi y' A2 B2) ->
  (forall a1 a2, closed a1 -> closed a2 -> rel_at a1 a2 A1 A2 ->
    rel_at (subst a1 x b1) (subst a2 y b2) (subst a1 x' B1) (subst a2 y' B2)) ->
  rel_at (TLam x b1) (TLam y b2) (TPi x' A1 B1) (TPi y' A2 B2).
Proof.
  intros x b1 y b2 x' A1 B1 y' A2 B2 k [R HR] Hb.
  destruct (interp_pi_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & Ha & Hb' & HU & HV & HE).
  destruct (conv_pi_inv _ _ _ _ _ _ Ha) as [HAU HBV].
  destruct (conv_pi_inv _ _ _ _ _ _ Hb') as [HAU' HBV'].
  exists k, R; split; [exact HR|]. apply HE; intros a b Ha1 Hb1 Hab.
  assert (Hrel : rel_at a b A1 A2).
  { exists k, RU; split; [eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']|exact Hab]. }
  pose proof (Hb a b Ha1 Hb1 Hrel) as Hab'.
  eapply interp_conv_closed; [apply HV; assumption| | |].
  - eapply rel_at_transfer; [exact Hab'|apply HV; assumption|apply HBV; exact Ha1].
  - apply cv_sym, beta_conv.
  - apply cv_sym, beta_conv.
Qed.

Lemma sem_app : forall f1 f2 x A1 B1 y A2 B2 a1 a2,
  rel_at f1 f2 (TPi x A1 B1) (TPi y A2 B2) -> rel_at a1 a2 A1 A2 -> closed a1 -> closed a2 ->
  rel_at (TApp f1 a1) (TApp f2 a2) (subst a1 x B1) (subst a2 y B2).
Proof.
  intros f1 f2 x A1 B1 y A2 B2 a1 a2 [k [R [HR Hf]]] Ha Hc1 Hc2.
  destruct (interp_pi_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_pi_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_pi_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  assert (Hab : RU a1 a2) by (eapply rel_at_transfer; [exact Ha|exact HU|exact HAU]).
  exists k, (RV a1 a2); split.
  - eapply interp_conv; [apply HV; assumption|apply cv_sym, HBV, Hc1|apply cv_sym, HBV', Hc2].
  - apply (proj1 (HE f1 f2) Hf); assumption.
Qed.

Lemma sem_pair : forall x A1 B1 y A2 B2 k a1 a2 b1 b2,
  ty_rel k (TSigma x A1 B1) (TSigma y A2 B2) ->
  closed a1 -> closed a2 -> closed b1 -> closed b2 ->
  rel_at a1 a2 A1 A2 -> rel_at b1 b2 (subst a1 x B1) (subst a2 y B2) ->
  rel_at (TPair a1 b1) (TPair a2 b2) (TSigma x A1 B1) (TSigma y A2 B2).
Proof.
  intros x A1 B1 y A2 B2 k a1 a2 b1 b2 [R HR] Hca1 Hca2 Hcb1 Hcb2 Ha Hb.
  destruct (interp_sigma_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_sigma_inv _ _ _ _ _ _ HA) as [HAU HBV].
  assert (Hab : RU a1 a2) by (eapply rel_at_transfer; [exact Ha|exact HU|exact HAU]).
  exists k, R; split; [exact HR|]. apply HE.
  exists a1, b1, a2, b2; repeat apply conj; try assumption; try apply cv_refl.
  eapply rel_at_transfer; [exact Hb|apply HV; assumption|apply HBV; exact Hca1].
Qed.

Lemma sem_fst : forall p1 p2 x A1 B1 y A2 B2,
  rel_at p1 p2 (TSigma x A1 B1) (TSigma y A2 B2) -> rel_at (TFst p1) (TFst p2) A1 A2.
Proof.
  intros p1 p2 x A1 B1 y A2 B2 [k [R [HR Hp]]].
  destruct (interp_sigma_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_sigma_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_sigma_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  destruct (proj1 (HE p1 p2) Hp) as [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp1 [Hp2 [HR1 HR2]]]]]]]]]]].
  exists k, RU; split; [eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']|].
  eapply interp_conv_closed; [exact HU|exact HR1| |].
  - eapply cv_trans; [|apply cv_sym, conv_fst, Hp1]; apply cv_sym, conv_root; reflexivity.
  - eapply cv_trans; [|apply cv_sym, conv_fst, Hp2]; apply cv_sym, conv_root; reflexivity.
Qed.

Lemma sem_snd : forall p1 p2 x A1 B1 y A2 B2,
  rel_at p1 p2 (TSigma x A1 B1) (TSigma y A2 B2) ->
  rel_at (TSnd p1) (TSnd p2) (subst (TFst p1) x B1) (subst (TFst p2) y B2).
Proof.
  intros p1 p2 x A1 B1 y A2 B2 [k [R [HR Hp]]].
  destruct (interp_sigma_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_sigma_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_sigma_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  destruct (proj1 (HE p1 p2) Hp) as [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp1 [Hp2 [HR1 HR2]]]]]]]]]]].
  assert (Hf1 : conv (TFst p1) a) by (eapply cv_trans; [apply conv_fst, Hp1|apply conv_root; reflexivity]).
  assert (Hf2 : conv (TFst p2) a') by (eapply cv_trans; [apply conv_fst, Hp2|apply conv_root; reflexivity]).
  exists k, (RV a a'); split.
  - eapply interp_conv; [apply HV; assumption| |].
    + eapply cv_trans; [apply cv_sym, HBV, Ha|]. apply substitution_argument_conversion, cv_sym, Hf1.
    + eapply cv_trans; [apply cv_sym, HBV', Ha'|]. apply substitution_argument_conversion, cv_sym, Hf2.
  - eapply interp_conv_closed; [apply HV; assumption|exact HR2| |].
    + eapply cv_trans; [|apply cv_sym, conv_snd, Hp1]; apply cv_sym, conv_root; reflexivity.
    + eapply cv_trans; [|apply cv_sym, conv_snd, Hp2]; apply cv_sym, conv_root; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Unit, labels, enumeration codes and enumerations *)

Lemma small_ty_rel : forall k A B R, S2 A B R -> ty_rel k A B.
Proof. intros k A B R H; exists R; apply S2_interp, H. Qed.

Lemma sem_unitT : forall k, ty_rel k TUnitT TUnitT.
Proof. intro k; eapply small_ty_rel, s2_unit; apply cv_refl. Qed.
Lemma sem_unit : rel_at TUnit TUnit TUnitT TUnitT.
Proof.
  exists 0, unit_rel; split; [apply S2_interp, s2_unit; apply cv_refl|split; apply cv_refl].
Qed.
Lemma sem_uid : ty_rel 0 TUId TUId.
Proof. eapply small_ty_rel, s2_uid; apply cv_refl. Qed.
Lemma sem_tag : forall s, rel_at (TTag s) (TTag s) TUId TUId.
Proof.
  intro s; exists 0, tag_rel; split; [apply S2_interp, s2_uid; apply cv_refl|exists s; split; apply cv_refl].
Qed.
Lemma sem_enumu : ty_rel 0 TEnumU TEnumU.
Proof. eapply small_ty_rel, s2_enumu; apply cv_refl. Qed.
Lemma enumu_interp : interp 0 TEnumU TEnumU code_rel.
Proof. apply S2_interp, s2_enumu; apply cv_refl. Qed.
Lemma sem_nile : rel_at TNilE TNilE TEnumU TEnumU.
Proof. exists 0, code_rel; split; [exact enumu_interp|exists []; split; apply cv_refl]. Qed.
Lemma rel_at_code : forall E1 E2, rel_at E1 E2 TEnumU TEnumU -> code_rel E1 E2.
Proof. intros E1 E2 H; eapply rel_at_transfer; [exact H|exact enumu_interp|apply cv_refl]. Qed.
Lemma uid_interp : interp 0 TUId TUId tag_rel.
Proof. apply S2_interp, s2_uid; apply cv_refl. Qed.
Lemma rel_at_tag : forall t1 t2, rel_at t1 t2 TUId TUId -> tag_rel t1 t2.
Proof. intros t1 t2 H; eapply rel_at_transfer; [exact H|exact uid_interp|apply cv_refl]. Qed.

Lemma sem_conse : forall t1 t2 E1 E2, rel_at t1 t2 TUId TUId -> rel_at E1 E2 TEnumU TEnumU ->
  rel_at (TConsE t1 E1) (TConsE t2 E2) TEnumU TEnumU.
Proof.
  intros t1 t2 E1 E2 Ht HE.
  destruct (rel_at_tag _ _ Ht) as [s [Hs1 Hs2]]; destruct (rel_at_code _ _ HE) as [L [HL1 HL2]].
  exists 0, code_rel; split; [exact enumu_interp|exists (s :: L)].
  split; apply cv_compatible, cp_TConsE; assumption.
Qed.

Lemma enum_interp : forall E1 E2 L, conv E1 (code L) -> conv E2 (code L) ->
  interp 0 (TEnumT E1) (TEnumT E2) (enum_rel (List.length L)).
Proof. intros; apply S2_interp; eapply s2_enum; [apply cv_refl|apply cv_refl|eassumption|eassumption]. Qed.
Lemma sem_enumt : forall E1 E2, rel_at E1 E2 TEnumU TEnumU -> ty_rel 0 (TEnumT E1) (TEnumT E2).
Proof.
  intros E1 E2 HE; destruct (rel_at_code _ _ HE) as [L [HL1 HL2]].
  exists (enum_rel (List.length L)); apply enum_interp; assumption.
Qed.
Lemma rel_at_enum : forall n1 n2 E1 E2 L, rel_at n1 n2 (TEnumT E1) (TEnumT E2) ->
  conv E1 (code L) -> exists m, m < List.length L /\ conv n1 (enum_position m) /\ conv n2 (enum_position m).
Proof.
  intros n1 n2 E1 E2 L H HL.
  apply (rel_at_transfer _ _ _ _ _ _ _ _ H (enum_interp E1 E1 L HL HL) (cv_refl _)).
Qed.
Lemma sem_position : forall E1 E2 L m, conv E1 (code L) -> conv E2 (code L) -> m < List.length L ->
  rel_at (enum_position m) (enum_position m) (TEnumT E1) (TEnumT E2).
Proof.
  intros E1 E2 L m H1 H2 Hm; exists 0, (enum_rel (List.length L)); split;
    [apply enum_interp; assumption|exists m; repeat apply conj; [exact Hm|apply cv_refl|apply cv_refl]].
Qed.

Lemma sem_zero : forall t1 t2 E1 E2, rel_at t1 t2 TUId TUId -> rel_at E1 E2 TEnumU TEnumU ->
  rel_at TEZero TEZero (TEnumT (TConsE t1 E1)) (TEnumT (TConsE t2 E2)).
Proof.
  intros t1 t2 E1 E2 Ht HE.
  destruct (rel_at_code _ _ (sem_conse _ _ _ _ Ht HE)) as [L [HL1 HL2]].
  destruct L as [|s L]; [clash HL1|].
  apply (sem_position _ _ (s :: L) 0); [exact HL1|exact HL2|cbn; lia].
Qed.
Lemma sem_succ : forall t1 t2 E1 E2 n1 n2, rel_at t1 t2 TUId TUId -> rel_at E1 E2 TEnumU TEnumU ->
  rel_at n1 n2 (TEnumT E1) (TEnumT E2) ->
  rel_at (TESucc n1) (TESucc n2) (TEnumT (TConsE t1 E1)) (TEnumT (TConsE t2 E2)).
Proof.
  intros t1 t2 E1 E2 n1 n2 Ht HE Hn.
  destruct (rel_at_tag _ _ Ht) as [s [Hs1 Hs2]]; destruct (rel_at_code _ _ HE) as [L [HL1 HL2]].
  destruct (rel_at_enum _ _ _ _ _ Hn HL1) as [m [Hm [Hm1 Hm2]]].
  exists 0, (enum_rel (List.length (s :: L))); split.
  - apply enum_interp; cbn [code]; apply cv_compatible, cp_TConsE; assumption.
  - exists (S m); repeat apply conj; [cbn; lia| |]; cbn [enum_position];
      apply cv_compatible, cp_TESucc; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Non-dependent function and pair types *)

Lemma subst_not_free : forall t u x, ~ In x (free_vars t) -> subst u x t = t.
Proof. intros; apply subst_fresh; assumption. Qed.

Lemma sem_arrow : forall A1 B1 A2 B2 j k, ty_rel j A1 A2 -> ty_rel k B1 B2 ->
  ty_rel (Nat.max j k) (arrow A1 B1) (arrow A2 B2).
Proof.
  intros A1 B1 A2 B2 j k HA HB; unfold arrow; apply sem_pi; [exact HA|].
  intros a1 a2 _ _ _; rewrite !subst_not_free by (apply fresh_not_free; cbn; auto); exact HB.
Qed.
Lemma sem_product : forall A1 B1 A2 B2 j k, ty_rel j A1 A2 -> ty_rel k B1 B2 ->
  ty_rel (Nat.max j k) (product A1 B1) (product A2 B2).
Proof.
  intros A1 B1 A2 B2 j k HA HB; unfold product; apply sem_sigma; [exact HA|].
  intros a1 a2 _ _ _; rewrite !subst_not_free by (apply fresh_not_free; cbn; auto); exact HB.
Qed.
Lemma sem_arrow_app : forall f1 f2 A1 B1 A2 B2 a1 a2,
  rel_at f1 f2 (arrow A1 B1) (arrow A2 B2) -> rel_at a1 a2 A1 A2 -> closed a1 -> closed a2 ->
  rel_at (TApp f1 a1) (TApp f2 a2) B1 B2.
Proof.
  intros f1 f2 A1 B1 A2 B2 a1 a2 Hf Ha H1 H2; unfold arrow in Hf.
  pose proof (sem_app _ _ _ _ _ _ _ _ _ _ Hf Ha H1 H2) as H.
  rewrite !subst_not_free in H by (apply fresh_not_free; cbn; auto); exact H.
Qed.
Lemma sem_arrow_lam : forall f1 f2 A1 B1 A2 B2 k,
  ty_rel k (arrow A1 B1) (arrow A2 B2) ->
  (forall a1 a2, closed a1 -> closed a2 -> rel_at a1 a2 A1 A2 -> rel_at (TApp f1 a1) (TApp f2 a2) B1 B2) ->
  rel_at f1 f2 (arrow A1 B1) (arrow A2 B2).
Proof.
  intros f1 f2 A1 B1 A2 B2 k [R HR] Hf; unfold arrow in *.
  destruct (interp_pi_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_pi_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_pi_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  exists k, R; split; [exact HR|]. apply HE; intros a b Ha1 Hb1 Hab.
  assert (Hrel : rel_at a b A1 A2).
  { exists k, RU; split; [eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']|exact Hab]. }
  eapply rel_at_transfer; [exact (Hf a b Ha1 Hb1 Hrel)|apply HV; assumption|].
  pose proof (HBV a Ha1) as Hc. rewrite subst_not_free in Hc by (apply fresh_not_free; cbn; auto).
  exact Hc.
Qed.
Lemma sem_product_pair : forall A1 B1 A2 B2 k a1 a2 b1 b2,
  ty_rel k (product A1 B1) (product A2 B2) ->
  closed a1 -> closed a2 -> closed b1 -> closed b2 ->
  rel_at a1 a2 A1 A2 -> rel_at b1 b2 B1 B2 ->
  rel_at (TPair a1 b1) (TPair a2 b2) (product A1 B1) (product A2 B2).
Proof.
  intros A1 B1 A2 B2 k a1 a2 b1 b2 HT H1 H2 H3 H4 Ha Hb; unfold product in *.
  eapply sem_pair; try eassumption.
  rewrite !subst_not_free by (apply fresh_not_free; cbn; auto); exact Hb.
Qed.
Lemma sem_product_view : forall p1 p2 A1 B1 A2 B2,
  rel_at p1 p2 (product A1 B1) (product A2 B2) ->
  exists a1 b1 a2 b2, closed a1 /\ closed b1 /\ closed a2 /\ closed b2 /\
    conv p1 (TPair a1 b1) /\ conv p2 (TPair a2 b2) /\ rel_at a1 a2 A1 A2 /\ rel_at b1 b2 B1 B2.
Proof.
  intros p1 p2 A1 B1 A2 B2 [k [R [HR Hp]]]; unfold product in *.
  destruct (interp_sigma_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_sigma_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_sigma_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  destruct (proj1 (HE p1 p2) Hp) as [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp1 [Hp2 [HR1 HR2]]]]]]]]]]].
  exists a, b, a', b'; repeat apply conj; try assumption.
  - exists k, RU; split; [eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']|exact HR1].
  - exists k, (RV a a'); split; [|exact HR2].
    eapply interp_conv; [apply HV; assumption| |].
    + pose proof (HBV a Ha) as Hc; rewrite subst_not_free in Hc by (apply fresh_not_free; cbn; auto).
      apply cv_sym; exact Hc.
    + pose proof (HBV' a' Ha') as Hc; rewrite subst_not_free in Hc by (apply fresh_not_free; cbn; auto).
      apply cv_sym; exact Hc.
Qed.

(* ------------------------------------------------------------------ *)
(* Enumerated tuples and switch *)

Definition shift_motive (P : term) (x : nat) := TLam x (TApp P (TESucc (TVar x))).

Lemma closed_shift_motive : forall P x, closed P -> closed (shift_motive P x).
Proof.
  intros P x H; unfold closed, shift_motive in *; cbn [free_vars]; rewrite H; cbn.
  destruct (Nat.eq_dec x x); [reflexivity|congruence].
Qed.

Lemma shift_motive_beta : forall P x m, ~ In x (free_vars P) ->
  conv (TApp (shift_motive P x) (enum_position m)) (TApp P (enum_position (S m))).
Proof.
  intros P x m Hx; unfold shift_motive. eapply cv_trans; [apply beta_conv|].
  unfold subst; cbn [substitute]. rewrite Nat.eqb_refl.
  change (substitute (fun y => if Nat.eqb y x then enum_position m else TVar y) P) with
    (subst (enum_position m) x P).
  rewrite subst_not_free by exact Hx. apply cv_refl.
Qed.
Lemma shift_motive_alpha : forall P x y, ~ In x (free_vars P) -> ~ In y (free_vars P) ->
  conv (shift_motive P x) (shift_motive P y).
Proof.
  intros P x y Hx Hy; unfold shift_motive; apply cv_alpha.
  unfold alpha_equiv, alpha_eqb; cbn [alpha_eqb_in]; rewrite !Bool.andb_true_iff.
  split; [apply alpha_env_fresh; [apply alpha_eqb_in_refl|exact Hx|exact Hy]|].
  cbn [alpha_var]; rewrite !Nat.eqb_refl; reflexivity.
Qed.

Lemma epi_nil_conv : forall k E P, conv E TNilE -> conv (TEPi k E P) TUnitT.
Proof.
  intros k E P H; eapply cv_trans; [apply cv_compatible, cp_TEPi; [exact H|apply cv_refl]|].
  apply conv_root; reflexivity.
Qed.
Lemma epi_cons_conv : forall k E P s L, conv E (TConsE (TTag s) (code L)) ->
  conv (TEPi k E P)
    (product (TApp P TEZero) (TEPi k (code L) (shift_motive P (fresh [TTag s; code L; P])))).
Proof.
  intros k E P s L H; eapply cv_trans; [apply cv_compatible, cp_TEPi; [exact H|apply cv_refl]|].
  apply conv_root; reflexivity.
Qed.

Lemma sem_epi : forall k L E1 E2 P1 P2, conv E1 (code L) -> conv E2 (code L) ->
  (forall m, m < List.length L -> ty_rel k (TApp P1 (enum_position m)) (TApp P2 (enum_position m))) ->
  ty_rel k (TEPi k E1 P1) (TEPi k E2 P2).
Proof.
  intros k L; induction L as [|s L IH]; intros E1 E2 P1 P2 H1 H2 HP.
  - eapply ty_rel_conv; [apply sem_unitT|apply cv_sym, epi_nil_conv, H1|apply cv_sym, epi_nil_conv, H2].
  - eapply ty_rel_conv; [|apply cv_sym, epi_cons_conv, H1|apply cv_sym, epi_cons_conv, H2].
    replace k with (Nat.max k k) at 1 by lia. apply sem_product.
    + apply (HP 0); cbn; lia.
    + apply IH; [apply cv_refl|apply cv_refl|]. intros m Hm.
      eapply ty_rel_conv; [apply (HP (S m)); cbn; lia| |];
        apply cv_sym, shift_motive_beta, fresh_not_free; cbn; auto.
Qed.

Lemma switch_zero_conv : forall k s L P p a b, conv p (TPair a b) ->
  conv (TSwitch k (TConsE (TTag s) (code L)) P p TEZero) a.
Proof.
  intros k s L P p a b H.
  eapply cv_trans; [apply cv_compatible, cp_TSwitch; [apply cv_refl|apply cv_refl|exact H|apply cv_refl]|].
  apply conv_root; reflexivity.
Qed.
Lemma switch_succ_conv : forall k s L P p a b m, conv p (TPair a b) ->
  conv (TSwitch k (TConsE (TTag s) (code L)) P p (TESucc (enum_position m)))
    (TSwitch k (code L) (shift_motive P (fresh [TTag s; code L; P; a; b; enum_position m])) b (enum_position m)).
Proof.
  intros k s L P p a b m H.
  eapply cv_trans; [apply cv_compatible, cp_TSwitch; [apply cv_refl|apply cv_refl|exact H|apply cv_refl]|].
  apply conv_root; reflexivity.
Qed.

Lemma sem_switch_code : forall k L P1 P2 p1 p2 m, m < List.length L ->
  closed P1 -> closed P2 ->
  rel_at p1 p2 (TEPi k (code L) P1) (TEPi k (code L) P2) ->
  rel_at (TSwitch k (code L) P1 p1 (enum_position m)) (TSwitch k (code L) P2 p2 (enum_position m))
    (TApp P1 (enum_position m)) (TApp P2 (enum_position m)).
Proof.
  intros k L; induction L as [|s L IH]; intros P1 P2 p1 p2 m Hm HP1 HP2 Hp; [cbn in Hm; lia|].
  pose proof (rel_at_conv _ _ _ _ _ _ _ _ Hp (cv_refl _) (cv_refl _)
    (epi_cons_conv k _ P1 s L (cv_refl _)) (epi_cons_conv k _ P2 s L (cv_refl _))) as Hp'.
  destruct (sem_product_view _ _ _ _ _ _ Hp') as
    (a1 & b1 & a2 & b2 & Ha1 & Hb1 & Ha2 & Hb2 & Hp1 & Hp2 & Ha & Hb).
  destruct m as [|m].
  - eapply rel_at_conv; [exact Ha| | |apply cv_refl|apply cv_refl];
      apply cv_sym; eapply switch_zero_conv; eassumption.
  - cbn [enum_position].
    set (x1 := fresh [TTag s; code L; P1; a1; b1; enum_position m]).
    set (x2 := fresh [TTag s; code L; P2; a2; b2; enum_position m]).
    assert (Hx1 : ~ In x1 (free_vars P1)) by (apply fresh_not_free; cbn; auto).
    assert (Hx2 : ~ In x2 (free_vars P2)) by (apply fresh_not_free; cbn; auto).
    assert (HIH : rel_at (TSwitch k (code L) (shift_motive P1 x1) b1 (enum_position m))
      (TSwitch k (code L) (shift_motive P2 x2) b2 (enum_position m))
      (TApp (shift_motive P1 x1) (enum_position m)) (TApp (shift_motive P2 x2) (enum_position m))).
    { apply IH; [cbn in Hm; lia| | |].
      - apply closed_shift_motive, HP1.
      - apply closed_shift_motive, HP2.
      - eapply rel_at_conv; [exact Hb|apply cv_refl|apply cv_refl| |];
          apply cv_compatible, cp_TEPi; try apply cv_refl;
          apply shift_motive_alpha; try exact Hx1; try exact Hx2;
          apply fresh_not_free; cbn; auto. }
    eapply rel_at_conv; [exact HIH| | |apply shift_motive_beta, Hx1|apply shift_motive_beta, Hx2].
    + apply cv_sym; eapply switch_succ_conv; exact Hp1.
    + apply cv_sym; eapply switch_succ_conv; exact Hp2.
Qed.

Lemma sem_switch : forall k L E1 E2 P1 P2 p1 p2 e1 e2,
  conv E1 (code L) -> conv E2 (code L) -> closed P1 -> closed P2 ->
  rel_at p1 p2 (TEPi k E1 P1) (TEPi k E2 P2) -> rel_at e1 e2 (TEnumT E1) (TEnumT E2) ->
  rel_at (TSwitch k E1 P1 p1 e1) (TSwitch k E2 P2 p2 e2) (TApp P1 e1) (TApp P2 e2).
Proof.
  intros k L E1 E2 P1 P2 p1 p2 e1 e2 H1 H2 HP1 HP2 Hp He.
  destruct (rel_at_enum _ _ _ _ _ He H1) as [m [Hm [He1 He2]]].
  assert (Hp' : rel_at p1 p2 (TEPi k (code L) P1) (TEPi k (code L) P2)).
  { eapply rel_at_conv; [exact Hp|apply cv_refl|apply cv_refl| |];
      apply cv_compatible, cp_TEPi; [exact H1|apply cv_refl|exact H2|apply cv_refl]. }
  eapply rel_at_conv; [apply (sem_switch_code k L P1 P2 p1 p2 m Hm HP1 HP2 Hp')| | | |].
  - apply cv_compatible, cp_TSwitch; try apply cv_refl; apply cv_sym; assumption.
  - apply cv_compatible, cp_TSwitch; try apply cv_refl; apply cv_sym; assumption.
  - apply conv_app_a, cv_sym, He1.
  - apply conv_app_a, cv_sym, He2.
Qed.

(* Introduction for any function value, not only lambdas. *)
Lemma sem_pi_intro : forall f1 f2 x A1 B1 y A2 B2 k,
  ty_rel k (TPi x A1 B1) (TPi y A2 B2) ->
  (forall a1 a2, closed a1 -> closed a2 -> rel_at a1 a2 A1 A2 ->
    rel_at (TApp f1 a1) (TApp f2 a2) (subst a1 x B1) (subst a2 y B2)) ->
  rel_at f1 f2 (TPi x A1 B1) (TPi y A2 B2).
Proof.
  intros f1 f2 x A1 B1 y A2 B2 k [R HR] Hf.
  destruct (interp_pi_view _ _ _ _ _ _ _ HR (cv_refl _)) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA & HB & HU & HV & HE).
  destruct (conv_pi_inv _ _ _ _ _ _ HA) as [HAU HBV].
  destruct (conv_pi_inv _ _ _ _ _ _ HB) as [HAU' HBV'].
  exists k, R; split; [exact HR|]. apply HE; intros a b Ha1 Hb1 Hab.
  assert (Hrel : rel_at a b A1 A2).
  { exists k, RU; split; [eapply interp_conv; [exact HU|apply cv_sym; exact HAU|apply cv_sym; exact HAU']|exact Hab]. }
  eapply rel_at_transfer; [exact (Hf a b Ha1 Hb1 Hrel)|apply HV; assumption|apply HBV; exact Ha1].
Qed.

(* ------------------------------------------------------------------ *)
(* Small types and description codes *)

Lemma small_of_rel : forall A1 A2, rel_at A1 A2 (TSort 0) (TSort 0) -> exists RA, S2 A1 A2 RA.
Proof.
  intros A1 A2 H; destruct (proj1 (rel_at_sort _ _ _) H) as [RA HA].
  exists RA; apply interp0_S2, HA.
Qed.
Lemma small_rel_at : forall A1 A2 RA a1 a2, S2 A1 A2 RA -> RA a1 a2 -> rel_at a1 a2 A1 A2.
Proof. intros; exists 0, RA; split; [apply S2_interp|]; assumption. Qed.
Lemma rel_at_small : forall A1 A2 RA a1 a2, S2 A1 A2 RA -> rel_at a1 a2 A1 A2 -> RA a1 a2.
Proof. intros A1 A2 RA a1 a2 HS H; eapply rel_at_transfer; [exact H|apply (S2_interp 0); exact HS|apply cv_refl]. Qed.
Lemma small_type_rel : forall A1 A2 RA, S2 A1 A2 RA -> rel_at A1 A2 (TSort 0) (TSort 0).
Proof. intros A1 A2 RA H; apply rel_at_sort; exists RA; apply S2_interp, H. Qed.

Definition canonL (RI : rel) (D : term) : functor :=
  fun X t u => exists D' F, D2 RI D D' F /\ F X t u.
Lemma canonL_equiv : forall RI D D' F, D2 RI D D' F -> per RI -> conv_closed RI ->
  fequiv RI F (canonL RI D).
Proof.
  intros RI D D' F H HP HC X HX t u; split.
  - intros Ht; exists D', F; split; assumption.
  - intros [D'' [G [HG Ht]]].
    exact (rel_equiv_l _ _ _ _ (D2_unique_left _ _ _ _ _ _ _ _ H HP HC HG (rel_equiv_refl _) (cv_refl _) X HX) Ht).
Qed.
Lemma D2_canonL : forall RI D D' F, D2 RI D D' F -> per RI -> conv_closed RI ->
  D2 RI D D' (canonL RI D).
Proof. intros; eapply d2_equiv; [eassumption|eapply canonL_equiv; eassumption]. Qed.

Lemma idesc_interp : forall k IT1 IT2 RI, 0 < k -> S2 IT1 IT2 RI ->
  interp k (TIDesc IT1) (TIDesc IT2) (desc_rel RI).
Proof. intros; apply t2_atom; eapply a2_idesc; [eassumption|eassumption|apply cv_refl|apply cv_refl]. Qed.
Lemma sem_idesc : forall IT1 IT2, rel_at IT1 IT2 (TSort 0) (TSort 0) ->
  ty_rel 1 (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 H; destruct (small_of_rel _ _ H) as [RI HI].
  exists (desc_rel RI); apply idesc_interp; [lia|exact HI].
Qed.
Lemma rel_at_desc : forall IT1 IT2 RI Df1 Df2, S2 IT1 IT2 RI ->
  rel_at Df1 Df2 (TIDesc IT1) (TIDesc IT2) -> desc_rel RI Df1 Df2.
Proof.
  intros IT1 IT2 RI Df1 Df2 HI H.
  eapply rel_at_transfer; [exact H|apply (idesc_interp 1); [lia|exact HI]|apply cv_refl].
Qed.
Lemma desc_rel_at : forall IT1 IT2 RI Df1 Df2, S2 IT1 IT2 RI ->
  desc_rel RI Df1 Df2 -> rel_at Df1 Df2 (TIDesc IT1) (TIDesc IT2).
Proof. intros; exists 1, (desc_rel RI); split; [apply idesc_interp; [lia|assumption]|assumption]. Qed.

Lemma sem_ivar : forall IT1 IT2 RI i1 i2, S2 IT1 IT2 RI -> rel_at i1 i2 IT1 IT2 ->
  closed i1 -> closed i2 -> rel_at (TIVar i1) (TIVar i2) (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 RI i1 i2 HI Hi H1 H2; eapply desc_rel_at; [exact HI|].
  eexists; eapply d2_var; [apply cv_refl|apply cv_refl|exact H1|exact H2|eapply rel_at_small; eassumption].
Qed.
Lemma sem_i1 : forall IT1 IT2 RI, S2 IT1 IT2 RI -> rel_at TI1 TI1 (TIDesc IT1) (TIDesc IT2).
Proof. intros; eapply desc_rel_at; [eassumption|eexists; apply d2_one; apply cv_refl]. Qed.
Lemma sem_ibot : forall IT1 IT2 RI, S2 IT1 IT2 RI -> rel_at TIBot TIBot (TIDesc IT1) (TIDesc IT2).
Proof. intros; eapply desc_rel_at; [eassumption|eexists; apply d2_bot; apply cv_refl]. Qed.
Lemma sem_iprod : forall IT1 IT2 RI A1 A2 B1 B2, S2 IT1 IT2 RI ->
  closed A1 -> closed A2 -> closed B1 -> closed B2 ->
  rel_at A1 A2 (TIDesc IT1) (TIDesc IT2) -> rel_at B1 B2 (TIDesc IT1) (TIDesc IT2) ->
  rel_at (TIProd A1 B1) (TIProd A2 B2) (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 RI A1 A2 B1 B2 HI H1 H2 H3 H4 HA HB; eapply desc_rel_at; [exact HI|].
  destruct (rel_at_desc _ _ _ _ _ HI HA) as [FA HFA]; destruct (rel_at_desc _ _ _ _ _ HI HB) as [FB HFB].
  eexists; eapply d2_prod; [apply cv_refl|apply cv_refl|exact H1|exact H3|exact H2|exact H4|exact HFA|exact HFB].
Qed.

Lemma sem_desc_family : forall IT1 IT2 RI A1 A2 RA Df1 Df2, S2 IT1 IT2 RI -> S2 A1 A2 RA ->
  rel_at Df1 Df2 (arrow A1 (TIDesc IT1)) (arrow A2 (TIDesc IT2)) ->
  forall a a', closed a -> closed a' -> RA a a' ->
    D2 RI (TApp Df1 a) (TApp Df2 a') (canonL RI (TApp Df1 a)).
Proof.
  intros IT1 IT2 RI A1 A2 RA Df1 Df2 HI HA HD a a' Ha Ha' Haa.
  pose proof (sem_arrow_app _ _ _ _ _ _ _ _ HD (small_rel_at _ _ _ _ _ HA Haa) Ha Ha') as H.
  destruct (rel_at_desc _ _ _ _ _ HI H) as [F HF].
  eapply D2_canonL; [exact HF|eapply S2_per|eapply S2_conv_closed]; exact HI.
Qed.
Lemma sem_ipi : forall IT1 IT2 RI A1 A2 Df1 Df2, S2 IT1 IT2 RI ->
  closed A1 -> closed A2 -> closed Df1 -> closed Df2 ->
  rel_at A1 A2 (TSort 0) (TSort 0) ->
  rel_at Df1 Df2 (arrow A1 (TIDesc IT1)) (arrow A2 (TIDesc IT2)) ->
  rel_at (TIPi A1 Df1) (TIPi A2 Df2) (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 RI A1 A2 Df1 Df2 HI Hc1 Hc2 Hc3 Hc4 HA HD; destruct (small_of_rel _ _ HA) as [RA HRA].
  eapply desc_rel_at; [exact HI|]. eexists.
  eapply d2_pi with (FE := fun a => canonL RI (TApp Df1 a));
    [apply cv_refl|apply cv_refl|exact Hc1|exact Hc3|exact Hc2|exact Hc4|exact HRA|].
  intros a a' Ha Ha' Haa; eapply sem_desc_family; eassumption.
Qed.
Lemma sem_isig : forall IT1 IT2 RI A1 A2 Df1 Df2, S2 IT1 IT2 RI ->
  closed A1 -> closed A2 -> closed Df1 -> closed Df2 ->
  rel_at A1 A2 (TSort 0) (TSort 0) ->
  rel_at Df1 Df2 (arrow A1 (TIDesc IT1)) (arrow A2 (TIDesc IT2)) ->
  rel_at (TISig A1 Df1) (TISig A2 Df2) (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 RI A1 A2 Df1 Df2 HI Hc1 Hc2 Hc3 Hc4 HA HD; destruct (small_of_rel _ _ HA) as [RA HRA].
  eapply desc_rel_at; [exact HI|]. eexists.
  eapply d2_sig with (FE := fun a => canonL RI (TApp Df1 a));
    [apply cv_refl|apply cv_refl|exact Hc1|exact Hc3|exact Hc2|exact Hc4|exact HRA|].
  intros a a' Ha Ha' Haa; eapply sem_desc_family; eassumption.
Qed.
Lemma sem_ichoice : forall IT1 IT2 RI E1 E2 C1 C2, S2 IT1 IT2 RI ->
  closed C1 -> closed C2 -> rel_at E1 E2 TEnumU TEnumU ->
  rel_at C1 C2 (arrow (TEnumT E1) (TIDesc IT1)) (arrow (TEnumT E2) (TIDesc IT2)) ->
  rel_at (TIChoice E1 C1) (TIChoice E2 C2) (TIDesc IT1) (TIDesc IT2).
Proof.
  intros IT1 IT2 RI E1 E2 C1 C2 HI Hc1 Hc2 HE HC; destruct (rel_at_code _ _ HE) as [L [HL1 HL2]].
  eapply desc_rel_at; [exact HI|]. eexists.
  eapply d2_choice with (L := L) (FC := fun n => canonL RI (TApp C1 (enum_position n)));
    [apply cv_refl|apply cv_refl|exact Hc1|exact Hc2|exact HL1|exact HL2|].
  intros n Hn.
  pose proof (sem_arrow_app _ _ _ _ _ _ _ _ HC (sem_position _ _ _ _ HL1 HL2 Hn)
    (closed_position n) (closed_position n)) as H.
  destruct (rel_at_desc _ _ _ _ _ HI H) as [F HF].
  eapply D2_canonL; [exact HF|eapply S2_per|eapply S2_conv_closed]; exact HI.
Qed.
