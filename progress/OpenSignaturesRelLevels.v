(* Cumulative universe tower for the binary relational model. Each level is
   a structural Pi/Sigma closure over atoms: small non-function types,
   lower universes, and description types from level one. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelSmallClaims.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Generic structural closure *)

Section Structural.
Variable atom : term -> term -> rel -> Prop.

Inductive TI2 : term -> term -> rel -> Prop :=
| t2_atom : forall A B R, atom A B R -> TI2 A B R
| t2_pi : forall A B x U V y U' V' RU RV,
    conv A (TPi x U V) -> conv B (TPi y U' V') -> TI2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> TI2 (subst a x V) (subst b y V') (RV a b)) ->
    TI2 A B (pi_rel RU RV)
| t2_sigma : forall A B x U V y U' V' RU RV,
    conv A (TSigma x U V) -> conv B (TSigma y U' V') -> TI2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> TI2 (subst a x V) (subst b y V') (RV a b)) ->
    TI2 A B (sigma_rel RU RV)
| t2_equiv : forall A B R S, TI2 A B R -> rel_equiv R S -> TI2 A B S.

Inductive T2_shape (A B : term) (R : rel) : Prop :=
| tsh_atom : forall R', atom A B R' -> rel_equiv R R' -> T2_shape A B R
| tsh_pi : forall x U V y U' V' RU RV, conv A (TPi x U V) -> conv B (TPi y U' V') -> TI2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> TI2 (subst a x V) (subst b y V') (RV a b)) ->
    rel_equiv R (pi_rel RU RV) -> T2_shape A B R
| tsh_sigma : forall x U V y U' V' RU RV, conv A (TSigma x U V) -> conv B (TSigma y U' V') -> TI2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> TI2 (subst a x V) (subst b y V') (RV a b)) ->
    rel_equiv R (sigma_rel RU RV) -> T2_shape A B R.

Lemma T2_view : forall A B R, TI2 A B R -> T2_shape A B R.
Proof.
  intros A B R H; induction H.
  - eapply tsh_atom; [eassumption|apply rel_equiv_refl].
  - eapply tsh_pi; eauto using rel_equiv_refl.
  - eapply tsh_sigma; eauto using rel_equiv_refl.
  - destruct IHTI2.
    + eapply tsh_atom; [eassumption|eapply rel_equiv_trans; [apply rel_equiv_sym; eassumption|eassumption]].
    + eapply tsh_pi; try eassumption; eapply rel_equiv_trans; [apply rel_equiv_sym; eassumption|eassumption].
    + eapply tsh_sigma; try eassumption; eapply rel_equiv_trans; [apply rel_equiv_sym; eassumption|eassumption].
Qed.

Hypothesis atom_conv : forall A B R A' B', atom A B R -> conv A A' -> conv B B' -> atom A' B' R.
Hypothesis atom_not_pi_l : forall A B R x U V, atom A B R -> conv A (TPi x U V) -> False.
Hypothesis atom_not_pi_r : forall A B R x U V, atom A B R -> conv B (TPi x U V) -> False.
Hypothesis atom_not_sigma_l : forall A B R x U V, atom A B R -> conv A (TSigma x U V) -> False.
Hypothesis atom_not_sigma_r : forall A B R x U V, atom A B R -> conv B (TSigma x U V) -> False.
Hypothesis atom_per : forall A B R, atom A B R -> per R /\ conv_closed R.
Hypothesis atom_sym : forall A B R, atom A B R -> atom B A R.
Hypothesis atom_unique_l : forall A B R A' B' S, atom A B R -> atom A' B' S -> conv A A' -> rel_equiv R S.
Hypothesis atom_unique_r : forall A B R A' B' S, atom A B R -> atom A' B' S -> conv B B' -> rel_equiv R S.
Hypothesis atom_trans : forall A B R B' C S, atom A B R -> atom B' C S -> conv B B' -> atom A C R.

Lemma TI2_conv : forall A B R A' B', TI2 A B R -> conv A A' -> conv B B' -> TI2 A' B' R.
Proof.
  intros A B R A' B' H; revert A' B'; induction H; intros A0 B0 HA0 HB0.
  - apply t2_atom; eapply atom_conv; eassumption.
  - eapply t2_pi; [eapply cv_trans; [apply cv_sym; exact HA0|exact H]
      |eapply cv_trans; [apply cv_sym; exact HB0|exact H0]|exact H1|exact H2].
  - eapply t2_sigma; [eapply cv_trans; [apply cv_sym; exact HA0|exact H]
      |eapply cv_trans; [apply cv_sym; exact HB0|exact H0]|exact H1|exact H2].
  - eapply t2_equiv; [apply IHTI2; assumption|assumption].
Qed.

Definition T2_claim A B R :=
  per R /\ conv_closed R /\ TI2 B A R /\
  (forall A' B' S, TI2 A' B' S -> conv A A' -> rel_equiv R S) /\
  (forall A' B' S, TI2 A' B' S -> conv B B' -> rel_equiv R S).

Ltac atom_contra :=
  exfalso; first
  [ eapply atom_not_pi_l; [eassumption|eapply cv_trans; [eassumption|eassumption]]
  | eapply atom_not_pi_r; [eassumption|eapply cv_trans; [eassumption|eassumption]]
  | eapply atom_not_sigma_l; [eassumption|eapply cv_trans; [eassumption|eassumption]]
  | eapply atom_not_sigma_r; [eassumption|eapply cv_trans; [eassumption|eassumption]]
  | eapply atom_not_pi_l; [eassumption|eapply cv_trans; [apply cv_sym; eassumption|eassumption]]
  | eapply atom_not_pi_r; [eassumption|eapply cv_trans; [apply cv_sym; eassumption|eassumption]]
  | eapply atom_not_sigma_l; [eassumption|eapply cv_trans; [apply cv_sym; eassumption|eassumption]]
  | eapply atom_not_sigma_r; [eassumption|eapply cv_trans; [apply cv_sym; eassumption|eassumption]] ].

Lemma T2_claims : forall A B R, TI2 A B R -> T2_claim A B R.
Proof.
  intros A B R H; induction H as
    [A B R HA
    |A B x U V y U' V' RU RV HA HB HU IHU HV IHV
    |A B x U V y U' V' RU RV HA HB HU IHU HV IHV
    |A B R S H IH HE].
  - destruct (atom_per _ _ _ HA) as [Hp Hc]; claim_split; try assumption.
    + apply t2_atom, atom_sym, HA.
    + intros A' B' S HS Hcv; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * eapply rel_equiv_trans; [eapply atom_unique_l; eassumption|apply rel_equiv_sym; exact HR'].
      * exfalso; eapply atom_not_pi_l; [exact HA|eapply cv_trans; [exact Hcv|exact Ha0]].
      * exfalso; eapply atom_not_sigma_l; [exact HA|eapply cv_trans; [exact Hcv|exact Ha0]].
    + intros A' B' S HS Hcv; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * eapply rel_equiv_trans; [eapply atom_unique_r; eassumption|apply rel_equiv_sym; exact HR'].
      * exfalso; eapply atom_not_pi_r; [exact HA|eapply cv_trans; [exact Hcv|exact Hb0]].
      * exfalso; eapply atom_not_sigma_r; [exact HA|eapply cv_trans; [exact Hcv|exact Hb0]].
  - destruct IHU as [HUp [HUc [HUs [HUl HUr]]]].
    assert (Hcf : cfam RU RV).
    { intros a b Ha Hb Hab. destruct (IHV a b Ha Hb Hab) as [Hp [Hc [_ [Hl Hr]]]].
      refine (conj Hp (conj Hc (conj _ _))).
      - eapply Hl; [apply HV; [exact Ha|exact Ha|eapply per_refl_left; eassumption]|apply cv_refl].
      - eapply Hr; [apply HV; [exact Hb|exact Hb|eapply per_refl_right; eassumption]|apply cv_refl]. }
    claim_split.
    + apply pi_rel_per; assumption.
    + apply pi_rel_conv_on; intros a b Ha Hb Hab; apply (Hcf a b Ha Hb Hab).
    + eapply t2_equiv; [eapply t2_pi with (RU := RU) (RV := fun b a => RV a b);
        [exact HB|exact HA|exact HUs|]|apply pi_rel_flip; assumption].
      intros b a Hb Ha Hba.
      destruct (IHV a b Ha Hb (proj1 HUp _ _ Hba)) as [_ [_ [Hs _]]]; exact Hs.
    + intros A' B' S HS Hc; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * exfalso; eapply atom_not_pi_l; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HA]].
      * destruct (conv_pi_inv x U V x0 U0 V0 (cv_trans (cv_sym HA) (cv_trans Hc Ha0))) as [HUU HVV].
        pose proof (HUl _ _ _ HU0 HUU) as HRU.
        eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
        apply pi_rel_equiv; [exact HRU|]. intros a b Ha Hb Hab.
        destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [Hl _]]]].
        eapply Hl; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Ha].
      * shape_contra.
    + intros A' B' S HS Hc; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * exfalso; eapply atom_not_pi_r; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]].
      * destruct (conv_pi_inv y U' V' y0 U0' V0' (cv_trans (cv_sym HB) (cv_trans Hc Hb0))) as [HUU HVV].
        pose proof (HUr _ _ _ HU0 HUU) as HRU.
        eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
        apply pi_rel_equiv; [exact HRU|]. intros a b Ha Hb Hab.
        destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [_ Hr]]]].
        eapply Hr; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Hb].
      * shape_contra.
  - destruct IHU as [HUp [HUc [HUs [HUl HUr]]]].
    assert (Hcf : cfam RU RV).
    { intros a b Ha Hb Hab. destruct (IHV a b Ha Hb Hab) as [Hp [Hc [_ [Hl Hr]]]].
      refine (conj Hp (conj Hc (conj _ _))).
      - eapply Hl; [apply HV; [exact Ha|exact Ha|eapply per_refl_left; eassumption]|apply cv_refl].
      - eapply Hr; [apply HV; [exact Hb|exact Hb|eapply per_refl_right; eassumption]|apply cv_refl]. }
    claim_split.
    + apply sigma_rel_per; assumption.
    + apply sigma_rel_conv.
    + eapply t2_equiv; [eapply t2_sigma with (RU := RU) (RV := fun b a => RV a b);
        [exact HB|exact HA|exact HUs|]|apply sigma_rel_flip; assumption].
      intros b a Hb Ha Hba.
      destruct (IHV a b Ha Hb (proj1 HUp _ _ Hba)) as [_ [_ [Hs _]]]; exact Hs.
    + intros A' B' S HS Hc; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * exfalso; eapply atom_not_sigma_l; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HA]].
      * shape_contra.
      * destruct (conv_sigma_inv x U V x0 U0 V0 (cv_trans (cv_sym HA) (cv_trans Hc Ha0))) as [HUU HVV].
        pose proof (HUl _ _ _ HU0 HUU) as HRU.
        eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
        apply sigma_rel_equiv; [exact HRU|]. intros a b Ha Hb Hab.
        destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [Hl _]]]].
        eapply Hl; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Ha].
    + intros A' B' S HS Hc; destruct (T2_view _ _ _ HS) as
        [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
      * exfalso; eapply atom_not_sigma_r; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]].
      * shape_contra.
      * destruct (conv_sigma_inv y U' V' y0 U0' V0' (cv_trans (cv_sym HB) (cv_trans Hc Hb0))) as [HUU HVV].
        pose proof (HUr _ _ _ HU0 HUU) as HRU.
        eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
        apply sigma_rel_equiv; [exact HRU|]. intros a b Ha Hb Hab.
        destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [_ Hr]]]].
        eapply Hr; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Hb].
  - destruct IH as [Hp [Hc [Hs [Hl Hr]]]]; claim_split.
    + eapply per_equiv; eassumption.
    + eapply conv_closed_equiv; eassumption.
    + eapply t2_equiv; eassumption.
    + intros; eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eapply Hl; eassumption].
    + intros; eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eapply Hr; eassumption].
Qed.

Lemma TI2_per : forall A B R, TI2 A B R -> per R.
Proof. intros A B R H; exact (proj1 (T2_claims _ _ _ H)). Qed.
Lemma TI2_conv_closed : forall A B R, TI2 A B R -> conv_closed R.
Proof. intros A B R H; exact (proj1 (proj2 (T2_claims _ _ _ H))). Qed.
Lemma TI2_sym : forall A B R, TI2 A B R -> TI2 B A R.
Proof. intros A B R H; exact (proj1 (proj2 (proj2 (T2_claims _ _ _ H)))). Qed.
Lemma TI2_unique_left : forall A B R A' B' S, TI2 A B R -> TI2 A' B' S -> conv A A' -> rel_equiv R S.
Proof. intros A B R A' B' S H; exact (proj1 (proj2 (proj2 (proj2 (T2_claims _ _ _ H)))) A' B' S). Qed.
Lemma TI2_unique_right : forall A B R A' B' S, TI2 A B R -> TI2 A' B' S -> conv B B' -> rel_equiv R S.
Proof. intros A B R A' B' S H; exact (proj2 (proj2 (proj2 (proj2 (T2_claims _ _ _ H)))) A' B' S). Qed.

Lemma TI2_trans : forall A B R B' C S, TI2 A B R -> TI2 B' C S -> conv B B' -> TI2 A C R.
Proof.
  intros A B R B' C S H; revert B' C S; induction H as
    [A B R HA
    |A B x U V y U' V' RU RV HA HB HU IHU HV IHV
    |A B x U V y U' V' RU RV HA HB HU IHU HV IHV
    |A B R S0 H IH HE]; intros B' C S HS Hc.
  - destruct (T2_view _ _ _ HS) as
      [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
    + apply t2_atom; eapply atom_trans; eassumption.
    + exfalso; eapply atom_not_pi_r; [exact HA|eapply cv_trans; [exact Hc|exact Ha0]].
    + exfalso; eapply atom_not_sigma_r; [exact HA|eapply cv_trans; [exact Hc|exact Ha0]].
  - destruct (T2_view _ _ _ HS) as
      [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
    + exfalso; eapply atom_not_pi_l; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]].
    + destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Ha0))) as [HUU HVV].
      pose proof (TI2_unique_left _ _ _ _ _ _ (TI2_sym _ _ _ HU) HU0 HUU) as HRU.
      pose proof (TI2_per _ _ _ HU) as HP.
      eapply t2_pi; [exact HA|exact Hb0|eapply IHU; [exact HU0|exact HUU]|].
      intros a c Ha Hc' Hac.
      eapply IHV; [exact Ha|exact Hc'|exact Hac|apply HV0; [exact Hc'|exact Hc'|]|apply HVV; exact Hc'].
      apply HRU; eapply per_refl_right; eassumption.
    + shape_contra.
  - destruct (T2_view _ _ _ HS) as
      [R' HA' HR'|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0|x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0].
    + exfalso; eapply atom_not_sigma_l; [exact HA'|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]].
    + shape_contra.
    + destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Ha0))) as [HUU HVV].
      pose proof (TI2_unique_left _ _ _ _ _ _ (TI2_sym _ _ _ HU) HU0 HUU) as HRU.
      pose proof (TI2_per _ _ _ HU) as HP.
      eapply t2_sigma; [exact HA|exact Hb0|eapply IHU; [exact HU0|exact HUU]|].
      intros a c Ha Hc' Hac.
      eapply IHV; [exact Ha|exact Hc'|exact Hac|apply HV0; [exact Hc'|exact Hc'|]|apply HVV; exact Hc'].
      apply HRU; eapply per_refl_right; eassumption.
  - eapply t2_equiv; [eapply IH; eassumption|exact HE].
Qed.

End Structural.

Lemma TI2_monotone : forall (atom atom' : term -> term -> rel -> Prop),
  (forall A B R, atom A B R -> atom' A B R) ->
  forall A B R, TI2 atom A B R -> TI2 atom' A B R.
Proof.
  intros atom atom' Hm A B R H; induction H.
  - apply t2_atom, Hm, H.
  - eapply t2_pi; eassumption.
  - eapply t2_sigma; eassumption.
  - eapply t2_equiv; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Facts about small types used as atoms *)

Lemma S2_not_pi_r : forall A B R x U V, S2 A B R ->
  (forall x0 U0 V0, ~ conv A (TPi x0 U0 V0)) -> conv B (TPi x U V) -> False.
Proof.
  intros A B R x U V H HA HB; destruct (S2_view _ _ _ H) as [ Ha Hb HR | Ha Hb HR | Ha Hb HR | E E' L Ha Hb HE HE' HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | IT D i IT' D' i' RI F Ha Hb HI Hi Hi' Hii HD HR | IT Fd G i IT' Fd' G' i' RI FF FG Ha Hb HI Hi Hi' Hii HF HG HR ].
  all: try (eapply HA; exact Ha).
  all: eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HB|exact Hb]
      |reflexivity|reflexivity|discriminate].
Qed.
Lemma S2_not_sigma_r : forall A B R x U V, S2 A B R ->
  (forall x0 U0 V0, ~ conv A (TSigma x0 U0 V0)) -> conv B (TSigma x U V) -> False.
Proof.
  intros A B R x U V H HA HB; destruct (S2_view _ _ _ H) as [ Ha Hb HR | Ha Hb HR | Ha Hb HR | E E' L Ha Hb HE HE' HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | IT D i IT' D' i' RI F Ha Hb HI Hi Hi' Hii HD HR | IT Fd G i IT' Fd' G' i' RI FF FG Ha Hb HI Hi Hi' Hii HF HG HR ].
  all: try (eapply HA; exact Ha).
  all: eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HB|exact Hb]
      |reflexivity|reflexivity|discriminate].
Qed.
Lemma S2_not_head_l : forall A B R n, S2 A B R -> conv A n ->
  term_head n = Some h_sort \/ (exists IT, n = TIDesc IT) -> False.
Proof.
  intros A B R n H HA Hn; destruct (S2_view _ _ _ H) as [ Ha Hb HR | Ha Hb HR | Ha Hb HR | E E' L Ha Hb HE HE' HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | x0 U0 V0 y0 U0' V0' RU RV Ha Hb HU HV HR | IT D i IT' D' i' RI F Ha Hb HI Hi Hi' Hii HD HR | IT Fd G i IT' Fd' G' i' RI FF FG Ha Hb HI Hi Hi' Hii HF HG HR ];
    destruct Hn as [Hn|[IT0 ->]];
    (eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HA|exact Ha]
      |try exact Hn; reflexivity|reflexivity|discriminate]).
Qed.
Lemma S2_not_head_r : forall A B R n, S2 A B R -> conv B n ->
  term_head n = Some h_sort \/ (exists IT, n = TIDesc IT) -> False.
Proof. intros A B R n H; apply S2_not_head_l with A R, S2_sym, H. Qed.

Lemma D2_rel_equiv : forall RI D D' F, D2 RI D D' F -> forall RI', rel_equiv RI RI' -> D2 RI' D D' F.
Proof.
  intros RI D D' F H; induction H; intros RI' HE.
  - eapply d2_var; try eassumption; apply HE; assumption.
  - apply d2_one; assumption.
  - apply d2_bot; assumption.
  - eapply d2_prod; eauto.
  - eapply d2_pi; eauto.
  - eapply d2_sig; eauto.
  - eapply d2_choice; eauto.
  - eapply d2_equiv; [apply IHD2; exact HE|]. eapply fequiv_rel; [apply rel_equiv_sym; exact HE|exact H0].
Qed.

Definition desc_rel (RI : rel) : rel := fun D D' => exists F, D2 RI D D' F.

Lemma desc_rel_per : forall RI, per RI -> conv_closed RI -> per (desc_rel RI).
Proof.
  intros RI HP HC; split.
  - intros D D' [F H]; exists F; apply D2_sym; assumption.
  - intros D D' D'' [F H] [G H']; exists F; eapply D2_trans; [exact H|exact HP|exact HC|exact H'
      |apply rel_equiv_refl|apply cv_refl].
Qed.
Lemma desc_rel_conv : forall RI, conv_closed (desc_rel RI).
Proof. intros RI D D2' E E' [F H] HD HE; exists F; eapply D2_conv; eassumption. Qed.
Lemma desc_rel_equiv : forall RI RI', rel_equiv RI RI' -> rel_equiv (desc_rel RI) (desc_rel RI').
Proof.
  intros RI RI' HE D D'; split; intros [F H]; exists F; eapply D2_rel_equiv;
    [exact H|exact HE|exact H|apply rel_equiv_sym; exact HE].
Qed.

(* ------------------------------------------------------------------ *)
(* Level atoms *)

Definition no_pi (A : term) := forall x U V, ~ conv A (TPi x U V).
Definition no_sigma (A : term) := forall x U V, ~ conv A (TSigma x U V).

Inductive atom2 (k : nat) (levels : list rel) : term -> term -> rel -> Prop :=
| a2_small : forall A B R, S2 A B R -> no_pi A -> no_sigma A -> atom2 k levels A B R
| a2_sort : forall A B j R, nth_error levels j = Some R ->
    conv A (TSort j) -> conv B (TSort j) -> atom2 k levels A B R
| a2_idesc : forall A B IT IT' RI, 0 < k -> S2 IT IT' RI ->
    conv A (TIDesc IT) -> conv B (TIDesc IT') -> atom2 k levels A B (desc_rel RI).

Definition levels_ok (levels : list rel) :=
  forall j R, nth_error levels j = Some R -> per R /\ conv_closed R.

Section LevelAtoms.
Variable k : nat.
Variable levels : list rel.
Hypothesis Hlevels : levels_ok levels.

Lemma no_pi_conv : forall A A', no_pi A -> conv A A' -> no_pi A'.
Proof. intros A A' H Hc x U V H'; eapply H; eapply cv_trans; eassumption. Qed.
Lemma no_sigma_conv : forall A A', no_sigma A -> conv A A' -> no_sigma A'.
Proof. intros A A' H Hc x U V H'; eapply H; eapply cv_trans; eassumption. Qed.

Lemma atom2_conv : forall A B R A' B', atom2 k levels A B R -> conv A A' -> conv B B' ->
  atom2 k levels A' B' R.
Proof.
  intros A B R A' B' H HA HB; destruct H.
  - apply a2_small; [eapply S2_conv; eassumption|eapply no_pi_conv; eassumption
      |eapply no_sigma_conv; eassumption].
  - eapply a2_sort; [eassumption|eapply cv_trans; [apply cv_sym; exact HA|eassumption]
      |eapply cv_trans; [apply cv_sym; exact HB|eassumption]].
  - eapply a2_idesc; [eassumption|eassumption|eapply cv_trans; [apply cv_sym; exact HA|eassumption]
      |eapply cv_trans; [apply cv_sym; exact HB|eassumption]].
Qed.

Lemma atom2_not_pi_l : forall A B R x U V, atom2 k levels A B R -> conv A (TPi x U V) -> False.
Proof.
  intros A B R x U V H Hc; destruct H as [A0 B0 R0 HS Hp Hs|A0 B0 j R0 Hj HA HB|A0 B0 IT IT' RI Hk HI HA HB].
  - eapply Hp; exact Hc.
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|reflexivity|reflexivity|discriminate].
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|reflexivity|reflexivity|discriminate].
Qed.
Lemma atom2_not_pi_r : forall A B R x U V, atom2 k levels A B R -> conv B (TPi x U V) -> False.
Proof.
  intros A B R x U V H Hc; destruct H as [A0 B0 R0 HS Hp Hs|A0 B0 j R0 Hj HA HB|A0 B0 IT IT' RI Hk HI HA HB].
  - eapply S2_not_pi_r; eassumption.
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|reflexivity|reflexivity|discriminate].
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|reflexivity|reflexivity|discriminate].
Qed.
Lemma atom2_not_sigma_l : forall A B R x U V, atom2 k levels A B R -> conv A (TSigma x U V) -> False.
Proof.
  intros A B R x U V H Hc; destruct H as [A0 B0 R0 HS Hp Hs|A0 B0 j R0 Hj HA HB|A0 B0 IT IT' RI Hk HI HA HB].
  - eapply Hs; exact Hc.
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|reflexivity|reflexivity|discriminate].
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|reflexivity|reflexivity|discriminate].
Qed.
Lemma atom2_not_sigma_r : forall A B R x U V, atom2 k levels A B R -> conv B (TSigma x U V) -> False.
Proof.
  intros A B R x U V H Hc; destruct H as [A0 B0 R0 HS Hp Hs|A0 B0 j R0 Hj HA HB|A0 B0 IT IT' RI Hk HI HA HB].
  - eapply S2_not_sigma_r; eassumption.
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|reflexivity|reflexivity|discriminate].
  - eapply head_clash; [eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|reflexivity|reflexivity|discriminate].
Qed.

Lemma atom2_per : forall A B R, atom2 k levels A B R -> per R /\ conv_closed R.
Proof.
  intros A B R H; destruct H.
  - split; [eapply S2_per|eapply S2_conv_closed]; eassumption.
  - eapply Hlevels; eassumption.
  - split; [apply desc_rel_per; [eapply S2_per|eapply S2_conv_closed]; eassumption|apply desc_rel_conv].
Qed.

Lemma atom2_sym : forall A B R, atom2 k levels A B R -> atom2 k levels B A R.
Proof.
  intros A B R H; destruct H.
  - apply a2_small; [apply S2_sym; exact H|intros x U V Hc; eapply S2_not_pi_r; eassumption
      |intros x U V Hc; eapply S2_not_sigma_r; eassumption].
  - eapply a2_sort; eassumption.
  - eapply a2_idesc; [eassumption|apply S2_sym; eassumption|eassumption|eassumption].
Qed.

Lemma atom2_unique_l : forall A B R A' B' S, atom2 k levels A B R -> atom2 k levels A' B' S ->
  conv A A' -> rel_equiv R S.
Proof.
  intros A B R A' B' S H H' Hc; destruct H as [A B R HS Hp Hs|A B j R Hj HA HB|A B IT IT' RI Hk HI HA HB];
    destruct H' as [A2 B2 R2 HS2 Hp2 Hs2|A2 B2 j2 R2 Hj2 HA2 HB2|A2 B2 IT2 IT2' RI2 Hk2 HI2 HA2 HB2].
  - eapply S2_unique_left; eassumption.
  - exfalso; eapply S2_not_head_l; [exact HS|eapply cv_trans; [exact Hc|exact HA2]|left; reflexivity].
  - exfalso; eapply S2_not_head_l; [exact HS|eapply cv_trans; [exact Hc|exact HA2]|right; eexists; reflexivity].
  - exfalso; eapply S2_not_head_l; [exact HS2|eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|left; reflexivity].
  - assert (j = j2) by (apply conv_sort_inv; eapply cv_trans; [apply cv_sym; exact HA|eapply cv_trans; [exact Hc|exact HA2]]).
    subst j2; rewrite Hj in Hj2; inversion Hj2; subst; apply rel_equiv_refl.
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HA|eapply cv_trans; [exact Hc|exact HA2]]
      |reflexivity|reflexivity|discriminate].
  - exfalso; eapply S2_not_head_l; [exact HS2|eapply cv_trans; [apply cv_sym; exact Hc|exact HA]|right; eexists; reflexivity].
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HA|eapply cv_trans; [exact Hc|exact HA2]]
      |reflexivity|reflexivity|discriminate].
  - apply desc_rel_equiv. eapply S2_unique_left; [exact HI|exact HI2|].
    apply conv_idesc; eapply cv_trans; [apply cv_sym; exact HA|eapply cv_trans; [exact Hc|exact HA2]].
Qed.

Lemma atom2_unique_r : forall A B R A' B' S, atom2 k levels A B R -> atom2 k levels A' B' S ->
  conv B B' -> rel_equiv R S.
Proof.
  intros A B R A' B' S H H' Hc.
  eapply atom2_unique_l; [apply atom2_sym; exact H|apply atom2_sym; exact H'|exact Hc].
Qed.

Lemma atom2_trans : forall A B R B' C S, atom2 k levels A B R -> atom2 k levels B' C S ->
  conv B B' -> atom2 k levels A C R.
Proof.
  intros A B R B' C S H H' Hc; destruct H as [A B R HS Hp Hs|A B j R Hj HA HB|A B IT IT' RI Hk HI HA HB];
    destruct H' as [A2 B2 R2 HS2 Hp2 Hs2|A2 B2 j2 R2 Hj2 HA2 HB2|A2 B2 IT2 IT2' RI2 Hk2 HI2 HA2 HB2].
  - apply a2_small; [eapply S2_trans; eassumption|assumption|assumption].
  - exfalso; eapply S2_not_head_r; [exact HS|eapply cv_trans; [exact Hc|exact HA2]|left; reflexivity].
  - exfalso; eapply S2_not_head_r; [exact HS|eapply cv_trans; [exact Hc|exact HA2]|right; eexists; reflexivity].
  - exfalso; eapply S2_not_head_l; [exact HS2|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|left; reflexivity].
  - assert (j = j2) by (apply conv_sort_inv; eapply cv_trans; [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact HA2]]).
    subst j2; eapply a2_sort; eassumption.
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact HA2]]
      |reflexivity|reflexivity|discriminate].
  - exfalso; eapply S2_not_head_l; [exact HS2|eapply cv_trans; [apply cv_sym; exact Hc|exact HB]|right; eexists; reflexivity].
  - exfalso; eapply head_clash; [eapply cv_trans; [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact HA2]]
      |reflexivity|reflexivity|discriminate].
  - eapply a2_idesc; [exact Hk|eapply S2_trans; [exact HI|exact HI2|]|exact HA|exact HB2].
    apply conv_idesc; eapply cv_trans; [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact HA2]].
Qed.

End LevelAtoms.

(* Structural closure over level atoms satisfies all generic laws whenever
   the lower universe relations are conversion-closed PERs. *)
Section LevelLaws.
Variable k : nat.
Variable levels : list rel.
Hypothesis Hlevels : levels_ok levels.

Let A2 := atom2 k levels.
Lemma level_per : forall A B R, TI2 A2 A B R -> per R.
Proof.
  apply TI2_per; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r].
Qed.
Lemma level_conv_closed : forall A B R, TI2 A2 A B R -> conv_closed R.
Proof.
  apply TI2_conv_closed; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r].
Qed.
Lemma level_sym : forall A B R, TI2 A2 A B R -> TI2 A2 B A R.
Proof.
  apply TI2_sym; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r].
Qed.
Lemma level_unique_left : forall A B R A' B' S, TI2 A2 A B R -> TI2 A2 A' B' S ->
  conv A A' -> rel_equiv R S.
Proof.
  apply TI2_unique_left; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r].
Qed.
Lemma level_unique_right : forall A B R A' B' S, TI2 A2 A B R -> TI2 A2 A' B' S ->
  conv B B' -> rel_equiv R S.
Proof.
  apply TI2_unique_right; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r].
Qed.
Lemma level_trans : forall A B R B' C S, TI2 A2 A B R -> TI2 A2 B' C S -> conv B B' ->
  TI2 A2 A C R.
Proof.
  apply TI2_trans; [apply atom2_not_pi_l|apply atom2_not_pi_r|apply atom2_not_sigma_l
    |apply atom2_not_sigma_r|apply atom2_per; exact Hlevels|apply atom2_sym
    |apply atom2_unique_l|apply atom2_unique_r|apply atom2_trans].
Qed.
Lemma level_conv : forall A B R A' B', TI2 A2 A B R -> conv A A' -> conv B B' -> TI2 A2 A' B' R.
Proof. apply TI2_conv, atom2_conv. Qed.
End LevelLaws.

(* ------------------------------------------------------------------ *)
(* The tower *)

Fixpoint levels (n : nat) : list rel :=
  match n with
  | 0 => []
  | S k => levels k ++ [fun A B => exists R, TI2 (atom2 k (levels k)) A B R]
  end.
Definition interp (k : nat) : term -> term -> rel -> Prop := TI2 (atom2 k (levels k)).
Definition univ_rel (k : nat) : rel := fun A B => exists R, interp k A B R.

Lemma levels_length : forall n, List.length (levels n) = n.
Proof. induction n; cbn [levels]; [reflexivity|rewrite length_app, IHn; cbn; lia]. Qed.
Lemma levels_lookup : forall j n, j < n -> nth_error (levels n) j = Some (univ_rel j).
Proof.
  intros j n; revert j; induction n; intros j H; [lia|].
  cbn [levels]; destruct (Nat.eq_dec j n) as [->|Hne].
  - rewrite nth_error_app2 by (rewrite levels_length; lia).
    rewrite levels_length, Nat.sub_diag; reflexivity.
  - rewrite nth_error_app1 by (rewrite levels_length; lia). apply IHn; lia.
Qed.
Lemma levels_lookup_inv : forall j n R, nth_error (levels n) j = Some R -> j < n /\ R = univ_rel j.
Proof.
  intros j n R H.
  assert (Hj : j < n) by (rewrite <- (levels_length n); apply nth_error_Some; congruence).
  split; [exact Hj|]. rewrite levels_lookup in H by exact Hj. congruence.
Qed.

Theorem levels_good : forall n, levels_ok (levels n).
Proof.
  induction n; intros j R H.
  - destruct j; discriminate.
  - destruct (levels_lookup_inv _ _ _ H) as [Hj ->].
    destruct (Nat.eq_dec j n) as [->|Hne].
    + split.
      * split.
        -- intros A B [R HR]; exists R; apply level_sym; [exact IHn|exact HR].
        -- intros A B C [R HR] [S HS]; exists R; eapply level_trans; [exact IHn|exact HR|exact HS|apply cv_refl].
      * intros A A' B B' [R HR] HA HB; exists R; eapply level_conv; eassumption.
    + apply (IHn j); apply levels_lookup; lia.
Qed.

Lemma interp_per : forall k A B R, interp k A B R -> per R.
Proof. intros k; apply level_per, levels_good. Qed.
Lemma interp_conv_closed : forall k A B R, interp k A B R -> conv_closed R.
Proof. intros k; apply level_conv_closed, levels_good. Qed.
Lemma interp_sym : forall k A B R, interp k A B R -> interp k B A R.
Proof. intros k; apply level_sym, levels_good. Qed.
Lemma interp_trans : forall k A B R B' C S, interp k A B R -> interp k B' C S -> conv B B' -> interp k A C R.
Proof. intros k; apply level_trans, levels_good. Qed.
Lemma interp_conv : forall k A B R A' B', interp k A B R -> conv A A' -> conv B B' -> interp k A' B' R.
Proof. intros k; apply level_conv. Qed.
Lemma interp_refl_left : forall k A B R, interp k A B R -> interp k A A R.
Proof. intros k A B R H; eapply interp_trans; [exact H|apply interp_sym, H|apply cv_refl]. Qed.
Lemma interp_refl_right : forall k A B R, interp k A B R -> interp k B B R.
Proof. intros k A B R H; eapply interp_trans; [apply interp_sym, H|exact H|apply cv_refl]. Qed.
Lemma interp_equiv : forall k A B R S, interp k A B R -> rel_equiv R S -> interp k A B S.
Proof. intros; eapply t2_equiv; eassumption. Qed.

(* Cumulativity *)
Lemma levels_prefix : forall j n m R, j <= n -> nth_error (levels j) m = Some R ->
  nth_error (levels n) m = Some R.
Proof.
  intros j n m R Hjn H. destruct (levels_lookup_inv _ _ _ H) as [Hm ->].
  apply levels_lookup; lia.
Qed.
Lemma atom2_cumulative : forall j n, j <= n -> forall A B R,
  atom2 j (levels j) A B R -> atom2 n (levels n) A B R.
Proof.
  intros j n Hjn A B R H; destruct H.
  - apply a2_small; assumption.
  - eapply a2_sort; [eapply levels_prefix; eassumption|assumption|assumption].
  - eapply a2_idesc; [lia|eassumption|eassumption|eassumption].
Qed.
Lemma interp_cumulative : forall j n A B R, j <= n -> interp j A B R -> interp n A B R.
Proof. intros j n A B R Hjn; apply TI2_monotone, atom2_cumulative, Hjn. Qed.

Lemma interp_unique_left : forall j n A B R A' B' S, interp j A B R -> interp n A' B' S ->
  conv A A' -> rel_equiv R S.
Proof.
  intros j n A B R A' B' S H H' Hc.
  eapply (level_unique_left (Nat.max j n)); [apply levels_good
    |apply (interp_cumulative j); [lia|exact H]
    |apply (interp_cumulative n); [lia|exact H']|exact Hc].
Qed.
Lemma interp_unique_right : forall j n A B R A' B' S, interp j A B R -> interp n A' B' S ->
  conv B B' -> rel_equiv R S.
Proof.
  intros j n A B R A' B' S H H' Hc.
  eapply (level_unique_right (Nat.max j n)); [apply levels_good
    |apply (interp_cumulative j); [lia|exact H]
    |apply (interp_cumulative n); [lia|exact H']|exact Hc].
Qed.
Lemma interp_trans_levels : forall j n A B R B' C S, interp j A B R -> interp n B' C S ->
  conv B B' -> interp (Nat.max j n) A C R.
Proof.
  intros j n A B R B' C S H H' Hc.
  eapply interp_trans; [apply (interp_cumulative j); [lia|exact H]
    |apply (interp_cumulative n); [lia|exact H']|exact Hc].
Qed.

(* Small types are exactly level zero. *)
Ltac head_contra2 := exfalso; match goal with
  | H1 : conv ?A ?n1, H2 : conv ?A ?n2 |- _ =>
      eapply head_clash with (t := n1) (u := n2);
      [eapply cv_trans; [apply cv_sym; exact H1|exact H2]|reflexivity|reflexivity|discriminate]
  end.

Lemma S2_interp : forall k A B R, S2 A B R -> interp k A B R.
Proof.
  intros k A B R H; induction H.
  - apply t2_atom, a2_small; [apply s2_unit; assumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - apply t2_atom, a2_small; [apply s2_uid; assumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - apply t2_atom, a2_small; [apply s2_enumu; assumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - apply t2_atom, a2_small; [eapply s2_enum; eassumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - eapply t2_pi; eassumption.
  - eapply t2_sigma; eassumption.
  - apply t2_atom, a2_small; [eapply s2_mu; eassumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - apply t2_atom, a2_small; [eapply s2_close; eassumption
      |intros x0 U0 V0 Hc; head_contra2|intros x0 U0 V0 Hc; head_contra2].
  - eapply t2_equiv; eassumption.
Qed.

Lemma interp0_S2 : forall A B R, interp 0 A B R -> S2 A B R.
Proof.
  intros A B R H; induction H.
  - destruct H; [assumption|destruct j; discriminate|lia].
  - eapply s2_pi; eassumption.
  - eapply s2_sigma; eassumption.
  - eapply s2_equiv; eassumption.
Qed.
