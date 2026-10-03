(* Every small type relation is a conversion-closed PER, symmetric in its
   two types, and determined by either type. Every interpreted description is
   a good functor with the same properties. Proved simultaneously. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelSmall.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Relation-former lemmas *)

Definition cfam (RA : rel) (RB : term -> term -> rel) :=
  forall a b, closed a -> closed b -> RA a b ->
    per (RB a b) /\ conv_closed (RB a b) /\
    rel_equiv (RB a b) (RB a a) /\ rel_equiv (RB a b) (RB b b).

Lemma cfam_flip : forall RA RB, per RA -> cfam RA RB ->
  forall a b, closed a -> closed b -> RA a b -> rel_equiv (RB a b) (RB b a).
Proof.
  intros RA RB HP HC a b Ha Hb H.
  destruct (HC a b Ha Hb H) as [_ [_ [_ H1]]].
  destruct (HC b a Hb Ha (proj1 HP _ _ H)) as [_ [_ [H2 _]]].
  eapply rel_equiv_trans; [exact H1|apply rel_equiv_sym; exact H2].
Qed.
Lemma cfam_conv_index : forall RA RB, per RA -> conv_closed RA -> cfam RA RB ->
  forall a b b', closed a -> closed b -> closed b' -> RA a b -> conv b b' ->
  rel_equiv (RB a b) (RB a b').
Proof.
  intros RA RB HP HCA HC a b b' Ha Hb Hb' H Hc.
  assert (H' : RA a b') by (eapply HCA; [exact H|apply cv_refl|exact Hc]).
  destruct (HC a b Ha Hb H) as [_ [_ [H1 _]]]; destruct (HC a b' Ha Hb' H') as [_ [_ [H2 _]]].
  eapply rel_equiv_trans; [exact H1|apply rel_equiv_sym; exact H2].
Qed.

Lemma pi_rel_equiv : forall RA RA' RB RB', rel_equiv RA RA' ->
  (forall a b, closed a -> closed b -> RA a b -> rel_equiv (RB a b) (RB' a b)) ->
  rel_equiv (pi_rel RA RB) (pi_rel RA' RB').
Proof.
  intros RA RA' RB RB' HA HB f g; split; intros H a b Ha Hb Hab.
  - apply (HB a b Ha Hb (proj2 (HA a b) Hab)), H; try assumption; apply HA, Hab.
  - apply (HB a b Ha Hb Hab), H; try assumption; apply HA, Hab.
Qed.
Lemma sigma_rel_equiv : forall RA RA' RB RB', rel_equiv RA RA' ->
  (forall a b, closed a -> closed b -> RA a b -> rel_equiv (RB a b) (RB' a b)) ->
  rel_equiv (sigma_rel RA RB) (sigma_rel RA' RB').
Proof.
  intros RA RA' RB RB' HA HB p q; split;
    intros [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]];
    exists a, b, a', b'; repeat apply conj; try assumption.
  - apply HA, HR.
  - apply (HB a a' Ha Ha' HR), HS.
  - apply HA, HR.
  - apply (HB a a' Ha Ha' (proj2 (HA a a') HR)), HS.
Qed.

Lemma pi_rel_per : forall RA RB, per RA -> cfam RA RB -> per (pi_rel RA RB).
Proof.
  intros RA RB HP HC; split.
  - intros f g H a b Ha Hb Hab.
    pose proof (proj1 HP _ _ Hab) as Hba.
    destruct (HC b a Hb Ha Hba) as [[Hs _] _].
    apply (cfam_flip RA RB HP HC a b Ha Hb Hab), Hs, H; assumption.
  - intros f g h H1 H2 a b Ha Hb Hab.
    pose proof (per_refl_right _ _ _ HP Hab) as Hbb.
    destruct (HC a b Ha Hb Hab) as [[_ Ht] [_ [_ HE]]].
    eapply Ht; [apply H1; assumption|apply HE, H2; assumption].
Qed.
(* All codomain relations at mutually related indices coincide. *)
Lemma cfam_same : forall RA RB, per RA -> cfam RA RB ->
  forall a b c d, closed a -> closed b -> closed c -> closed d ->
  RA a b -> RA c d -> RA a c -> rel_equiv (RB a b) (RB c d).
Proof.
  intros RA RB HP HC a b c d Ha Hb Hc Hd Hab Hcd Hac.
  destruct (HC a b Ha Hb Hab) as [_ [_ [E1 _]]].
  destruct (HC c d Hc Hd Hcd) as [_ [_ [E2 _]]].
  destruct (HC a c Ha Hc Hac) as [_ [_ [E3 E4]]].
  eapply rel_equiv_trans; [exact E1|].
  eapply rel_equiv_trans; [apply rel_equiv_sym; exact E3|].
  eapply rel_equiv_trans; [exact E4|apply rel_equiv_sym; exact E2].
Qed.

Lemma sigma_rel_per : forall RA RB, per RA -> conv_closed RA -> cfam RA RB ->
  per (sigma_rel RA RB).
Proof.
  intros RA RB HP HCA HC; split.
  - intros p q [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]].
    pose proof (proj1 HP _ _ HR) as HR'.
    exists a', b', a, b; repeat apply conj; try assumption.
    apply (cfam_same RA RB HP HC a a' a' a Ha Ha' Ha' Ha HR HR' HR).
    destruct (HC a a' Ha Ha' HR) as [[Hs _] _]; apply Hs, HS.
  - intros p q r [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]]
      [c [d [c' [d' [Hc [Hd [Hc' [Hd' [Hq' [Hr [HR' HS']]]]]]]]]]].
    assert (Hpair : conv (TPair a' b') (TPair c d))
      by (eapply cv_trans; [apply cv_sym; exact Hq|exact Hq']).
    destruct (conv_pair_inv _ _ _ _ Hpair) as [Hac Hbd].
    assert (Hac' : RA a c) by (eapply HCA; [exact HR|apply cv_refl|exact Hac]).
    assert (Hacc : RA a c') by (eapply (proj2 HP); [exact Hac'|exact HR']).
    pose proof (per_refl_left _ _ _ HP HR) as Haa.
    exists a, b, c', d'; repeat apply conj; try assumption.
    destruct (HC a a Ha Ha Haa) as [[_ Ht] [Hcl _]].
    apply (cfam_same RA RB HP HC a c' a a Ha Hc' Ha Ha Hacc Haa Haa).
    eapply Ht.
    + eapply Hcl; [apply (cfam_same RA RB HP HC a a' a a Ha Ha' Ha Ha HR Haa Haa); exact HS
        |apply cv_refl|exact Hbd].
    + apply (cfam_same RA RB HP HC c c' a a Hc Hc' Ha Ha HR' Haa (proj1 HP _ _ Hac')); exact HS'.
Qed.

Lemma pi_rel_flip : forall RA RB, per RA -> cfam RA RB ->
  rel_equiv (pi_rel RA (fun a b => RB b a)) (pi_rel RA RB).
Proof.
  intros RA RB HP HC; apply pi_rel_equiv; [apply rel_equiv_refl|].
  intros a b Ha Hb Hab; apply rel_equiv_sym, (cfam_flip RA RB HP HC a b Ha Hb Hab).
Qed.
Lemma sigma_rel_flip : forall RA RB, per RA -> cfam RA RB ->
  rel_equiv (sigma_rel RA (fun a b => RB b a)) (sigma_rel RA RB).
Proof.
  intros RA RB HP HC; apply sigma_rel_equiv; [apply rel_equiv_refl|].
  intros a b Ha Hb Hab; apply rel_equiv_sym, (cfam_flip RA RB HP HC a b Ha Hb Hab).
Qed.

Lemma pi_rel_conv_on : forall RA RB,
  (forall a b, closed a -> closed b -> RA a b -> conv_closed (RB a b)) ->
  conv_closed (pi_rel RA RB).
Proof.
  intros RA RB HB f f' g g' H Hf Hg a b Ha Hb Hab.
  eapply HB; [assumption|assumption|assumption|apply H; assumption
    |apply conv_app_f; exact Hf|apply conv_app_f; exact Hg].
Qed.

(* ------------------------------------------------------------------ *)
(* Claims *)

Definition S2_claim A B R :=
  per R /\ conv_closed R /\ S2 B A R /\
  (forall A' B' S, S2 A' B' S -> conv A A' -> rel_equiv R S) /\
  (forall A' B' S, S2 A' B' S -> conv B B' -> rel_equiv R S).

Ltac claim_split := refine (conj _ (conj _ (conj _ (conj _ _)))).

Lemma claim_unit : forall A B, conv A TUnitT -> conv B TUnitT -> S2_claim A B unit_rel.
Proof.
  intros A B HA HB; claim_split.
  - apply unit_rel_per.
  - apply unit_rel_conv.
  - apply s2_unit; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
Qed.
Lemma claim_uid : forall A B, conv A TUId -> conv B TUId -> S2_claim A B tag_rel.
Proof.
  intros A B HA HB; claim_split.
  - apply tag_rel_per.
  - apply tag_rel_conv.
  - apply s2_uid; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
Qed.
Lemma claim_enumu : forall A B, conv A TEnumU -> conv B TEnumU -> S2_claim A B code_rel.
Proof.
  intros A B HA HB; claim_split.
  - apply code_rel_per.
  - apply code_rel_conv.
  - apply s2_enumu; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    apply rel_equiv_sym; assumption.
Qed.
Lemma claim_enum : forall A B E E' L, conv A (TEnumT E) -> conv B (TEnumT E') ->
  conv E (code L) -> conv E' (code L) -> S2_claim A B (enum_rel (List.length L)).
Proof.
  intros A B E E' L HA HB HE HE'; claim_split.
  - apply enum_rel_per.
  - apply enum_rel_conv.
  - eapply s2_enum; eassumption.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    match goal with H : conv A' (TEnumT ?E2) |- _ =>
      assert (HEE : conv E E2) by (apply conv_enum; eapply cv_trans;
        [apply cv_sym; exact HA|eapply cv_trans; [exact Hc|exact H]]) end.
    match goal with H : conv _ (code ?L2) , H' : rel_equiv S _ |- _ =>
      assert (L = L2) by (apply conv_code_inv; eapply cv_trans;
        [apply cv_sym; exact HE|eapply cv_trans; [exact HEE|exact H]]); subst L2;
      apply rel_equiv_sym; exact H' end.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS); try shape_contra.
    match goal with H : conv B' (TEnumT ?E2) |- _ =>
      assert (HEE : conv E' E2) by (apply conv_enum; eapply cv_trans;
        [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact H]]) end.
    match goal with H : conv _ (code ?L2) , H' : rel_equiv S _ |- _ =>
      assert (L = L2) by (apply conv_code_inv; eapply cv_trans;
        [apply cv_sym; exact HE'|eapply cv_trans; [exact HEE|exact H]]); subst L2;
      apply rel_equiv_sym; exact H' end.
Qed.

Lemma claim_cfam : forall x V y V' RU RV, per RU ->
  (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
  (forall a b, closed a -> closed b -> RU a b -> S2_claim (subst a x V) (subst b y V') (RV a b)) ->
  cfam RU RV.
Proof.
  intros x V y V' RU RV HP HV IHV a b Ha Hb Hab.
  destruct (IHV a b Ha Hb Hab) as [Hp [Hc [_ [Hl Hr]]]].
  refine (conj Hp (conj Hc (conj _ _))).
  - eapply Hl; [apply HV; [exact Ha|exact Ha|eapply per_refl_left; eassumption]|apply cv_refl].
  - eapply Hr; [apply HV; [exact Hb|exact Hb|eapply per_refl_right; eassumption]|apply cv_refl].
Qed.

Lemma claim_pi : forall A B x U V y U' V' RU RV,
  conv A (TPi x U V) -> conv B (TPi y U' V') -> S2_claim U U' RU ->
  (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
  (forall a b, closed a -> closed b -> RU a b -> S2_claim (subst a x V) (subst b y V') (RV a b)) ->
  S2_claim A B (pi_rel RU RV).
Proof.
  intros A B x U V y U' V' RU RV HA HB HU HV IHV.
  destruct HU as [HUp [HUc [HUs [HUl HUr]]]].
  pose proof (claim_cfam x V y V' RU RV HUp HV IHV) as Hcf.
  claim_split.
  - apply pi_rel_per; assumption.
  - apply pi_rel_conv_on; intros a b Ha Hb Hab; apply (Hcf a b Ha Hb Hab).
  - eapply s2_equiv; [eapply s2_pi with (RU := RU) (RV := fun b a => RV a b);
      [exact HB|exact HA|exact HUs|]|apply pi_rel_flip; assumption].
    intros b a Hb Ha Hba.
    destruct (IHV a b Ha Hb (proj1 HUp _ _ Hba)) as [_ [_ [Hs _]]]; exact Hs.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS) as [ | | | | x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0 | | | ]; try shape_contra.
    destruct (conv_pi_inv x U V x0 U0 V0
      (cv_trans (cv_sym HA) (cv_trans Hc Ha0))) as [HUU HVV].
    pose proof (HUl _ _ _ HU0 HUU) as HRU.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
    apply pi_rel_equiv; [exact HRU|].
    intros a b Ha Hb Hab.
    destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [Hl _]]]].
    eapply Hl; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Ha].
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS) as [ | | | | x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0 | | | ]; try shape_contra.
    destruct (conv_pi_inv y U' V' y0 U0' V0'
      (cv_trans (cv_sym HB) (cv_trans Hc Hb0))) as [HUU HVV].
    pose proof (HUr _ _ _ HU0 HUU) as HRU.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
    apply pi_rel_equiv; [exact HRU|].
    intros a b Ha Hb Hab.
    destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [_ Hr]]]].
    eapply Hr; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Hb].
Qed.

Lemma claim_sigma : forall A B x U V y U' V' RU RV,
  conv A (TSigma x U V) -> conv B (TSigma y U' V') -> S2_claim U U' RU ->
  (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
  (forall a b, closed a -> closed b -> RU a b -> S2_claim (subst a x V) (subst b y V') (RV a b)) ->
  S2_claim A B (sigma_rel RU RV).
Proof.
  intros A B x U V y U' V' RU RV HA HB HU HV IHV.
  destruct HU as [HUp [HUc [HUs [HUl HUr]]]].
  pose proof (claim_cfam x V y V' RU RV HUp HV IHV) as Hcf.
  claim_split.
  - apply sigma_rel_per; assumption.
  - apply sigma_rel_conv.
  - eapply s2_equiv; [eapply s2_sigma with (RU := RU) (RV := fun b a => RV a b);
      [exact HB|exact HA|exact HUs|]|apply sigma_rel_flip; assumption].
    intros b a Hb Ha Hba.
    destruct (IHV a b Ha Hb (proj1 HUp _ _ Hba)) as [_ [_ [Hs _]]]; exact Hs.
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS) as [ | | | | | x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0 | | ]; try shape_contra.
    destruct (conv_sigma_inv x U V x0 U0 V0
      (cv_trans (cv_sym HA) (cv_trans Hc Ha0))) as [HUU HVV].
    pose proof (HUl _ _ _ HU0 HUU) as HRU.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
    apply sigma_rel_equiv; [exact HRU|].
    intros a b Ha Hb Hab.
    destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [Hl _]]]].
    eapply Hl; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Ha].
  - intros A' B' S HS Hc; destruct (S2_view _ _ _ HS) as [ | | | | | x0 U0 V0 y0 U0' V0' RU0 RV0 Ha0 Hb0 HU0 HV0 HR0 | | ]; try shape_contra.
    destruct (conv_sigma_inv y U' V' y0 U0' V0'
      (cv_trans (cv_sym HB) (cv_trans Hc Hb0))) as [HUU HVV].
    pose proof (HUr _ _ _ HU0 HUU) as HRU.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR0].
    apply sigma_rel_equiv; [exact HRU|].
    intros a b Ha Hb Hab.
    destruct (IHV a b Ha Hb Hab) as [_ [_ [_ [_ Hr]]]].
    eapply Hr; [apply HV0; [exact Ha|exact Hb|apply HRU, Hab]|apply HVV; exact Hb].
Qed.

(* ------------------------------------------------------------------ *)
(* Description claims *)

Lemma fam_resp_equiv : forall RI RI' X, rel_equiv RI RI' -> fam_resp RI X -> fam_resp RI' X.
Proof.
  intros RI RI' X HE HX i i' Hc Hc' [H|H]; apply HX; try assumption; [left; apply HE, H|right; exact H].
Qed.
Lemma fequiv_rel : forall RI RI' F G, rel_equiv RI RI' -> fequiv RI' F G -> fequiv RI F G.
Proof. intros RI RI' F G HE H X HX; apply H; eapply fam_resp_equiv; eassumption. Qed.

Lemma sigma_rel_mono : forall RA RA' RB RB', rel_incl RA RA' ->
  (forall a b, closed a -> closed b -> RA a b -> rel_incl (RB a b) (RB' a b)) ->
  rel_incl (sigma_rel RA RB) (sigma_rel RA' RB').
Proof.
  intros RA RA' RB RB' HA HB p q [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]].
  exists a, b, a', b'; repeat apply conj; try assumption; [apply HA, HR|eapply HB; eassumption].
Qed.
Lemma pi_rel_mono : forall RA RB RB',
  (forall a b, closed a -> closed b -> RA a b -> rel_incl (RB a b) (RB' a b)) ->
  rel_incl (pi_rel RA RB) (pi_rel RA RB').
Proof. intros RA RB RB' HB f g H a b Ha Hb Hab; eapply HB; try eassumption; apply H; assumption. Qed.

Definition D2_claim RI D D' F :=
  per RI -> conv_closed RI ->
  good_functor RI F /\ D2 RI D' D F /\
  (forall RI' E E' G, D2 RI' E E' G -> rel_equiv RI RI' -> conv D E -> fequiv RI F G) /\
  (forall RI' E E' G, D2 RI' E E' G -> rel_equiv RI RI' -> conv D' E' -> fequiv RI F G).

Ltac dclaim_split := refine (conj _ (conj _ (conj _ _))).
Ltac good_split := refine (conj _ (conj _ (conj _ _))).

Lemma dclaim_var : forall RI D D' i i', conv D (TIVar i) -> conv D' (TIVar i') ->
  closed i -> closed i' -> RI i i' -> D2_claim RI D D' (fun X => X i).
Proof.
  intros RI D D' i i' HD HD' Hi Hi' Hii HP HC; dclaim_split.
  - good_split.
    + intros X Y _ _ HXY t u H; apply HXY, H.
    + intros X Y _ _ H t u Ht; apply H, Ht.
    + intros X Y Z _ _ _ _ _ _ H t u v H1 H2; eapply H; eassumption.
    + intros X _ HX; apply HX, Hi.
  - eapply d2_equiv; [eapply d2_var; [exact HD'|exact HD|exact Hi'|exact Hi|apply (proj1 HP), Hii]|].
    intros X HX; apply HX; [exact Hi'|exact Hi|left; apply (proj1 HP), Hii].
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    match goal with H : conv E (TIVar ?i2), HF : fequiv RI' G _ |- _ =>
      apply fequiv_sym; eapply fequiv_trans; [apply (fequiv_rel _ _ _ _ HE HF)|];
      intros X HX; apply HX; [assumption|exact Hi|right];
      apply cv_sym, conv_ivar_inv; eapply cv_trans; [apply cv_sym; exact HD|eapply cv_trans; [exact Hc|exact H]]
    end.
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    match goal with H : conv E' (TIVar ?i2'), HR : RI' ?i2 ?i2', HF : fequiv RI' G _ |- _ =>
      apply fequiv_sym; eapply fequiv_trans; [apply (fequiv_rel _ _ _ _ HE HF)|];
      assert (Hii2 : conv i' i2') by (apply conv_ivar_inv; eapply cv_trans;
        [apply cv_sym; exact HD'|eapply cv_trans; [exact Hc|exact H]]);
      assert (HR' : RI i2 i') by (eapply HC; [apply HE, HR|apply cv_refl|apply cv_sym; exact Hii2]);
      intros X HX; apply HX; [assumption|exact Hi|left];
      eapply (proj2 HP); [exact HR'|apply (proj1 HP); exact Hii]
    end.
Qed.

Lemma dclaim_one : forall RI D D', conv D TI1 -> conv D' TI1 -> D2_claim RI D D' (fun _ => unit_rel).
Proof.
  intros RI D D' HD HD' HP HC; dclaim_split.
  - good_split.
    + intros X Y _ _ _ t u H; exact H.
    + intros X Y _ _ _ t u H; apply unit_rel_per, H.
    + intros X Y Z _ _ _ _ _ _ _ t u v H1 H2; eapply (proj2 unit_rel_per); eassumption.
    + intros X _ _; apply unit_rel_conv.
  - apply d2_one; assumption.
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    apply fequiv_sym; eapply fequiv_rel; eassumption.
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    apply fequiv_sym; eapply fequiv_rel; eassumption.
Qed.

Lemma dclaim_bot : forall RI D D', conv D TIBot -> conv D' TIBot -> D2_claim RI D D' (fun _ => empty_rel).
Proof.
  intros RI D D' HD HD' HP HC; dclaim_split.
  - good_split.
    + intros X Y _ _ _ t u H; exact H.
    + intros X Y _ _ _ t u H; exact H.
    + intros X Y Z _ _ _ _ _ _ _ t u v H1 H2; exact H1.
    + intros X _ _; apply empty_rel_conv.
  - apply d2_bot; assumption.
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    apply fequiv_sym; eapply fequiv_rel; eassumption.
  - intros RI' E E' G HG HE Hc; destruct (D2_view _ _ _ _ HG); try shape_contra.
    apply fequiv_sym; eapply fequiv_rel; eassumption.
Qed.

Lemma dclaim_prod : forall RI D D' A B A' B' FA FB,
  conv D (TIProd A B) -> conv D' (TIProd A' B') ->
  closed A -> closed B -> closed A' -> closed B' ->
  D2_claim RI A A' FA -> D2_claim RI B B' FB ->
  D2_claim RI D D' (fun X => sigma_rel (FA X) (fun _ _ => FB X)).
Proof.
  intros RI D D' A B A' B' FA FB HD HD' HcA HcB HcA' HcB' IA IB HP HC.
  destruct (IA HP HC) as [[FAm [FAs [FAt FAc]]] [FAsym [FAl FAr]]].
  destruct (IB HP HC) as [[FBm [FBs [FBt FBc]]] [FBsym [FBl FBr]]].
  dclaim_split.
  - good_split.
    + intros X Y HX HY HXY; apply sigma_rel_mono; [apply FAm; assumption|intros; apply FBm; assumption].
    + intros X Y HX HY H p q [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]].
      exists a', b', a, b; repeat apply conj; try assumption;
        [exact (FAs X Y HX HY H _ _ HR)|exact (FBs X Y HX HY H _ _ HS)].
    + intros X Y Z HX HY HZ HXc HYc HZc H p q r
        [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]]
        [c [d [c' [d' [Hc [Hd [Hc' [Hd' [Hq' [Hr [HR' HS']]]]]]]]]]].
      destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hq) Hq')) as [Hac Hbd].
      exists a, b, c', d'; repeat apply conj; try assumption.
      * eapply FAt; [exact HX|exact HY|exact HZ|exact HXc|exact HYc|exact HZc|exact H|exact HR|].
        eapply FAc; [exact HY|exact HYc|exact HR'|apply cv_sym; exact Hac|apply cv_refl].
      * eapply FBt; [exact HX|exact HY|exact HZ|exact HXc|exact HYc|exact HZc|exact H|exact HS|].
        eapply FBc; [exact HY|exact HYc|exact HS'|apply cv_sym; exact Hbd|apply cv_refl].
    + intros X _ _; apply sigma_rel_conv.
  - eapply d2_prod; [exact HD'|exact HD|exact HcA'|exact HcB'|exact HcA|exact HcB|exact FAsym|exact FBsym].
  - intros RI' E E' G HG HE Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | A2 B2 A2' B2' GA GB HE1 HE2 Hk1 Hk2 Hk3 Hk4 HGA HGB HF | | | ];
      try shape_contra.
    destruct (conv_iprod_inv _ _ _ _ (cv_trans (cv_sym HD) (cv_trans Hc HE1))) as [HAA HBB].
    pose proof (FAl _ _ _ _ HGA HE HAA) as EA; pose proof (FBl _ _ _ _ HGB HE HBB) as EB.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HE HF); exact HX].
    apply sigma_rel_equiv; [apply EA, HX|intros; apply EB, HX].
  - intros RI' E E' G HG HE Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | A2 B2 A2' B2' GA GB HE1 HE2 Hk1 Hk2 Hk3 Hk4 HGA HGB HF | | | ];
      try shape_contra.
    destruct (conv_iprod_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc HE2))) as [HAA HBB].
    pose proof (FAr _ _ _ _ HGA HE HAA) as EA; pose proof (FBr _ _ _ _ HGB HE HBB) as EB.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HE HF); exact HX].
    apply sigma_rel_equiv; [apply EA, HX|intros; apply EB, HX].
Qed.

(* Families of functors indexed by a related domain. *)
Lemma dclaim_family_resp : forall RI RA E E' FE, per RI -> conv_closed RI -> per RA ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2_claim RI (TApp E a) (TApp E' a') (FE a)) ->
  forall a a2, closed a -> closed a2 -> RA a a2 -> fequiv RI (FE a) (FE a2).
Proof.
  intros RI RA E E' FE HP HC HAp HE IE a a2 Ha Ha2 H.
  destruct (IE a a2 Ha Ha2 H HP HC) as [_ [_ [_ Hr]]].
  eapply Hr; [apply HE; [exact Ha2|exact Ha2|eapply per_refl_right; eassumption]
    |apply rel_equiv_refl|apply cv_refl].
Qed.

Lemma dclaim_pi : forall RI D D' A E A' E' RA FE,
  conv D (TIPi A E) -> conv D' (TIPi A' E') ->
  closed A -> closed E -> closed A' -> closed E' -> S2_claim A A' RA ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2_claim RI (TApp E a) (TApp E' a') (FE a)) ->
  D2_claim RI D D' (fun X => pi_rel RA (fun a _ => FE a X)).
Proof.
  intros RI D D' A E A' E' RA FE HD HD' HcA HcE HcA' HcE' [HAp [HAc [HAs [HAl HAr]]]] HE IE HP HC.
  pose proof (dclaim_family_resp RI RA E E' FE HP HC HAp HE IE) as Hresp.
  dclaim_split.
  - good_split.
    + intros X Y HX HY HXY; apply pi_rel_mono; intros a b Ha Hb Hab.
      destruct (IE a b Ha Hb Hab HP HC) as [[Hm _] _]; apply Hm; assumption.
    + intros X Y HX HY H f g Hfg a b Ha Hb Hab.
      pose proof (proj1 HAp _ _ Hab) as Hba.
      destruct (IE b a Hb Ha Hba HP HC) as [[_ [Hs _]] _].
      apply (Hresp a b Ha Hb Hab Y HY).
      exact (Hs X Y HX HY H _ _ (Hfg b a Hb Ha Hba)).
    + intros X Y Z HX HY HZ HXc HYc HZc H f g h Hfg Hgh a b Ha Hb Hab.
      pose proof (per_refl_right _ _ _ HAp Hab) as Hbb.
      destruct (IE a b Ha Hb Hab HP HC) as [[_ [_ [Ht _]]] _].
      apply (Ht X Y Z HX HY HZ HXc HYc HZc H _ _ _ (Hfg a b Ha Hb Hab)).
      apply (Hresp a b Ha Hb Hab Y HY); apply Hgh; assumption.
    + intros X HX HXc; apply pi_rel_conv_on; intros a b Ha Hb Hab.
      destruct (IE a b Ha Hb Hab HP HC) as [[_ [_ [_ Hc]]] _]; apply Hc; assumption.
  - eapply d2_pi; [exact HD'|exact HD|exact HcA'|exact HcE'|exact HcA|exact HcE|exact HAs|].
    intros b a Hb Ha Hba.
    destruct (IE a b Ha Hb (proj1 HAp _ _ Hba) HP HC) as [_ [Hs _]].
    eapply d2_equiv; [exact Hs|apply Hresp; [exact Ha|exact Hb|apply (proj1 HAp), Hba]].
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | A2 E2 A2' E2' RA2 GE HE1 HE2 Hk1 Hk2 Hk3 Hk4 HA2 HGE HF | | ];
      try shape_contra.
    destruct (conv_ipi_inv _ _ _ _ (cv_trans (cv_sym HD) (cv_trans Hc HE1))) as [HAA HEE].
    pose proof (HAl _ _ _ HA2 HAA) as HRA.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply pi_rel_equiv; [exact HRA|]. intros a b Ha Hb Hab.
    destruct (IE a b Ha Hb Hab HP HC) as [_ [_ [Hl _]]].
    apply (Hl _ _ _ _ (HGE a b Ha Hb (proj1 (HRA a b) Hab)) HEq (conv_app_f _ _ a HEE)); exact HX.
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | A2 E2 A2' E2' RA2 GE HE1 HE2 Hk1 Hk2 Hk3 Hk4 HA2 HGE HF | | ];
      try shape_contra.
    destruct (conv_ipi_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc HE2))) as [HAA HEE].
    pose proof (HAr _ _ _ HA2 HAA) as HRA.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply pi_rel_equiv; [exact HRA|]. intros a b Ha Hb Hab.
    destruct (IE a b Ha Hb Hab HP HC) as [_ [_ [_ Hr]]].
    apply (Hr _ _ _ _ (HGE a b Ha Hb (proj1 (HRA a b) Hab)) HEq (conv_app_f _ _ b HEE)); exact HX.
Qed.

Lemma dclaim_sig : forall RI D D' A E A' E' RA FE,
  conv D (TISig A E) -> conv D' (TISig A' E') ->
  closed A -> closed E -> closed A' -> closed E' -> S2_claim A A' RA ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
  (forall a a', closed a -> closed a' -> RA a a' -> D2_claim RI (TApp E a) (TApp E' a') (FE a)) ->
  D2_claim RI D D' (fun X => sigma_rel RA (fun a _ => FE a X)).
Proof.
  intros RI D D' A E A' E' RA FE HD HD' HcA HcE HcA' HcE' [HAp [HAc [HAs [HAl HAr]]]] HE IE HP HC.
  pose proof (dclaim_family_resp RI RA E E' FE HP HC HAp HE IE) as Hresp.
  dclaim_split.
  - good_split.
    + intros X Y HX HY HXY; apply sigma_rel_mono; [intros t u H; exact H|intros a b Ha Hb Hab].
      destruct (IE a b Ha Hb Hab HP HC) as [[Hm _] _]; apply Hm; assumption.
    + intros X Y HX HY H p q [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]].
      pose proof (proj1 HAp _ _ HR) as HR'.
      exists a', b', a, b; repeat apply conj; try assumption.
      destruct (IE a a' Ha Ha' HR HP HC) as [[_ [Hs _]] _].
      apply (Hresp a a' Ha Ha' HR Y HY). exact (Hs X Y HX HY H _ _ HS).
    + intros X Y Z HX HY HZ HXc HYc HZc H p q r
        [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HR HS]]]]]]]]]]]
        [c [d [c' [d' [Hc [Hd [Hc' [Hd' [Hq' [Hr [HR' HS']]]]]]]]]]].
      destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hq) Hq')) as [Hac Hbd].
      assert (Hac' : RA a c) by (eapply HAc; [exact HR|apply cv_refl|exact Hac]).
      exists a, b, c', d'; repeat apply conj; try assumption.
      * eapply (proj2 HAp); eassumption.
      * destruct (IE a a' Ha Ha' HR HP HC) as [[_ [_ [Ht Hcv]]] _].
        assert (HS1 : FE a X b d) by (eapply Hcv; [exact HX|exact HXc|exact HS|apply cv_refl|exact Hbd]).
        assert (HS2 : FE a Y d d') by (apply (Hresp a c Ha Hc Hac' Y HY); exact HS').
        exact (Ht X Y Z HX HY HZ HXc HYc HZc H _ _ _ HS1 HS2).
    + intros X _ _; apply sigma_rel_conv.
  - eapply d2_sig; [exact HD'|exact HD|exact HcA'|exact HcE'|exact HcA|exact HcE|exact HAs|].
    intros b a Hb Ha Hba.
    destruct (IE a b Ha Hb (proj1 HAp _ _ Hba) HP HC) as [_ [Hs _]].
    eapply d2_equiv; [exact Hs|apply Hresp; [exact Ha|exact Hb|apply (proj1 HAp), Hba]].
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | A2 E2 A2' E2' RA2 GE HE1 HE2 Hk1 Hk2 Hk3 Hk4 HA2 HGE HF | ];
      try shape_contra.
    destruct (conv_isig_inv _ _ _ _ (cv_trans (cv_sym HD) (cv_trans Hc HE1))) as [HAA HEE].
    pose proof (HAl _ _ _ HA2 HAA) as HRA.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply sigma_rel_equiv; [exact HRA|]. intros a b Ha Hb Hab.
    destruct (IE a b Ha Hb Hab HP HC) as [_ [_ [Hl _]]].
    apply (Hl _ _ _ _ (HGE a b Ha Hb (proj1 (HRA a b) Hab)) HEq (conv_app_f _ _ a HEE)); exact HX.
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | A2 E2 A2' E2' RA2 GE HE1 HE2 Hk1 Hk2 Hk3 Hk4 HA2 HGE HF | ];
      try shape_contra.
    destruct (conv_isig_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc HE2))) as [HAA HEE].
    pose proof (HAr _ _ _ HA2 HAA) as HRA.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply sigma_rel_equiv; [exact HRA|]. intros a b Ha Hb Hab.
    destruct (IE a b Ha Hb Hab HP HC) as [_ [_ [_ Hr]]].
    apply (Hr _ _ _ _ (HGE a b Ha Hb (proj1 (HRA a b) Hab)) HEq (conv_app_f _ _ b HEE)); exact HX.
Qed.

Lemma dclaim_choice : forall RI D D' E C E' C' L FC,
  conv D (TIChoice E C) -> conv D' (TIChoice E' C') -> closed C -> closed C' ->
  conv E (code L) -> conv E' (code L) ->
  (forall n, n < List.length L ->
    D2_claim RI (TApp C (enum_position n)) (TApp C' (enum_position n)) (FC n)) ->
  D2_claim RI D D'
    (fun X => sigma_rel (enum_rel (List.length L)) (fun e _ => choice_rel (List.length L) FC X e)).
Proof.
  intros RI D D' E C E' C' L FC HD HD' HcC HcC' HE HE' IC HP HC.
  dclaim_split.
  - good_split.
    + intros X Y HX HY HXY; apply sigma_rel_mono; [intros t u H; exact H|].
      intros e e' He He' Hee t u [m [Hm [Hem HF]]]; exists m; repeat apply conj; try assumption.
      destruct (IC m Hm HP HC) as [[Hmono _] _]; exact (Hmono X Y HX HY HXY _ _ HF).
    + intros X Y HX HY H p q [e [b [e' [b' [He [Hb [He' [Hb' [Hp [Hq [HR HS]]]]]]]]]]].
      exists e', b', e, b; repeat apply conj; try assumption.
      * apply enum_rel_per, HR.
      * destruct HR as [m [Hm [Hem He'm]]]; destruct HS as [m2 [Hm2 [Hem2 HF]]].
        assert (m2 = m) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hem2|exact Hem]).
        subst m2. exists m; repeat apply conj; try assumption.
        destruct (IC m Hm HP HC) as [[_ [Hs _]] _]; exact (Hs X Y HX HY H _ _ HF).
    + intros X Y Z HX HY HZ HXc HYc HZc H p q r
        [e [b [e' [b' [He [Hb [He' [Hb' [Hp [Hq [HR HS]]]]]]]]]]]
        [f [d [f' [d' [Hf [Hd [Hf' [Hd' [Hq' [Hr [HR' HS']]]]]]]]]]].
      destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hq) Hq')) as [Hef Hbd].
      exists e, b, f', d'; repeat apply conj; try assumption.
      * eapply (proj2 (enum_rel_per _)); [exact HR|].
        eapply enum_rel_conv; [exact HR'|apply cv_sym; exact Hef|apply cv_refl].
      * destruct HR as [k [Hk [Hek He'k]]]; destruct HS as [m [Hm [Hem HF]]].
        destruct HS' as [m' [Hm' [Hfm' HF']]].
        assert (m = k) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hem|exact Hek]).
        assert (m' = k) by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hfm'|];
          eapply cv_trans; [apply cv_sym; exact Hef|exact He'k]).
        subst m m'. exists k; repeat apply conj; try assumption.
        destruct (IC k Hk HP HC) as [[_ [_ [Ht Hcv]]] _].
        assert (HF1 : FC k X b d) by (eapply Hcv; [exact HX|exact HXc|exact HF|apply cv_refl|exact Hbd]).
        exact (Ht X Y Z HX HY HZ HXc HYc HZc H _ _ _ HF1 HF').
    + intros X _ _; apply sigma_rel_conv.
  - eapply d2_choice; [exact HD'|exact HD|exact HcC'|exact HcC|exact HE'|exact HE|].
    intros m Hm; destruct (IC m Hm HP HC) as [_ [Hs _]]; exact Hs.
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | | E2 C2 E2' C2' L2 GC HE1 HE2 Hk1 Hk2 HL2 HL2' HGC HF];
      try shape_contra.
    destruct (conv_choice _ _ _ _ (cv_trans (cv_sym HD) (cv_trans Hc HE1))) as [HEE HCC].
    assert (L = L2) by (apply conv_code_inv; eapply cv_trans;
      [apply cv_sym; exact HE|eapply cv_trans; [exact HEE|exact HL2]]); subst L2.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply sigma_rel_equiv; [apply rel_equiv_refl|].
    intros e e' He He' Hee t u; split; intros [m [Hm [Hem HFm]]]; exists m; repeat apply conj; try assumption;
      destruct (IC m Hm HP HC) as [_ [_ [Hl _]]];
      pose proof (Hl _ _ _ _ (HGC m Hm) HEq (conv_app_f _ _ _ HCC) X HX) as Hq;
      apply Hq; exact HFm.
  - intros RI' E0 E0' G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | | E2 C2 E2' C2' L2 GC HE1 HE2 Hk1 Hk2 HL2 HL2' HGC HF];
      try shape_contra.
    destruct (conv_choice _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc HE2))) as [HEE HCC].
    assert (L = L2) by (apply conv_code_inv; eapply cv_trans;
      [apply cv_sym; exact HE'|eapply cv_trans; [exact HEE|exact HL2']]); subst L2.
    intros X HX. eapply rel_equiv_trans; [|apply rel_equiv_sym, (fequiv_rel _ _ _ _ HEq HF); exact HX].
    apply sigma_rel_equiv; [apply rel_equiv_refl|].
    intros e e' He He' Hee t u; split; intros [m [Hm [Hem HFm]]]; exists m; repeat apply conj; try assumption;
      destruct (IC m Hm HP HC) as [_ [_ [_ Hr]]];
      pose proof (Hr _ _ _ _ (HGC m Hm) HEq (conv_app_f _ _ _ HCC) X HX) as Hq;
      apply Hq; exact HFm.
Qed.

Lemma dclaim_equiv : forall RI D D' F G, D2_claim RI D D' F -> fequiv RI F G -> D2_claim RI D D' G.
Proof.
  intros RI D D' F G IF HFG HP HC.
  destruct (IF HP HC) as [[Fm [Fs [Ft Fc]]] [Fsym [Fl Fr]]].
  dclaim_split.
  - good_split.
    + intros X Y HX HY HXY t u H. apply (HFG Y HY). apply (Fm X Y HX HY HXY). apply (HFG X HX). exact H.
    + intros X Y HX HY H t u Ht. apply (HFG Y HY). apply (Fs X Y HX HY H). apply (HFG X HX). exact Ht.
    + intros X Y Z HX HY HZ HXc HYc HZc H t u v H1 H2. apply (HFG Z HZ).
      exact (Ft X Y Z HX HY HZ HXc HYc HZc H _ _ _ (proj2 (HFG X HX _ _) H1) (proj2 (HFG Y HY _ _) H2)).
    + intros X HX HXc. eapply conv_closed_equiv; [apply (HFG X HX)|apply Fc; assumption].
  - eapply d2_equiv; [exact Fsym|exact HFG].
  - intros RI' E E' G' HG HE Hc; eapply fequiv_trans; [apply fequiv_sym; exact HFG|eapply Fl; eassumption].
  - intros RI' E E' G' HG HE Hc; eapply fequiv_trans; [apply fequiv_sym; exact HFG|eapply Fr; eassumption].
Qed.

(* ------------------------------------------------------------------ *)
(* Fixed points of interpreted descriptions *)

Definition mu_ok (RI : rel) (F : ifunctor) :=
  per RI /\ conv_closed RI /\ iresp RI F /\
  (forall j, closed j -> RI j j -> good_functor RI (F j)).

Lemma mu_ok_per : forall RI F, mu_ok RI F -> forall i, per (mu_rel RI F i).
Proof.
  intros RI F [HP [HC [HR HG]]]; apply mu_per; try assumption;
    intros j Hj Hjj; apply (HG j Hj Hjj).
Qed.
Lemma mu_ok_conv : forall RI F, mu_ok RI F -> fam_conv (mu_rel RI F).
Proof.
  intros RI F [HP [HC [HR HG]]]; apply mu_conv; try assumption;
    intros j Hj Hjj; apply (HG j Hj Hjj).
Qed.
Lemma mu_ok_unfold : forall RI F, mu_ok RI F -> forall i t u, closed i -> RI i i ->
  (mu_rel RI F i t u <-> roll (F i (mu_rel RI F)) t u).
Proof.
  intros RI F [HP [HC [HR HG]]] i t u Hi Hii; split.
  - apply mu_unfold; try assumption; intros j Hj Hjj; apply (HG j Hj Hjj).
  - apply mu_fold; try assumption; intros j Hj Hjj; apply (HG j Hj Hjj).
Qed.

Lemma mu_family_ok : forall RI D D' F, per RI -> conv_closed RI ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp D j) (TApp D' j') (F j)) ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2_claim RI (TApp D j) (TApp D' j') (F j)) ->
  mu_ok RI F.
Proof.
  intros RI D D' F HP HC HD ID; refine (conj HP (conj HC (conj _ _))).
  - intros j j' Hj Hj' Hjj [H|H].
    + destruct (ID j j' Hj Hj' H HP HC) as [_ [_ [_ Hr]]].
      eapply Hr; [apply HD; [exact Hj'|exact Hj'|eapply per_refl_right; eassumption]
        |apply rel_equiv_refl|apply cv_refl].
    + destruct (ID j j Hj Hj Hjj HP HC) as [_ [_ [Hl _]]].
      assert (Hj'j' : RI j' j') by (eapply HC; [exact Hjj|exact H|exact H]).
      eapply Hl; [apply HD; [exact Hj'|exact Hj'|exact Hj'j']|apply rel_equiv_refl|apply conv_app_a; exact H].
  - intros j Hj Hjj; exact (proj1 (ID j j Hj Hj Hjj HP HC)).
Qed.

(* A good functor applied to a good family is a conversion-closed PER. *)
Lemma functor_per : forall RI F X, good_functor RI F -> fam_resp RI X -> fam_conv X ->
  (forall i, per (X i)) -> per (F X) /\ conv_closed (F X).
Proof.
  intros RI F X [Fm [Fs [Ft Fc]]] HX HXc HXp; split; [split|].
  - intros t u H; eapply Fs; [exact HX|exact HX| |exact H]. intros i a b; apply (HXp i).
  - intros t u v H1 H2; eapply Ft; [exact HX|exact HX|exact HX|exact HXc|exact HXc|exact HXc| |exact H1|exact H2].
    intros i a b c; apply (HXp i).
  - apply Fc; assumption.
Qed.

Lemma claim_mu : forall A B IT D i IT' D' i' RI F,
  conv A (MuAt IT D i) -> conv B (MuAt IT' D' i') ->
  S2_claim IT IT' RI -> closed i -> closed i' -> RI i i' ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp D j) (TApp D' j') (F j)) ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2_claim RI (TApp D j) (TApp D' j') (F j)) ->
  S2_claim A B (mu_rel RI F i).
Proof.
  intros A B IT D i IT' D' i' RI F HA HB [HIp [HIc [HIs [HIl HIr]]]] Hi Hi' Hii HD ID.
  pose proof (mu_family_ok RI D D' F HIp HIc HD ID) as Hok.
  pose proof Hok as [_ [_ [Hresp _]]].
  claim_split.
  - apply mu_ok_per; exact Hok.
  - apply mu_ok_conv; [exact Hok|exact Hi].
  - eapply s2_equiv; [eapply s2_mu with (F := F);
      [exact HB|exact HA|exact HIs|exact Hi'|exact Hi|apply (proj1 HIp), Hii|]|].
    + intros j' j Hj' Hj Hjj'.
      destruct (ID j j' Hj Hj' (proj1 HIp _ _ Hjj') HIp HIc) as [_ [Hs _]].
      eapply d2_equiv; [exact Hs|].
      apply Hresp; [exact Hj|exact Hj'|eapply per_refl_right; [exact HIp|exact Hjj']|].
      left; apply (proj1 HIp), Hjj'.
    + apply mu_resp; [exact Hi'|exact Hi|left; apply (proj1 HIp), Hii].
  - intros A' B' S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | IT2 Dm2 i2 IT2' Dm2' i2' RI2 F2 Ha2 Hb2 HI2 Hci2 Hci2' Hii2 HD2 HR2 | ];
      try shape_contra.
    destruct (conv_muat_inv _ _ _ _ _ _ (cv_trans (cv_sym HA) (cv_trans Hc Ha2))) as [HIT [HDD Hii']].
    pose proof (HIl _ _ _ HI2 HIT) as HRI.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR2].
    eapply rel_equiv_trans; [apply (mu_equiv RI RI2 F F2 HRI)|].
    + intros j Hj Hjj.
      destruct (ID j j Hj Hj Hjj HIp HIc) as [_ [_ [Hl _]]].
      eapply Hl; [apply HD2; [exact Hj|exact Hj|apply HRI, Hjj]|exact HRI|apply conv_app_f; exact HDD].
    + apply mu_resp; [exact Hi|exact Hci2|right; exact Hii'].
  - intros A' B' S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | IT2 Dm2 i2 IT2' Dm2' i2' RI2 F2 Ha2 Hb2 HI2 Hci2 Hci2' Hii2 HD2 HR2 | ];
      try shape_contra.
    destruct (conv_muat_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2))) as [HIT [HDD Hii']].
    pose proof (HIr _ _ _ HI2 HIT) as HRI.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR2].
    eapply rel_equiv_trans; [apply (mu_equiv RI RI2 F F2 HRI)|].
    + intros j Hj Hjj.
      destruct (ID j j Hj Hj Hjj HIp HIc) as [_ [_ [_ Hr]]].
      eapply Hr; [apply HD2; [exact Hj|exact Hj|apply HRI, Hjj]|exact HRI|apply conv_app_f; exact HDD].
    + apply mu_resp; [exact Hi|exact Hci2|left].
      apply HRI. eapply (proj2 HIp); [exact Hii|].
      apply (proj1 HIp). eapply HIc; [apply HRI, Hii2|apply cv_refl|apply cv_sym; exact Hii'].
Qed.

Lemma claim_close : forall A B IT Fd G i IT' Fd' G' i' RI FF FG,
  conv A (CloseAt IT Fd G i) -> conv B (CloseAt IT' Fd' G' i') ->
  S2_claim IT IT' RI -> closed i -> closed i' -> RI i i' ->
  D2_claim RI (TApp Fd i) (TApp Fd' i') FF ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp G j) (TApp G' j') (FG j)) ->
  (forall j j', closed j -> closed j' -> RI j j' -> D2_claim RI (TApp G j) (TApp G' j') (FG j)) ->
  S2_claim A B (roll (FF (mu_rel RI FG))).
Proof.
  intros A B IT Fd G i IT' Fd' G' i' RI FF FG HA HB [HIp [HIc [HIs [HIl HIr]]]] Hi Hi' Hii IF HG IG.
  pose proof (mu_family_ok RI G G' FG HIp HIc HG IG) as Hok.
  destruct (IF HIp HIc) as [HFgood [HFs [HFl HFr]]].
  assert (Hmu : per (FF (mu_rel RI FG)) /\ conv_closed (FF (mu_rel RI FG))).
  { apply (functor_per RI); [exact HFgood|apply mu_resp|apply mu_ok_conv, Hok|apply mu_ok_per, Hok]. }
  pose proof Hok as [_ [_ [Hresp _]]].
  claim_split.
  - apply roll_per; apply Hmu.
  - apply roll_conv.
  - eapply s2_close; [exact HB|exact HA|exact HIs|exact Hi'|exact Hi|apply (proj1 HIp), Hii|exact HFs|].
    intros j' j Hj' Hj Hjj'.
    destruct (IG j j' Hj Hj' (proj1 HIp _ _ Hjj') HIp HIc) as [_ [Hs _]].
    eapply d2_equiv; [exact Hs|].
    apply Hresp; [exact Hj|exact Hj'|eapply per_refl_right; [exact HIp|exact Hjj']|].
    left; apply (proj1 HIp), Hjj'.
  - intros A' B' S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | | IT2 Fd2 G2 i2 IT2' Fd2' G2' i2' RI2 FF2 FG2 Ha2 Hb2 HI2 Hci2 Hci2' Hii2 HF2 HG2 HR2];
      try shape_contra.
    destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym HA) (cv_trans Hc Ha2)))
      as [HIT [HFF [HGG Hii']]].
    pose proof (HIl _ _ _ HI2 HIT) as HRI.
    assert (HM : forall k, rel_equiv (mu_rel RI FG k) (mu_rel RI2 FG2 k)).
    { apply mu_equiv; [exact HRI|]. intros j Hj Hjj.
      destruct (IG j j Hj Hj Hjj HIp HIc) as [_ [_ [Hl _]]].
      eapply Hl; [apply HG2; [exact Hj|exact Hj|apply HRI, Hjj]|exact HRI|apply conv_app_f; exact HGG]. }
    pose proof (HFl _ _ _ _ HF2 HRI (conv_app _ _ _ _ HFF Hii')) as HFE.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR2].
    apply roll_equiv.
    eapply rel_equiv_trans; [apply (fmono_equiv RI FF (mu_rel RI FG) (mu_rel RI2 FG2))|].
    + apply HFgood.
    + apply mu_resp.
    + eapply fam_resp_equiv; [apply rel_equiv_sym; exact HRI|apply mu_resp].
    + exact HM.
    + apply HFE. eapply fam_resp_equiv; [apply rel_equiv_sym; exact HRI|apply mu_resp].
  - intros A' B' S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | | IT2 Fd2 G2 i2 IT2' Fd2' G2' i2' RI2 FF2 FG2 Ha2 Hb2 HI2 Hci2 Hci2' Hii2 HF2 HG2 HR2];
      try shape_contra.
    destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2)))
      as [HIT [HFF [HGG Hii']]].
    pose proof (HIr _ _ _ HI2 HIT) as HRI.
    assert (HM : forall k, rel_equiv (mu_rel RI FG k) (mu_rel RI2 FG2 k)).
    { apply mu_equiv; [exact HRI|]. intros j Hj Hjj.
      destruct (IG j j Hj Hj Hjj HIp HIc) as [_ [_ [_ Hr]]].
      eapply Hr; [apply HG2; [exact Hj|exact Hj|apply HRI, Hjj]|exact HRI|apply conv_app_f; exact HGG]. }
    pose proof (HFr _ _ _ _ HF2 HRI (conv_app _ _ _ _ HFF Hii')) as HFE.
    eapply rel_equiv_trans; [|apply rel_equiv_sym; exact HR2].
    apply roll_equiv.
    eapply rel_equiv_trans; [apply (fmono_equiv RI FF (mu_rel RI FG) (mu_rel RI2 FG2))|].
    + apply HFgood.
    + apply mu_resp.
    + eapply fam_resp_equiv; [apply rel_equiv_sym; exact HRI|apply mu_resp].
    + exact HM.
    + apply HFE. eapply fam_resp_equiv; [apply rel_equiv_sym; exact HRI|apply mu_resp].
Qed.

Lemma claim_equiv : forall A B R S, S2_claim A B R -> rel_equiv R S -> S2_claim A B S.
Proof.
  intros A B R S [Hp [Hc [Hs [Hl Hr]]]] HE; claim_split.
  - eapply per_equiv; eassumption.
  - eapply conv_closed_equiv; eassumption.
  - eapply s2_equiv; eassumption.
  - intros; eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eapply Hl; eassumption].
  - intros; eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eapply Hr; eassumption].
Qed.

Theorem S2_D2_claims :
  (forall A B R, S2 A B R -> S2_claim A B R) /\
  (forall RI D D' F, D2 RI D D' F -> D2_claim RI D D' F).
Proof.
  apply S2_D2_mind; intros.
  - apply claim_unit; assumption.
  - apply claim_uid; assumption.
  - apply claim_enumu; assumption.
  - eapply claim_enum; eassumption.
  - eapply claim_pi; eassumption.
  - eapply claim_sigma; eassumption.
  - eapply claim_mu; eassumption.
  - eapply claim_close; eassumption.
  - eapply claim_equiv; eassumption.
  - eapply dclaim_var; eassumption.
  - apply dclaim_one; assumption.
  - apply dclaim_bot; assumption.
  - eapply dclaim_prod; eassumption.
  - eapply dclaim_pi; eassumption.
  - eapply dclaim_sig; eassumption.
  - eapply dclaim_choice; eassumption.
  - eapply dclaim_equiv; eassumption.
Qed.

Corollary S2_per : forall A B R, S2 A B R -> per R.
Proof. intros A B R H; exact (proj1 (proj1 S2_D2_claims A B R H)). Qed.
Corollary S2_conv_closed : forall A B R, S2 A B R -> conv_closed R.
Proof. intros A B R H; exact (proj1 (proj2 (proj1 S2_D2_claims A B R H))). Qed.
Corollary S2_sym : forall A B R, S2 A B R -> S2 B A R.
Proof. intros A B R H; exact (proj1 (proj2 (proj2 (proj1 S2_D2_claims A B R H)))). Qed.
Corollary S2_unique_left : forall A B R A' B' S, S2 A B R -> S2 A' B' S -> conv A A' -> rel_equiv R S.
Proof. intros A B R A' B' S H; exact (proj1 (proj2 (proj2 (proj2 (proj1 S2_D2_claims A B R H)))) A' B' S). Qed.
Corollary S2_unique_right : forall A B R A' B' S, S2 A B R -> S2 A' B' S -> conv B B' -> rel_equiv R S.
Proof. intros A B R A' B' S H; exact (proj2 (proj2 (proj2 (proj2 (proj1 S2_D2_claims A B R H)))) A' B' S). Qed.
Corollary D2_good : forall RI D D' F, D2 RI D D' F -> per RI -> conv_closed RI -> good_functor RI F.
Proof. intros RI D D' F H HP HC; exact (proj1 (proj2 S2_D2_claims RI D D' F H HP HC)). Qed.
Corollary D2_sym : forall RI D D' F, D2 RI D D' F -> per RI -> conv_closed RI -> D2 RI D' D F.
Proof. intros RI D D' F H HP HC; exact (proj1 (proj2 (proj2 S2_D2_claims RI D D' F H HP HC))). Qed.
Corollary D2_unique_left : forall RI D D' F RI' E E' G, D2 RI D D' F -> per RI -> conv_closed RI ->
  D2 RI' E E' G -> rel_equiv RI RI' -> conv D E -> fequiv RI F G.
Proof. intros RI D D' F RI' E E' G H HP HC; exact (proj1 (proj2 (proj2 (proj2 S2_D2_claims RI D D' F H HP HC))) RI' E E' G). Qed.
Corollary D2_unique_right : forall RI D D' F RI' E E' G, D2 RI D D' F -> per RI -> conv_closed RI ->
  D2 RI' E E' G -> rel_equiv RI RI' -> conv D' E' -> fequiv RI F G.
Proof. intros RI D D' F RI' E E' G H HP HC; exact (proj2 (proj2 (proj2 (proj2 S2_D2_claims RI D D' F H HP HC))) RI' E E' G). Qed.

(* ------------------------------------------------------------------ *)
(* Transitivity *)

Definition S2_tclaim A B R := forall B' C S, S2 B' C S -> conv B B' -> S2 A C R.
Definition D2_tclaim RI D D' F := per RI -> conv_closed RI ->
  forall RI' D'' E G, D2 RI' D'' E G -> rel_equiv RI RI' -> conv D' D'' -> D2 RI D E F.

Theorem S2_D2_trans_claims :
  (forall A B R, S2 A B R -> S2_tclaim A B R) /\
  (forall RI D D' F, D2 RI D D' F -> D2_tclaim RI D D' F).
Proof.
  apply S2_D2_mind; unfold S2_tclaim, D2_tclaim.
  - intros A B HA HB B' C S HS Hc.
    destruct (S2_view _ _ _ HS); try shape_contra. apply s2_unit; assumption.
  - intros A B HA HB B' C S HS Hc.
    destruct (S2_view _ _ _ HS); try shape_contra. apply s2_uid; assumption.
  - intros A B HA HB B' C S HS Hc.
    destruct (S2_view _ _ _ HS); try shape_contra. apply s2_enumu; assumption.
  - intros A B E E' L HA HB HE HE' B' C S HS Hc.
    destruct (S2_view _ _ _ HS) as [ | | | E2 E3 L2 Hb2 Hc3 HE2 HE3 HR2 | | | | ]; try shape_contra.
    assert (L = L2) by (apply conv_code_inv; eapply cv_trans; [apply cv_sym; exact HE'|];
      eapply cv_trans; [|exact HE2]; apply conv_enum; eapply cv_trans;
      [apply cv_sym; exact HB|eapply cv_trans; [exact Hc|exact Hb2]]).
    subst L2. eapply s2_enum; [exact HA|exact Hc3|exact HE|exact HE3].
  - intros A B x U V y U' V' RU RV HA HB HU IHU HV IHV B' C S HS Hc.
    destruct (S2_view _ _ _ HS) as [ | | | | x2 U2 V2 z U3 V3 RU2 RV2 Hb2 Hc3 HU2 HV2 HR2 | | | ];
      try shape_contra.
    destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2))) as [HUU HVV].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HU) HU2 HUU) as HRU.
    pose proof (S2_per _ _ _ HU) as HP.
    eapply s2_pi; [exact HA|exact Hc3|eapply IHU; [exact HU2|exact HUU]|].
    intros a c Ha Hc' Hac.
    eapply IHV; [exact Ha|exact Hc'|exact Hac|apply HV2; [exact Hc'|exact Hc'|]|apply HVV; exact Hc'].
    apply HRU; eapply per_refl_right; eassumption.
  - intros A B x U V y U' V' RU RV HA HB HU IHU HV IHV B' C S HS Hc.
    destruct (S2_view _ _ _ HS) as [ | | | | | x2 U2 V2 z U3 V3 RU2 RV2 Hb2 Hc3 HU2 HV2 HR2 | | ];
      try shape_contra.
    destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2))) as [HUU HVV].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HU) HU2 HUU) as HRU.
    pose proof (S2_per _ _ _ HU) as HP.
    eapply s2_sigma; [exact HA|exact Hc3|eapply IHU; [exact HU2|exact HUU]|].
    intros a c Ha Hc' Hac.
    eapply IHV; [exact Ha|exact Hc'|exact Hac|apply HV2; [exact Hc'|exact Hc'|]|apply HVV; exact Hc'].
    apply HRU; eapply per_refl_right; eassumption.
  - intros A B IT D i IT' D' i' RI F HA HB HI IHI Hi Hi' Hii HD IHD B' C S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | IT2 Dm2 i2 IT3 Dm3 i3 RI2 F2 Hb2 Hc3 HI2 Hci2 Hci3 Hii2 HD2 HR2 | ];
      try shape_contra.
    destruct (conv_muat_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2))) as [HIT [HDD Hii']].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HI) HI2 HIT) as HRI.
    pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
    assert (Hi'3 : RI i' i3) by (eapply HC; [apply HRI, Hii2|apply cv_sym; exact Hii'|apply cv_refl]).
    eapply s2_mu; [exact HA|exact Hc3|eapply IHI; [exact HI2|exact HIT]|exact Hi|exact Hci3
      |eapply (proj2 HP); eassumption|].
    intros j k Hj Hk Hjk.
    eapply IHD; [exact Hj|exact Hk|exact Hjk|exact HP|exact HC| |exact HRI|apply conv_app_f; exact HDD].
    apply HD2; [exact Hk|exact Hk|apply HRI; eapply per_refl_right; eassumption].
  - intros A B IT Fd G i IT' Fd' G' i' RI FF FG HA HB HI IHI Hi Hi' Hii HF IHF HG IHG B' C S HS Hc.
    destruct (S2_view _ _ _ HS) as
      [ | | | | | | | IT2 Fd2 G2 i2 IT3 Fd3 G3 i3 RI2 FF2 FG2 Hb2 Hc3 HI2 Hci2 Hci3 Hii2 HF2 HG2 HR2];
      try shape_contra.
    destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym HB) (cv_trans Hc Hb2)))
      as [HIT [HFF [HGG Hii']]].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HI) HI2 HIT) as HRI.
    pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
    assert (Hi'3 : RI i' i3) by (eapply HC; [apply HRI, Hii2|apply cv_sym; exact Hii'|apply cv_refl]).
    eapply s2_close; [exact HA|exact Hc3|eapply IHI; [exact HI2|exact HIT]|exact Hi|exact Hci3
      |eapply (proj2 HP); eassumption| |].
    + eapply IHF; [exact HP|exact HC|exact HF2|exact HRI|apply conv_app; [exact HFF|exact Hii']].
    + intros j k Hj Hk Hjk.
      eapply IHG; [exact Hj|exact Hk|exact Hjk|exact HP|exact HC| |exact HRI|apply conv_app_f; exact HGG].
      apply HG2; [exact Hk|exact Hk|apply HRI; eapply per_refl_right; eassumption].
  - intros A B R S HR IHR HE B' C S' HS Hc. eapply s2_equiv; [eapply IHR; eassumption|exact HE].
  - intros RI D D' i i' HD HD' Hi Hi' Hii HP HC RI' D'' E G HG HE Hc.
    destruct (D2_view _ _ _ _ HG) as [i2 i3 Hd2 He3 Hci2 Hci3 Hii2 HF2| | | | | | ]; try shape_contra.
    assert (Hii' : conv i' i2) by (apply conv_ivar_inv; eapply cv_trans;
      [apply cv_sym; exact HD'|eapply cv_trans; [exact Hc|exact Hd2]]).
    eapply d2_var; [exact HD|exact He3|exact Hi|exact Hci3|].
    eapply (proj2 HP); [exact Hii|]. eapply HC; [apply HE, Hii2|apply cv_sym; exact Hii'|apply cv_refl].
  - intros RI D D' HD HD' HP HC RI' D'' E G HG HE Hc.
    destruct (D2_view _ _ _ _ HG); try shape_contra. apply d2_one; assumption.
  - intros RI D D' HD HD' HP HC RI' D'' E G HG HE Hc.
    destruct (D2_view _ _ _ _ HG); try shape_contra. apply d2_bot; assumption.
  - intros RI D D' A B A' B' FA FB HD HD' Hk1 Hk2 Hk3 Hk4 HA IHA HB IHB HP HC RI' D'' E G HG HE Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | A2 B2 A3 B3 GA GB Hd2 He3 Hl1 Hl2 Hl3 Hl4 HGA HGB HF2 | | | ];
      try shape_contra.
    destruct (conv_iprod_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc Hd2))) as [HAA HBB].
    eapply d2_prod; [exact HD|exact He3|exact Hk1|exact Hk2|exact Hl3|exact Hl4
      |eapply IHA; eassumption|eapply IHB; eassumption].
  - intros RI D D' A Ef A' Ef' RA FE HD HD' Hk1 Hk2 Hk3 Hk4 HA IHA HE IHE HP HC RI' D'' E G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | A2 E2 A3 E3 RA2 GE Hd2 He3 Hl1 Hl2 Hl3 Hl4 HA2 HGE HF2 | | ];
      try shape_contra.
    destruct (conv_ipi_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc Hd2))) as [HAA HEE].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HA) HA2 HAA) as HRA.
    pose proof (S2_per _ _ _ HA) as HPA.
    eapply d2_pi; [exact HD|exact He3|exact Hk1|exact Hk2|exact Hl3|exact Hl4|eapply IHA; [exact HA2|exact HAA]|].
    intros a c Ha Hc' Hac.
    eapply IHE; [exact Ha|exact Hc'|exact Hac|exact HP|exact HC| |exact HEq|apply conv_app_f; exact HEE].
    apply HGE; [exact Hc'|exact Hc'|apply HRA; eapply per_refl_right; eassumption].
  - intros RI D D' A Ef A' Ef' RA FE HD HD' Hk1 Hk2 Hk3 Hk4 HA IHA HE IHE HP HC RI' D'' E G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | A2 E2 A3 E3 RA2 GE Hd2 He3 Hl1 Hl2 Hl3 Hl4 HA2 HGE HF2 | ];
      try shape_contra.
    destruct (conv_isig_inv _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc Hd2))) as [HAA HEE].
    pose proof (S2_unique_left _ _ _ _ _ _ (S2_sym _ _ _ HA) HA2 HAA) as HRA.
    pose proof (S2_per _ _ _ HA) as HPA.
    eapply d2_sig; [exact HD|exact He3|exact Hk1|exact Hk2|exact Hl3|exact Hl4|eapply IHA; [exact HA2|exact HAA]|].
    intros a c Ha Hc' Hac.
    eapply IHE; [exact Ha|exact Hc'|exact Hac|exact HP|exact HC| |exact HEq|apply conv_app_f; exact HEE].
    apply HGE; [exact Hc'|exact Hc'|apply HRA; eapply per_refl_right; eassumption].
  - intros RI D D' E C E' C' L FC HD HD' Hk1 Hk2 HE HE' HCs IHC HP HC RI' D'' E0 G HG HEq Hc.
    destruct (D2_view _ _ _ _ HG) as [ | | | | | | E2 C2 E3 C3 L2 GC Hd2 He3 Hl1 Hl2 HL2 HL3 HGC HF2];
      try shape_contra.
    destruct (conv_choice _ _ _ _ (cv_trans (cv_sym HD') (cv_trans Hc Hd2))) as [HEE HCC].
    assert (L = L2) by (apply conv_code_inv; eapply cv_trans;
      [apply cv_sym; exact HE'|eapply cv_trans; [exact HEE|exact HL2]]); subst L2.
    eapply d2_choice; [exact HD|exact He3|exact Hk1|exact Hl2|exact HE|exact HL3|].
    intros m Hm. eapply IHC; [exact Hm|exact HP|exact HC|apply HGC, Hm|exact HEq|apply conv_app_f; exact HCC].
  - intros RI D D' F G HF IHF HFG HP HC RI' D'' E G' HG HE Hc.
    eapply d2_equiv; [eapply IHF; eassumption|exact HFG].
Qed.

Corollary S2_trans : forall A B R B' C S, S2 A B R -> S2 B' C S -> conv B B' -> S2 A C R.
Proof. intros A B R B' C S H; exact (proj1 S2_D2_trans_claims A B R H B' C S). Qed.
Corollary S2_refl_left : forall A B R, S2 A B R -> S2 A A R.
Proof. intros A B R H; eapply S2_trans; [exact H|apply S2_sym, H|apply cv_refl]. Qed.
Corollary S2_refl_right : forall A B R, S2 A B R -> S2 B B R.
Proof. intros A B R H; eapply S2_trans; [apply S2_sym, H|exact H|apply cv_refl]. Qed.
Corollary D2_trans : forall RI D D' F RI' D'' E G, D2 RI D D' F -> per RI -> conv_closed RI ->
  D2 RI' D'' E G -> rel_equiv RI RI' -> conv D' D'' -> D2 RI D E F.
Proof. intros RI D D' F RI' D'' E G H HP HC; exact (proj2 S2_D2_trans_claims RI D D' F H HP HC RI' D'' E G). Qed.
