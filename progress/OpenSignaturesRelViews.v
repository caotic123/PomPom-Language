(* Inversion views of the binary model at enum types, enum-tagged sums and
   close types. Used by the semantic coercion graphs. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelAdequacy.
Import ListNotations.

Definition tyw (A : term) := exists k R, interp k A A R.

Lemma interp_enum_view : forall k A B R E L, interp k A B R -> conv A (TEnumT E) ->
  conv E (code L) ->
  exists E', conv B (TEnumT E') /\ conv E' (code L) /\ rel_equiv R (enum_rel (List.length L)).
Proof.
  intros k A B R E L H HA HE.
  destruct (T2_view _ _ _ _ H) as [R' Hat HR|? ? ? ? ? ? ? ? Ha|? ? ? ? ? ? ? ? Ha]; [|head_contra2|head_contra2].
  destruct Hat as [A0 B0 R0 HS _ _|A0 B0 j R0 _ Ha _|A0 B0 IT IT' RI _ _ Ha _]; [|head_contra2|head_contra2].
  destruct (S2_view _ _ _ HS) as
    [Ha _ _|Ha _ _|Ha _ _|E1 E1' L1 Ha Hb HE1 HE1' HR1|? ? ? ? ? ? ? ? Ha|? ? ? ? ? ? ? ? Ha
    |? ? ? ? ? ? ? ? Ha|? ? ? ? ? ? ? ? ? ? ? Ha]; try head_contra2.
  pose proof (conv_enum _ _ (cv_trans (cv_sym HA) Ha)) as HEE.
  assert (HL : L1 = L) by (apply conv_code_inv; eapply cv_trans; [apply cv_sym, HE1|eapply cv_trans; [apply cv_sym, HEE|exact HE]]).
  subst L1. exists E1'; repeat apply conj; [exact Hb|exact HE1'|].
  eapply rel_equiv_trans; eassumption.
Qed.

Lemma subst_arg_conv : forall a a' x B, conv a a' -> conv (subst a x B) (subst a' x B).
Proof. intros; apply substitution_argument_conversion; assumption. Qed.

(* A related pair of enum-tagged sums. *)
Lemma sum_view : forall k A B R x E P y E' P' L, interp k A B R ->
  conv A (TSigma x (TEnumT E) P) -> conv E (code L) -> conv B (TSigma y (TEnumT E') P') ->
  conv E' (code L) /\
  (forall m, m < List.length L ->
     exists S, interp k (subst (enum_position m) x P) (subst (enum_position m) y P') S) /\
  (forall p q, R p q <-> exists m xs ys, m < List.length L /\ closed xs /\ closed ys /\
     conv p (TPair (enum_position m) xs) /\ conv q (TPair (enum_position m) ys) /\
     rel_at xs ys (subst (enum_position m) x P) (subst (enum_position m) y P')).
Proof.
  intros k A B R x E P y E' P' L H HA HE HB.
  destruct (interp_sigma_view _ _ _ _ _ _ _ H HA) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA0 & HB0 & HU & HV & HR).
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HA) HA0)) as [HU1 HV1].
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) HB0)) as [HU2 HV2].
  assert (HUe : interp k (TEnumT E) (TEnumT E') RU) by (eapply interp_conv; [exact HU|apply cv_sym, HU1|apply cv_sym, HU2]).
  destruct (interp_enum_view _ _ _ _ _ _ HUe (cv_refl _) HE) as [E'' [HE1 [HE2 HRU]]].
  assert (HE' : conv E' (code L)) by (eapply cv_trans; [apply conv_enum, HE1|exact HE2]).
  assert (HRUp : forall m, m < List.length L -> RU (enum_position m) (enum_position m)).
  { intros m Hm; apply HRU; exists m; repeat apply conj; [exact Hm|apply cv_refl|apply cv_refl]. }
  refine (conj HE' (conj _ _)).
  - intros m Hm. exists (RV (enum_position m) (enum_position m)).
    eapply interp_conv; [apply HV; [apply closed_position|apply closed_position|apply HRUp, Hm]| |];
      apply cv_sym; [apply HV1|apply HV2]; apply closed_position.
  - intros p q; split.
    + intros Hpq; destruct (proj1 (HR p q) Hpq) as (a & b & a' & b' & Ha & Hb & Ha' & Hb' & Hp & Hq & Hab & Hbb).
      destruct (proj1 (HRU a a') Hab) as [m [Hm [Hma Hma']]].
      exists m, b, b'; repeat apply conj; try assumption.
      * eapply cv_trans; [exact Hp|apply conv_pair; [exact Hma|apply cv_refl]].
      * eapply cv_trans; [exact Hq|apply conv_pair; [exact Hma'|apply cv_refl]].
      * exists k, (RV a a'); split; [|exact Hbb].
        eapply interp_conv; [apply HV; assumption| |].
        -- eapply cv_trans; [apply cv_sym, HV1, Ha|apply subst_arg_conv, Hma].
        -- eapply cv_trans; [apply cv_sym, HV2, Ha'|apply subst_arg_conv, Hma'].
    + intros (m & xs & ys & Hm & Hxs & Hys & Hp & Hq & Hr).
      apply HR. exists (enum_position m), xs, (enum_position m), ys.
      repeat apply conj; try assumption; try apply closed_position; [apply HRUp, Hm|].
      eapply rel_at_transfer; [exact Hr|apply HV; [apply closed_position|apply closed_position|apply HRUp, Hm]|].
      apply HV1, closed_position.
Qed.

Lemma interp_close_view : forall k A B R IT F G i, interp k A B R -> conv A (CloseAt IT F G i) ->
  exists IT0 F0 G0 i0 IT0' F0' G0' i0' RI FF FG,
    conv A (CloseAt IT0 F0 G0 i0) /\ conv B (CloseAt IT0' F0' G0' i0') /\
    S2 IT0 IT0' RI /\ closed i0 /\ closed i0' /\ RI i0 i0' /\
    D2 RI (TApp F0 i0) (TApp F0' i0') FF /\
    (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp G0 j) (TApp G0' j') (FG j)) /\
    rel_equiv R (roll (FF (mu_rel RI FG))).
Proof.
  intros k A B R IT F G i H HA.
  destruct (T2_view _ _ _ _ H) as [R' Hat HR|? ? ? ? ? ? ? ? Ha|? ? ? ? ? ? ? ? Ha]; [|head_contra2|head_contra2].
  destruct Hat as [A0 B0 R0 HS _ _|A0 B0 j R0 _ Ha _|A0 B0 IT1 IT1' RI _ _ Ha _]; [|head_contra2|head_contra2].
  destruct (S2_view _ _ _ HS) as
    [Ha _ _|Ha _ _|Ha _ _|E1 E1' L1 Ha _ _ _ _|? ? ? ? ? ? ? ? Ha|? ? ? ? ? ? ? ? Ha
    |? ? ? ? ? ? ? ? Ha|IT0 F0 G0 i0 IT0' F0' G0' i0' RI FF FG Ha Hb HI Hi Hi' Hii HF HG HR1]; try head_contra2.
  exists IT0, F0, G0, i0, IT0', F0', G0', i0', RI, FF, FG; repeat apply conj; try assumption.
  eapply rel_equiv_trans; eassumption.
Qed.

(* The payload of related close types is related, and the close relation
   is its roll. *)
Lemma close_payload_interp : forall k A B R IT F G i IT' F' G' i', interp k A B R ->
  conv A (CloseAt IT F G i) -> conv B (CloseAt IT' F' G' i') ->
  exists P, interp 0 (payload IT F G i) (payload IT' F' G' i') P /\ rel_equiv R (roll P).
Proof.
  intros k A B R IT F G i IT' F' G' i' H HA HB.
  destruct (interp_close_view _ _ _ _ _ _ _ _ H HA) as
    (IT0 & F0 & G0 & i0 & IT0' & F0' & G0' & i0' & RI & FF & FG & HA0 & HB0 & HI & Hi & Hi' & Hii & HF & HG & HR).
  destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym HA) HA0)) as (HIT1 & HF1 & HG1 & Hi1).
  destruct (conv_closeat_inv _ _ _ _ _ _ _ _ (cv_trans (cv_sym HB) HB0)) as (HIT2 & HF2 & HG2 & Hi2).
  pose proof (S2_per _ _ _ HI) as HP; pose proof (S2_conv_closed _ _ _ HI) as HC.
  pose proof (mu_family_ok RI G0 G0' FG HP HC HG
    (fun j j' H1 H2 H3 => proj2 S2_D2_claims _ _ _ _ (HG j j' H1 H2 H3))) as Hok.
  pose proof Hok as [_ [_ [Hresp Hgood]]].
  exists (FF (mu_rel RI FG)); split; [|exact HR].
  unfold payload. eapply interp_TInterp.
  - eapply D2_conv; [exact HF|apply conv_app; apply cv_sym; assumption|apply conv_app; apply cv_sym; assumption].
  - exact HP.
  - exact HC.
  - apply mu_resp; try assumption; intros j Hj Hjj; exact (proj1 (Hgood j Hj Hjj)).
  - intros j1 j2 Hj1 Hj2 Hj. change (TApp (carrier IT G) j1) with (CloseAt IT G G j1).
    change (TApp (carrier IT' G') j2) with (CloseAt IT' G' G' j2).
    assert (Hj11 : RI j1 j1) by (eapply per_refl_left; eassumption).
    eapply interp_equiv; [apply S2_interp; eapply s2_close|].
    + apply cv_refl.
    + apply cv_refl.
    + eapply S2_conv; [exact HI|apply cv_sym, HIT1|apply cv_sym, HIT2].
    + exact Hj1.
    + exact Hj2.
    + exact Hj.
    + eapply D2_conv; [exact (HG j1 j2 Hj1 Hj2 Hj)|apply conv_app_f, cv_sym, HG1|apply conv_app_f, cv_sym, HG2].
    + intros j j' H1 H2 H3; eapply D2_conv; [exact (HG j j' H1 H2 H3)|apply conv_app_f, cv_sym, HG1|apply conv_app_f, cv_sym, HG2].
    + intros t u; symmetry; apply (mu_ok_unfold _ _ Hok j1 t u Hj1 Hj11).
Qed.

(* ------------------------------------------------------------------ *)
(* Related types *)

Definition rty (A B : term) := exists k R, interp k A B R.

Lemma rty_sym : forall A B, rty A B -> rty B A.
Proof. intros A B [k [R H]]; exists k, R; apply interp_sym, H. Qed.
Lemma rty_trans : forall A B C, rty A B -> rty B C -> rty A C.
Proof.
  intros A B C [k [R H]] [j [S H']]; exists (Nat.max k j), R.
  eapply interp_trans_levels; [exact H|exact H'|apply cv_refl].
Qed.
Lemma rty_conv : forall A B A' B', rty A B -> conv A A' -> conv B B' -> rty A' B'.
Proof. intros A B A' B' [k [R H]] H1 H2; exists k, R; eapply interp_conv; eassumption. Qed.
Lemma rty_tyw_l : forall A B, rty A B -> tyw A.
Proof. intros A B [k [R H]]; exists k, R; eapply interp_refl_left; exact H. Qed.
Lemma rty_tyw_r : forall A B, rty A B -> tyw B.
Proof. intros A B [k [R H]]; exists k, R; eapply interp_refl_right; exact H. Qed.
Lemma tyw_rty : forall A, tyw A -> rty A A.
Proof. intros A H; exact H. Qed.
Lemma tyw_conv : forall A A', tyw A -> conv A A' -> rty A A'.
Proof. intros A A' [k [R H]] Hc; exists k, R; eapply interp_conv; [exact H|apply cv_refl|exact Hc]. Qed.
Lemma rel_at_rty : forall t u A B, rel_at t u A B -> rty A B.
Proof. intros t u A B [k [R [H _]]]; exists k, R; exact H. Qed.

(* Relatedness only depends on the types up to relatedness. *)
Lemma rel_at_retype_l : forall t u A B A2, rel_at t u A B -> rty A A2 -> rel_at t u A2 B.
Proof.
  intros t u A B A2 Ht [k [S HS]].
  assert (Htt : rel_at t t A A2).
  { exists k, S; split; [exact HS|]. eapply rel_at_transfer; [eapply rel_at_refl_left; exact Ht|exact HS|apply cv_refl]. }
  eapply rel_at_trans; [apply rel_at_sym, Htt|exact Ht].
Qed.
Lemma rel_at_retype : forall t u A B A2 B2, rel_at t u A B -> rty A A2 -> rty B B2 -> rel_at t u A2 B2.
Proof.
  intros t u A B A2 B2 Ht HA HB. apply rel_at_sym.
  eapply rel_at_retype_l; [|exact HB]. apply rel_at_sym. eapply rel_at_retype_l; eassumption.
Qed.
Lemma rel_at_tyw : forall t u A B, rel_at t u A B -> tyw A /\ tyw B.
Proof. intros t u A B H; split; [eapply rty_tyw_l|eapply rty_tyw_r]; eapply rel_at_rty; exact H. Qed.
Lemma rel_at_rty_both : forall t u A B, rel_at t u A A -> rty A B -> rel_at t u A B.
Proof. intros t u A B H HAB. eapply rel_at_retype; [exact H|apply tyw_rty, (proj1 (rel_at_tyw _ _ _ _ H))|exact HAB]. Qed.
Lemma rel_at_left_of : forall t u A B, rel_at t u A B -> rel_at t t A A.
Proof. apply rel_at_refl_left. Qed.
Lemma rel_at_right_of : forall t u A B, rel_at t u A B -> rel_at u u B B.
Proof. intros t u A B H; exact (rel_at_refl_left _ _ _ _ (rel_at_sym _ _ _ _ H)). Qed.

(* Pi types *)
Lemma pi_rty : forall A B x U V y U' V', rty A B -> conv A (TPi x U V) -> conv B (TPi y U' V') ->
  rty U U' /\ forall a a', closed a -> closed a' -> rel_at a a' U U' -> rty (subst a x V) (subst a' y V').
Proof.
  intros A B x U V y U' V' [k [R H]] HA HB.
  destruct (interp_pi_view _ _ _ _ _ _ _ H HA) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA0 & HB0 & HU & HV & HR).
  destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HA) HA0)) as [HU1 HV1].
  destruct (conv_pi_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) HB0)) as [HU2 HV2].
  assert (HUi : interp k U U' RU) by (eapply interp_conv; [exact HU|apply cv_sym, HU1|apply cv_sym, HU2]).
  split; [exists k, RU; exact HUi|].
  intros a a' Ha Ha' Haa. exists k, (RV a a').
  eapply interp_conv; [apply HV; [exact Ha|exact Ha'|eapply rel_at_transfer; [exact Haa|exact HUi|apply cv_refl]]| |];
    apply cv_sym; [apply HV1|apply HV2]; assumption.
Qed.
Lemma pi_ex : forall A B x U V, rty A B -> conv A (TPi x U V) -> exists y U' V', conv B (TPi y U' V').
Proof.
  intros A B x U V [k [R H]] HA.
  destruct (interp_pi_view _ _ _ _ _ _ _ H HA) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA0 & HB0 & HU & HV & HR).
  exists y0, U0', V0'; exact HB0.
Qed.
Lemma pi_app_rel : forall f1 f2 A1 A2 x U V y U' V' a1 a2, rel_at f1 f2 A1 A2 ->
  conv A1 (TPi x U V) -> conv A2 (TPi y U' V') -> closed a1 -> closed a2 -> rel_at a1 a2 U U' ->
  rel_at (TApp f1 a1) (TApp f2 a2) (subst a1 x V) (subst a2 y V').
Proof.
  intros f1 f2 A1 A2 x U V y U' V' a1 a2 Hf H1 H2 Ha1 Ha2 Ha.
  eapply sem_app; [|exact Ha|exact Ha1|exact Ha2].
  eapply rel_at_conv; [exact Hf|apply cv_refl|apply cv_refl|exact H1|exact H2].
Qed.
Lemma pi_intro_rel : forall f g A B x U V y U' V', rty A B ->
  conv A (TPi x U V) -> conv B (TPi y U' V') ->
  (forall a a', closed a -> closed a' -> rel_at a a' U U' ->
     rel_at (TApp f a) (TApp g a') (subst a x V) (subst a' y V')) ->
  rel_at f g A B.
Proof.
  intros f g A B x U V y U' V' [k [R H]] HA HB Hf.
  eapply rel_at_conv; [eapply sem_pi_intro; [exists R; eapply interp_conv; [exact H|exact HA|exact HB]|exact Hf]
    |apply cv_refl|apply cv_refl|apply cv_sym, HA|apply cv_sym, HB].
Qed.

(* Enum-tagged sums *)
Lemma sum_ex : forall A B x E P L, rty A B -> conv A (TSigma x (TEnumT E) P) -> conv E (code L) ->
  exists y E' P', conv B (TSigma y (TEnumT E') P').
Proof.
  intros A B x E P L [k [R H]] HA HE.
  destruct (interp_sigma_view _ _ _ _ _ _ _ H HA) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA0 & HB0 & HU & HV & HR).
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HA) HA0)) as [HU1 HV1].
  assert (HUe : interp k (TEnumT E) U0' RU) by (eapply interp_conv; [exact HU|apply cv_sym, HU1|apply cv_refl]).
  destruct (interp_enum_view _ _ _ _ _ _ HUe (cv_refl _) HE) as [E' [HE1 _]].
  exists y0, E', V0'. eapply cv_trans; [exact HB0|].
  apply cv_compatible, cp_TSigma; [exact HE1|apply cv_refl].
Qed.
Lemma sum_rel_iff : forall A B x E P y E' P' L, rty A B ->
  conv A (TSigma x (TEnumT E) P) -> conv E (code L) -> conv B (TSigma y (TEnumT E') P') ->
  conv E' (code L) /\
  (forall m, m < List.length L -> rty (subst (enum_position m) x P) (subst (enum_position m) y P')) /\
  (forall p q, rel_at p q A B <-> exists m xs ys, m < List.length L /\ closed xs /\ closed ys /\
     conv p (TPair (enum_position m) xs) /\ conv q (TPair (enum_position m) ys) /\
     rel_at xs ys (subst (enum_position m) x P) (subst (enum_position m) y P')).
Proof.
  intros A B x E P y E' P' L [k [R H]] HA HE HB.
  destruct (sum_view _ _ _ _ _ _ _ _ _ _ _ H HA HE HB) as [HE' [Hrows HR]].
  refine (conj HE' (conj _ _)).
  - intros m Hm; destruct (Hrows m Hm) as [S HS]; exists k, S; exact HS.
  - intros p q; split.
    + intros Hpq; apply HR; eapply rel_at_transfer; [exact Hpq|exact H|apply cv_refl].
    + intros Hx; exists k, R; split; [exact H|apply HR, Hx].
Qed.

(* Close types *)
Lemma close_ex : forall A B IT F G i, rty A B -> conv A (CloseAt IT F G i) ->
  exists IT' F' G' i', conv B (CloseAt IT' F' G' i').
Proof.
  intros A B IT F G i [k [R H]] HA.
  destruct (interp_close_view _ _ _ _ _ _ _ _ H HA) as
    (IT0 & F0 & G0 & i0 & IT0' & F0' & G0' & i0' & RI & FF & FG & HA0 & HB0 & _).
  exists IT0', F0', G0', i0'; exact HB0.
Qed.
Lemma close_rel_iff : forall A B IT F G i IT' F' G' i', rty A B ->
  conv A (CloseAt IT F G i) -> conv B (CloseAt IT' F' G' i') ->
  rty (payload IT F G i) (payload IT' F' G' i') /\
  (forall t u, rel_at t u A B <-> exists xs ys, closed xs /\ closed ys /\ conv t (TIn xs) /\ conv u (TIn ys) /\
     rel_at xs ys (payload IT F G i) (payload IT' F' G' i')).
Proof.
  intros A B IT F G i IT' F' G' i' [k [R H]] HA HB.
  destruct (close_payload_interp _ _ _ _ _ _ _ _ _ _ _ _ H HA HB) as [P [HP HR]].
  split; [exists 0, P; exact HP|]. intros t u; split.
  - intros Ht. pose proof (proj1 (HR t u) (rel_at_transfer _ _ _ _ _ _ _ _ Ht H (cv_refl _)))
      as [xs [ys [Hx [Hy [Ht' [Hu' Hr]]]]]].
    exists xs, ys; repeat apply conj; try assumption. exists 0, P; split; assumption.
  - intros [xs [ys [Hx [Hy [Ht' [Hu' Hr]]]]]]. exists k, R; split; [exact H|].
    apply HR; exists xs, ys; repeat apply conj; try assumption.
    eapply rel_at_transfer; [exact Hr|exact HP|apply cv_refl].
Qed.
