(* Elaboration coherence: two elaborations of the same source expression are
   related in the binary model, over contexts linked by related types. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelCoercion.
Import ListNotations.

Definition elab_typed := elaboration_from_rules named_weakening (dead_from_rules named_weakening) sub_typed.
Lemma synth_typed : forall Gamma e A t, elab_synth Gamma e A t -> typing Gamma t A.
Proof. exact (proj1 elab_typed). Qed.
Lemma check_typed : forall Gamma e A t, elab_check Gamma e A t -> typing Gamma t A.
Proof. exact (proj1 (proj2 elab_typed)). Qed.

Lemma ext_domain : forall Gamma x A, wf Gamma -> fresh_in Gamma x -> wf (extend Gamma x A) -> type_wf Gamma A.
Proof.
  intros; eapply (extension_domain_formation named_weakening named_type_correctness named_beta_preservation); eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Closing environments *)

Lemma closing2_sym : forall Gamma g1 g2, closing2 Gamma g1 g2 -> closing2 Gamma g2 g1.
Proof.
  intros Gamma g1 g2 H; induction H; [apply c2_nil|].
  apply c2_cons; try assumption. apply rel_at_sym; assumption.
Qed.
Lemma closing2_refl_l : forall Gamma g1 g2, closing2 Gamma g1 g2 -> closing2 Gamma g1 g1.
Proof. intros; eapply closing2_refl_r, closing2_sym; eassumption. Qed.

Lemma rty_inst : forall Gamma g1 g2 A, closing2 Gamma g1 g2 -> type_wf Gamma A ->
  rty (instantiate g1 A) (instantiate g2 A).
Proof.
  intros Gamma g1 g2 A Hc [k Hk]. pose proof (rel_fundamental _ _ _ Hk _ _ Hc) as H.
  rewrite !instantiate_sort in H. apply rel_at_sort in H. destruct H as [R HR]; exists k, R; exact HR.
Qed.

Lemma closing2_lookup_rty : forall Gamma g1 g2 n A, closing2 Gamma g1 g2 -> lookup Gamma n = Some A ->
  rty (instantiate g1 A) (instantiate g2 A).
Proof. intros; eapply rel_at_rty, closing2_lookup; eassumption. Qed.

(* Two contexts closed by the same related environments, with related types. *)
Definition link (G1 G2 : ctx) (g1 g2 : env) :=
  closing2 G1 g1 g2 /\ closing2 G2 g1 g2 /\
  (forall n A1 A2, lookup G1 n = Some A1 -> lookup G2 n = Some A2 ->
     rty (instantiate g1 A1) (instantiate g2 A2)).

(* Type agreement on the pair and on both diagonals. *)
Definition TR (g1 g2 : env) (A1 A2 : term) :=
  rty (instantiate g1 A1) (instantiate g2 A2) /\ rty (instantiate g1 A1) (instantiate g1 A2) /\
  rty (instantiate g2 A1) (instantiate g2 A2).

Lemma link_same : forall Gamma g1 g2, closing2 Gamma g1 g2 -> link Gamma Gamma g1 g2.
Proof.
  intros Gamma g1 g2 H; refine (conj H (conj H _)).
  intros n A1 A2 H1 H2; rewrite H1 in H2; inversion H2; subst; eapply closing2_lookup_rty; eassumption.
Qed.

Lemma link_diag_l : forall G1 G2 g1 g2, link G1 G2 g1 g2 -> link G1 G2 g1 g1.
Proof.
  intros G1 G2 g1 g2 [H1 [H2 H3]]; refine (conj (closing2_refl_l _ _ _ H1) (conj (closing2_refl_l _ _ _ H2) _)).
  intros n A1 A2 L1 L2. eapply rty_trans; [exact (H3 _ _ _ L1 L2)|].
  apply rty_sym; exact (closing2_lookup_rty _ _ _ _ _ H2 L2).
Qed.
Lemma link_diag_r : forall G1 G2 g1 g2, link G1 G2 g1 g2 -> link G1 G2 g2 g2.
Proof.
  intros G1 G2 g1 g2 [H1 [H2 H3]]; refine (conj (closing2_refl_r _ _ _ H1) (conj (closing2_refl_r _ _ _ H2) _)).
  intros n A1 A2 L1 L2. eapply rty_trans; [apply rty_sym; exact (closing2_lookup_rty _ _ _ _ _ H1 L1)|].
  exact (H3 _ _ _ L1 L2).
Qed.

Lemma TR_wf : forall G1 G2 g1 g2 A, link G1 G2 g1 g2 -> type_wf G1 A -> type_wf G2 A -> TR g1 g2 A A.
Proof.
  intros G1 G2 g1 g2 A [H1 [H2 _]] HA1 HA2; repeat apply conj.
  - eapply rty_inst; eassumption.
  - eapply rty_inst; [eapply closing2_refl_l; exact H1|exact HA1].
  - eapply rty_inst; [eapply closing2_refl_r; exact H2|exact HA2].
Qed.

Lemma TR_conv : forall g1 g2 A1 A2 B1 B2, TR g1 g2 A1 A2 -> conv A1 B1 -> conv A2 B2 -> TR g1 g2 B1 B2.
Proof.
  intros g1 g2 A1 A2 B1 B2 [H1 [H2 H3]] C1 C2; repeat apply conj;
    [eapply rty_conv; [exact H1| |]|eapply rty_conv; [exact H2| |]|eapply rty_conv; [exact H3| |]];
    apply instantiate_conversion; assumption.
Qed.
Lemma TR_diag_l : forall g1 g2 A1 A2, TR g1 g2 A1 A2 -> TR g1 g1 A1 A2.
Proof. intros g1 g2 A1 A2 [_ [H _]]; repeat split; exact H. Qed.
Lemma TR_diag_r : forall g1 g2 A1 A2, TR g1 g2 A1 A2 -> TR g2 g2 A1 A2.
Proof. intros g1 g2 A1 A2 [_ [_ H]]; repeat split; exact H. Qed.

Lemma inst_cons_fresh : forall g x v A, ~ In x (free_vars A) -> instantiate ((x, v) :: g) A = instantiate g A.
Proof. intros g x v A H; cbn [instantiate]; rewrite subst_fresh by exact H; reflexivity. Qed.

Lemma link_extend : forall G1 G2 g1 g2 x A1 A2 v1 v2, link G1 G2 g1 g2 ->
  fresh_in G1 x -> fresh_in G2 x -> wf (extend G1 x A1) -> wf (extend G2 x A2) -> TR g1 g2 A1 A2 ->
  closed v1 -> closed v2 -> rel_at v1 v2 (instantiate g1 A1) (instantiate g2 A2) ->
  link (extend G1 x A1) (extend G2 x A2) ((x, v1) :: g1) ((x, v2) :: g2).
Proof.
  intros G1 G2 g1 g2 x A1 A2 v1 v2 [H1 [H2 H3]] Hx1 Hx2 Hw1 Hw2 [T1 [T2 T3]] Hv1 Hv2 Hv.
  pose proof (closing2_wf _ _ _ H1) as Hwf1. pose proof (closing2_wf _ _ _ H2) as Hwf2.
  destruct (ext_domain _ _ _ Hwf1 Hx1 Hw1) as [k1 HA1]. destruct (ext_domain _ _ _ Hwf2 Hx2 Hw2) as [k2 HA2].
  repeat apply conj.
  - apply closing2_extend; try assumption. eapply rel_at_retype; [exact Hv|apply tyw_rty; exact (rty_tyw_l _ _ T1)|apply rty_sym, T3].
  - apply closing2_extend; try assumption. eapply rel_at_retype; [exact Hv|exact T2|apply tyw_rty; exact (rty_tyw_r _ _ T1)].
  - intros n B1 B2 L1 L2. destruct (Nat.eq_dec n x) as [->|Hne].
    + rewrite lookup_extend_same in L1, L2. injection L1 as E1; injection L2 as E2; subst B1 B2.
      rewrite (inst_cons_fresh g1 x v1 A1) by exact (typing_fresh_not_free _ _ _ _ HA1 Hx1).
      rewrite (inst_cons_fresh g2 x v2 A2) by exact (typing_fresh_not_free _ _ _ _ HA2 Hx2). exact T1.
    + rewrite lookup_extend_other in L1, L2 by (intro E; apply Hne; symmetry; exact E).
      rewrite (inst_cons_fresh g1 x v1 B1) by exact (wf_type_fresh_not_free _ _ _ _ Hwf1 L1 Hx1).
      rewrite (inst_cons_fresh g2 x v2 B2) by exact (wf_type_fresh_not_free _ _ _ _ Hwf2 L2 Hx2).
      exact (H3 _ _ _ L1 L2).
Qed.

(* ------------------------------------------------------------------ *)
(* Checking without trailing target conversions *)

Inductive check_nt (Gamma : ctx) : expr -> term -> term -> Prop :=
| nt_core : forall t A, typing Gamma t A -> check_nt Gamma (ECore t) A t
| nt_conversion : forall e A B t, elab_synth Gamma e A t -> type_wf Gamma B -> conv A B -> check_nt Gamma e B t
| nt_subsumption : forall e A B t c, elab_synth Gamma e A t -> sub Gamma A B c -> check_nt Gamma e B (TApp c t)
| nt_lam : forall x e A B t, fresh_in Gamma x -> type_wf Gamma (TPi x A B) ->
    elab_check (extend Gamma x A) e B t -> check_nt Gamma (ELam x e) (TPi x A B) (TLam x t)
| nt_pair : forall x e f A B t u, type_wf Gamma (TSigma x A B) -> elab_check Gamma e A t ->
    elab_check Gamma f (subst t x B) u -> check_nt Gamma (EPair e f) (TSigma x A B) (TPair t u)
| nt_constructor : forall name e IT F G i rs n D xs, close_input Gamma IT F G i ->
    row_view Gamma IT (TApp F i) rs -> nth_error rs n = Some (name, D) ->
    elab_check Gamma e (TInterp IT D (carrier IT G)) xs ->
    check_nt Gamma (EConstructor name e) (CloseAt IT F G i) (TIn (TPair (enum_position n) xs)).

Lemma check_peel : forall Gamma e A t, elab_check Gamma e A t -> exists A0, conv A0 A /\ check_nt Gamma e A0 t.
Proof.
  intros Gamma e A t H; induction H.
  - exists A; split; [apply cv_refl|apply nt_core; assumption].
  - exists B; split; [apply cv_refl|eapply nt_conversion; eassumption].
  - destruct IHelab_check as [A0 [HA0 Hnt]]; exists A0; split; [eapply cv_trans; eassumption|exact Hnt].
  - exists B; split; [apply cv_refl|eapply nt_subsumption; eassumption].
  - eexists; split; [apply cv_refl|apply nt_lam; assumption].
  - eexists; split; [apply cv_refl|eapply nt_pair; eassumption].
  - eexists; split; [apply cv_refl|eapply nt_constructor; eassumption].
Qed.

(* ------------------------------------------------------------------ *)
(* Check outputs obtained from synthesis followed by a coercion *)

Lemma via_graphs : forall A1 B1 A2 B2 G1 G2 t1 o1 t2 o2,
  Gr A1 B1 G1 -> Gr A2 B2 G2 -> rty A1 A2 -> rty B1 B2 ->
  rel_at t1 t2 A1 A2 -> G1 t1 o1 -> G2 t2 o2 -> rel_at o1 o2 B1 B2.
Proof.
  intros A1 B1 A2 B2 G1 G2 t1 o1 t2 o2 H1 H2 HA HB Ht Ho1 Ho2.
  assert (H2' : Gr A1 B1 G2) by (eapply Gr_transport; [exact H2|apply rty_sym, HA|apply rty_sym, HB]).
  eapply rel_at_retype; [eapply (Gr_func _ _ _ H1 _ H2' _ _ _ _ Ho1 Ho2)|apply tyw_rty; exact (rty_tyw_l _ _ HB)|exact HB].
  eapply rel_at_retype; [exact Ht|apply tyw_rty; exact (rty_tyw_l _ _ HA)|apply rty_sym, HA].
Qed.

Lemma synth_side : forall Gamma g e B t', closing2 Gamma g g ->
  ((exists A, elab_synth Gamma e A t' /\ type_wf Gamma B /\ conv A B) \/
   (exists A t c, elab_synth Gamma e A t /\ sub Gamma A B c /\ t' = TApp c t)) ->
  exists A t G, elab_synth Gamma e A t /\ Gr (instantiate g A) (instantiate g B) G /\
    G (instantiate g t) (instantiate g t').
Proof.
  intros Gamma g e B t' Hc [(A & Hs & HB & HAB)|(A & t & c & Hs & Hsub & ->)].
  - pose proof (synth_typed _ _ _ _ Hs) as Ht.
    assert (HAw : tyw (instantiate g A)) by (eapply tyw_inst; [exact Hc|eapply type_wf_of_typing; exact Ht]).
    assert (HR : rty (instantiate g A) (instantiate g B)) by (apply tyw_conv; [exact HAw|apply instantiate_conversion, HAB]).
    exists A, t', (eq_graph (instantiate g A) (instantiate g B)); repeat apply conj;
      [exact Hs|apply gr_eq, HR|eapply inst_closed1; eassumption|eapply inst_closed1; eassumption|].
    eapply rel_at_retype; [exact (fund_self _ _ _ _ Hc Ht)|apply tyw_rty, HAw|exact HR].
  - pose proof (synth_typed _ _ _ _ Hs) as Ht.
    destruct (sub_real _ _ _ _ Hsub g Hc) as [G [HG R]].
    exists A, t, G; repeat apply conj; [exact Hs|exact HG|].
    rewrite instantiate_app. apply R; [eapply inst_closed1; eassumption|exact (fund_self _ _ _ _ Hc Ht)].
Qed.

(* ------------------------------------------------------------------ *)
(* Further semantic helpers *)

Lemma sigma_rty : forall A B x U V y U' V', rty A B -> conv A (TSigma x U V) -> conv B (TSigma y U' V') ->
  rty U U' /\ forall a a', closed a -> closed a' -> rel_at a a' U U' -> rty (subst a x V) (subst a' y V').
Proof.
  intros A B x U V y U' V' [k [R H]] HA HB.
  destruct (interp_sigma_view _ _ _ _ _ _ _ H HA) as
    (x0 & U0 & V0 & y0 & U0' & V0' & RU & RV & HA0 & HB0 & HU & HV & HR).
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HA) HA0)) as [HU1 HV1].
  destruct (conv_sigma_inv _ _ _ _ _ _ (cv_trans (cv_sym HB) HB0)) as [HU2 HV2].
  assert (HUi : interp k U U' RU) by (eapply interp_conv; [exact HU|apply cv_sym, HU1|apply cv_sym, HU2]).
  split; [exists k, RU; exact HUi|].
  intros a a' Ha Ha' Haa. exists k, (RV a a').
  eapply interp_conv; [apply HV; [exact Ha|exact Ha'|eapply rel_at_transfer; [exact Haa|exact HUi|apply cv_refl]]| |];
    apply cv_sym; [apply HV1|apply HV2]; assumption.
Qed.

Lemma carrier_typed : forall Gamma IT F G i, close_input Gamma IT F G i -> typing Gamma (carrier IT G) (Family IT).
Proof. intros Gamma IT F G i [HIT [_ [HG _]]]; apply ty_close; assumption. Qed.

Lemma row_payload_wf : forall Gamma IT F G i rs m name D, close_input Gamma IT F G i ->
  row_view Gamma IT (TApp F i) rs -> nth_error rs m = Some (name, D) ->
  type_wf Gamma (TInterp IT D (carrier IT G)).
Proof.
  intros Gamma IT F G i rs m name D Hin Hv Hm. destruct Hv as [rs Hr _ _].
  exists 0; apply ty_interp; [exact (proj1 Hin)|eapply row_nth_typed; eassumption|eapply carrier_typed; exact Hin].
Qed.

(* Related close types with row views: same row names, related payloads per row. *)
Lemma close_rows : forall G1 G2 h1 h2 IT F G i rs IT' F' G' i' rs',
  closing2 G1 h1 h1 -> closing2 G2 h2 h2 ->
  close_input G1 IT F G i -> close_input G2 IT' F' G' i' ->
  row_view G1 IT (TApp F i) rs -> row_view G2 IT' (TApp F' i') rs' ->
  rty (instantiate h1 (CloseAt IT F G i)) (instantiate h2 (CloseAt IT' F' G' i')) ->
  row_names rs = row_names rs' /\
  (forall m name D name' D', nth_error rs m = Some (name, D) -> nth_error rs' m = Some (name', D') ->
     name' = name /\ rty (instantiate h1 (TInterp IT D (carrier IT G))) (instantiate h2 (TInterp IT' D' (carrier IT' G')))) /\
  (forall t u, rel_at t u (instantiate h1 (CloseAt IT F G i)) (instantiate h2 (CloseAt IT' F' G' i')) <->
     exists m name D D' v1 v2, nth_error rs m = Some (name, D) /\ nth_error rs' m = Some (name, D') /\
       closed v1 /\ closed v2 /\ conv t (TIn (TPair (enum_position m) v1)) /\ conv u (TIn (TPair (enum_position m) v2)) /\
       rel_at v1 v2 (instantiate h1 (TInterp IT D (carrier IT G))) (instantiate h2 (TInterp IT' D' (carrier IT' G')))).
Proof.
  intros G1 G2 h1 h2 IT F G i rs IT' F' G' i' rs' Hc1 Hc2 Hin1 Hin2 Hv1 Hv2 HR.
  rewrite !inst_CloseAt in HR.
  destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ HR (cv_refl _) (cv_refl _)) as [HP Hiff].
  rewrite <- !inst_payload in HP. unfold payload in HP.
  destruct (row_sum _ h1 _ _ _ _ Hc1 Hv1 (carrier_typed _ _ _ _ _ Hin1)) as [z1 [P1 [HS1 HP1]]].
  destruct (row_sum _ h2 _ _ _ _ Hc2 Hv2 (carrier_typed _ _ _ _ _ Hin2)) as [z2 [P2 [HS2 HP2]]].
  destruct (sum_rel_iff _ _ _ _ _ _ _ _ (row_names rs) HP HS1 ltac:(rewrite row_enum_code; apply cv_refl) HS2)
    as [HE [Hrows Hsum]].
  rewrite row_enum_code in HE. pose proof (conv_code_inv _ _ HE) as Hnames.
  assert (Hnth : forall m name D name' D', nth_error rs m = Some (name, D) -> nth_error rs' m = Some (name', D') -> name' = name).
  { intros m name D name' D' H1 H2. pose proof (row_names_nth _ _ _ _ H1) as N1. pose proof (row_names_nth _ _ _ _ H2) as N2.
    rewrite Hnames in N2. congruence. }
  refine (conj (eq_sym Hnames) (conj _ _)).
  - intros m name D name' D' H1 H2. split; [eapply Hnth; eassumption|].
    eapply rty_conv; [apply Hrows; eapply nth_error_lt; exact (row_names_nth _ _ _ _ H1)| |].
    + exact (HP1 _ _ _ H1).
    + exact (HP2 _ _ _ H2).
  - intros t u. rewrite !inst_CloseAt, Hiff. split.
    + intros (xs & ys & Hxs & Hys & Ht & Hu & Hr). rewrite <- !inst_payload in Hr. unfold payload in Hr.
      destruct (proj1 (Hsum xs ys) Hr) as (m & v1 & v2 & Hm & Hv1c & Hv2c & Hxsc & Hysc & Hvv).
      destruct (row_nth_exists _ _ Hm) as [name [D HD]].
      assert (Hm' : m < List.length (row_names rs')) by (rewrite Hnames; exact Hm).
      destruct (row_nth_exists _ _ Hm') as [name' [D' HD']].
      pose proof (Hnth _ _ _ _ _ HD HD') as ->.
      exists m, name, D, D', v1, v2; repeat apply conj; try assumption.
      * eapply cv_trans; [exact Ht|apply conv_in, Hxsc].
      * eapply cv_trans; [exact Hu|apply conv_in, Hysc].
      * eapply rel_at_conv; [exact Hvv|apply cv_refl|apply cv_refl|exact (HP1 _ _ _ HD)|exact (HP2 _ _ _ HD')].
    + intros (m & name & D & D' & v1 & v2 & HD & HD' & Hv1c & Hv2c & Ht & Hu & Hvv).
      exists (TPair (enum_position m) v1), (TPair (enum_position m) v2); repeat apply conj;
        try (apply closed_pair; [apply closed_position|assumption]); try assumption.
      rewrite <- !inst_payload; unfold payload. apply Hsum.
      exists m, v1, v2; repeat apply conj; try assumption; try apply cv_refl.
      * eapply nth_error_lt; exact (row_names_nth _ _ _ _ HD).
      * eapply rel_at_conv; [exact Hvv|apply cv_refl|apply cv_refl|apply cv_sym, (HP1 _ _ _ HD)|apply cv_sym, (HP2 _ _ _ HD')].
Qed.

Lemma cases_handler_exists : forall Gamma k IT X Q bs rs hs, elab_cases Gamma k IT X Q bs rs hs ->
  forall m entry, nth_error rs m = Some entry -> exists h, nth_error hs m = Some h.
Proof.
  intros Gamma k IT X Q bs rs hs H; induction H; intros [|m] entry Hm; cbn in *; try discriminate; eauto.
Qed.

Lemma nodup_fst_unique : forall {V} (l : list (string * V)) k v v', NoDup (map fst l) ->
  In (k, v) l -> In (k, v') l -> v = v'.
Proof.
  intros V l; induction l as [|[k0 w] l IH]; intros k v v' HN H1 H2; [destruct H1|].
  cbn in HN; inversion HN as [|? ? Hnot HN']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - inversion E1; inversion E2; subst; reflexivity.
  - inversion E1; subst. exfalso; apply Hnot, in_map_iff; exists (k, v'); split; [reflexivity|exact H2].
  - inversion E2; subst. exfalso; apply Hnot, in_map_iff; exists (k, v); split; [reflexivity|exact H1].
  - eapply IH; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversions *)

Definition synthesizable (e : expr) :=
  match e with ECore _ | ELam _ _ | EPair _ _ | EConstructor _ _ => False | _ => True end.

Lemma synth_synthesizable : forall Gamma e A t, elab_synth Gamma e A t -> synthesizable e.
Proof. intros Gamma e A t H; destruct H; exact I. Qed.

Lemma nt_core_inv : forall Gamma t A u, check_nt Gamma (ECore t) A u -> u = t /\ typing Gamma t A.
Proof.
  intros Gamma t A u H; inversion H; subst; [split; [reflexivity|assumption]| |];
    match goal with Hs : elab_synth _ _ _ _ |- _ => destruct (synth_synthesizable _ _ _ _ Hs) end.
Qed.

Lemma nt_lam_inv : forall Gamma x e A u, check_nt Gamma (ELam x e) A u ->
  exists A' B' t', A = TPi x A' B' /\ u = TLam x t' /\ fresh_in Gamma x /\ type_wf Gamma (TPi x A' B') /\
    elab_check (extend Gamma x A') e B' t'.
Proof.
  intros Gamma x e A u H; inversion H; subst;
    try (match goal with Hs : elab_synth _ _ _ _ |- _ => destruct (synth_synthesizable _ _ _ _ Hs) end).
  do 3 eexists; refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))); eassumption.
Qed.

Lemma nt_pair_inv : forall Gamma e f A u, check_nt Gamma (EPair e f) A u ->
  exists x A' B' t' u', A = TSigma x A' B' /\ u = TPair t' u' /\ type_wf Gamma (TSigma x A' B') /\
    elab_check Gamma e A' t' /\ elab_check Gamma f (subst t' x B') u'.
Proof.
  intros Gamma e f A u H; inversion H; subst;
    try (match goal with Hs : elab_synth _ _ _ _ |- _ => destruct (synth_synthesizable _ _ _ _ Hs) end).
  do 5 eexists; refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))); eassumption.
Qed.

Lemma nt_constructor_inv : forall Gamma name e A u, check_nt Gamma (EConstructor name e) A u ->
  exists IT F G i rs n D xs, A = CloseAt IT F G i /\ u = TIn (TPair (enum_position n) xs) /\
    close_input Gamma IT F G i /\ row_view Gamma IT (TApp F i) rs /\ nth_error rs n = Some (name, D) /\
    elab_check Gamma e (TInterp IT D (carrier IT G)) xs.
Proof.
  intros Gamma name e A u H; inversion H; subst;
    try (match goal with Hs : elab_synth _ _ _ _ |- _ => destruct (synth_synthesizable _ _ _ _ Hs) end).
  do 8 eexists; refine (conj eq_refl (conj eq_refl (conj _ (conj _ (conj _ _))))); eassumption.
Qed.

Lemma nt_synth_inv : forall Gamma e B u, check_nt Gamma e B u -> synthesizable e ->
  (exists A, elab_synth Gamma e A u /\ type_wf Gamma B /\ conv A B) \/
  (exists A t c, elab_synth Gamma e A t /\ sub Gamma A B c /\ u = TApp c t).
Proof.
  intros Gamma e B u H Hs; destruct H; try destruct Hs; [left|right]; eauto 6.
Qed.

Lemma side_conv : forall Gamma g e A t B, closing2 Gamma g g -> elab_synth Gamma e A t -> type_wf Gamma B ->
  conv A B -> exists G, Gr (instantiate g A) (instantiate g B) G /\ G (instantiate g t) (instantiate g t).
Proof.
  intros Gamma g e A t B Hc Hs HB HAB.
  destruct (synth_side Gamma g e B t Hc (or_introl (ex_intro _ A (conj Hs (conj HB HAB)))))
    as (A' & t' & G & Hs' & HG & HGt).
  pose proof (synth_typed _ _ _ _ Hs) as Ht.
  assert (HAw : tyw (instantiate g A)) by (eapply tyw_inst; [exact Hc|eapply type_wf_of_typing; exact Ht]).
  assert (HR : rty (instantiate g A) (instantiate g B)) by (apply tyw_conv; [exact HAw|apply instantiate_conversion, HAB]).
  exists (eq_graph (instantiate g A) (instantiate g B)); split; [apply gr_eq, HR|].
  repeat apply conj; [eapply inst_closed1; eassumption|eapply inst_closed1; eassumption|].
  eapply rel_at_retype; [exact (fund_self _ _ _ _ Hc Ht)|apply tyw_rty, HAw|exact HR].
Qed.

Lemma side_sub : forall Gamma g e A t B c, closing2 Gamma g g -> elab_synth Gamma e A t -> sub Gamma A B c ->
  exists G, Gr (instantiate g A) (instantiate g B) G /\ G (instantiate g t) (instantiate g (TApp c t)).
Proof.
  intros Gamma g e A t B c Hc Hs Hsub. pose proof (synth_typed _ _ _ _ Hs) as Ht.
  destruct (sub_real _ _ _ _ Hsub g Hc) as [G [HG R]].
  exists G; split; [exact HG|]. rewrite instantiate_app. apply R; [eapply inst_closed1; eassumption|exact (fund_self _ _ _ _ Hc Ht)].
Qed.

Lemma case_term_conv : forall g k IT F G i Q rs hs x m name D h v,
  closed v -> conv (instantiate g x) (TIn (TPair (enum_position m) v)) ->
  nth_error rs m = Some (name, D) -> nth_error hs m = Some h ->
  conv (instantiate g (case_term k IT F G i Q rs hs x)) (TApp (instantiate g h) v).
Proof.
  intros g k IT F G i Q rs hs x m name D h v Hv Hx Hm Hh. unfold case_term; cbv zeta.
  rewrite inst_ccase.
  eapply cv_trans; [apply cv_compatible, cp_TCloseCase;
    [apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|exact Hx]|].
  eapply cv_trans; [apply conv_root; reflexivity|].
  rewrite <- inst_app_closed by (apply closed_pair; [apply closed_position|exact Hv]).
  rewrite <- (inst_app_closed g h v) by exact Hv.
  apply instantiate_conversion. eapply row_map_selected; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Coherence statements *)

Definition SynthP (G1 : ctx) (e : expr) (A1 t1 : term) := forall G2 A2 t2, elab_synth G2 e A2 t2 ->
  forall g1 g2, link G1 G2 g1 g2 ->
  rty (instantiate g1 A1) (instantiate g2 A2) /\
  rel_at (instantiate g1 t1) (instantiate g2 t2) (instantiate g1 A1) (instantiate g2 A2).

Definition CheckP (G1 : ctx) (e : expr) (A1 t1 : term) := forall G2 A2 t2, elab_check G2 e A2 t2 ->
  forall g1 g2, link G1 G2 g1 g2 -> TR g1 g2 A1 A2 ->
  rel_at (instantiate g1 t1) (instantiate g2 t2) (instantiate g1 A1) (instantiate g2 A2).

Definition CasesP (G1 : ctx) (k : nat) (IT X Q : term) (bs : list (string * (nat * expr))) (rs : row) (hs : list term) :=
  forall G2 k' IT' X' rs' hs', elab_cases G2 k' IT' X' Q bs rs' hs' ->
  NoDup (clause_names bs) -> row_names rs = row_names rs' ->
  forall g1 g2, link G1 G2 g1 g2 -> typing G1 Q (TSort k) -> typing G2 Q (TSort k') -> TR g1 g2 Q Q ->
  (forall m name D D', nth_error rs m = Some (name, D) -> nth_error rs' m = Some (name, D') ->
     TR g1 g2 (TInterp IT D X) (TInterp IT' D' X')) ->
  forall m name D D' h h' v1 v2, nth_error rs m = Some (name, D) -> nth_error rs' m = Some (name, D') ->
    nth_error hs m = Some h -> nth_error hs' m = Some h' -> closed v1 -> closed v2 ->
    rel_at v1 v2 (instantiate g1 (TInterp IT D X)) (instantiate g2 (TInterp IT' D' X')) ->
    rel_at (TApp (instantiate g1 h) v1) (TApp (instantiate g2 h') v2) (instantiate g1 Q) (instantiate g2 Q).

Lemma CheckP_of_nt : forall G1 e A1 t1,
  (forall G2 A0 t2, check_nt G2 e A0 t2 -> forall g1 g2, link G1 G2 g1 g2 -> TR g1 g2 A1 A0 ->
     rel_at (instantiate g1 t1) (instantiate g2 t2) (instantiate g1 A1) (instantiate g2 A0)) ->
  CheckP G1 e A1 t1.
Proof.
  intros G1 e A1 t1 H G2 A2 t2 H2 g1 g2 Hl HT.
  destruct (check_peel _ _ _ _ H2) as [A0 [HA0 Hnt]].
  eapply rel_at_conv; [apply (H _ _ _ Hnt _ _ Hl)|apply cv_refl|apply cv_refl|apply cv_refl|apply instantiate_conversion, HA0].
  eapply TR_conv; [exact HT|apply cv_refl|apply cv_sym, HA0].
Qed.

Lemma case_es_app : forall G1 G2 g1 g2 x f a A B t u x' A' B' t' u',
  link G1 G2 g1 g2 -> elab_check G1 a A u -> elab_check G2 a A' u' ->
  elab_synth G2 f (TPi x' A' B') t' ->
  SynthP G1 f (TPi x A B) t -> CheckP G1 a A u ->
  rty (instantiate g1 (subst u x B)) (instantiate g2 (subst u' x' B')) /\
  rel_at (instantiate g1 (TApp t u)) (instantiate g2 (TApp t' u'))
    (instantiate g1 (subst u x B)) (instantiate g2 (subst u' x' B')).
Proof.
  intros G1 G2 g1 g2 x f a A B t u x' A' B' t' u' Hl Ha Ha' Hf' IHf IHa.
  pose proof Hl as [Hc1 [Hc2 _]]. destruct (closing2_closed _ _ _ Hc1) as [Hg1 Hg2].
  destruct (IHf _ _ _ Hf' _ _ Hl) as [HRp Rt].
  destruct (IHf _ _ _ Hf' _ _ (link_diag_l _ _ _ _ Hl)) as [HRl _].
  destruct (IHf _ _ _ Hf' _ _ (link_diag_r _ _ _ _ Hl)) as [HRr _].
  rewrite !inst_pi in HRp, HRl, HRr, Rt by assumption.
  destruct (pi_rty _ _ _ _ _ _ _ _ HRp (cv_refl _) (cv_refl _)) as [HUp HVp].
  destruct (pi_rty _ _ _ _ _ _ _ _ HRl (cv_refl _) (cv_refl _)) as [HUl _].
  destruct (pi_rty _ _ _ _ _ _ _ _ HRr (cv_refl _) (cv_refl _)) as [HUr _].
  pose proof (IHa _ _ _ Ha' _ _ Hl (conj HUp (conj HUl HUr))) as Ru.
  pose proof (proj1 (inst_closed_typed _ _ _ _ _ Hc1 (check_typed _ _ _ _ Ha))) as Hcu1.
  pose proof (proj2 (inst_closed_typed _ _ _ _ _ Hc2 (check_typed _ _ _ _ Ha'))) as Hcu2.
  pose proof (cv_alpha (inst_subst g1 u x B Hg1)) as Hs1.
  pose proof (cv_alpha (inst_subst g2 u' x' B' Hg2)) as Hs2.
  split.
  - eapply rty_conv; [exact (HVp _ _ Hcu1 Hcu2 Ru)|apply cv_sym, Hs1|apply cv_sym, Hs2].
  - rewrite !instantiate_app. eapply rel_at_conv; [eapply sem_app; [exact Rt|exact Ru|exact Hcu1|exact Hcu2]
      |apply cv_refl|apply cv_refl|apply cv_sym, Hs1|apply cv_sym, Hs2].
Qed.

Lemma case_via_synth : forall G1 G2 g1 g2 e B B2 o1 o2,
  link G1 G2 g1 g2 -> TR g1 g2 B B2 ->
  (exists A t G, SynthP G1 e A t /\ Gr (instantiate g1 A) (instantiate g1 B) G /\
     G (instantiate g1 t) (instantiate g1 o1)) ->
  (exists A t G, elab_synth G2 e A t /\ Gr (instantiate g2 A) (instantiate g2 B2) G /\
     G (instantiate g2 t) (instantiate g2 o2)) ->
  rel_at (instantiate g1 o1) (instantiate g2 o2) (instantiate g1 B) (instantiate g2 B2).
Proof.
  intros G1 G2 g1 g2 e B B2 o1 o2 Hl HT (A & t & G & IH & HG & Ho) (A' & t' & G' & Hs' & HG' & Ho').
  destruct (IH _ _ _ Hs' _ _ Hl) as [HA Ht].
  eapply via_graphs; [exact HG|exact HG'|exact HA|exact (proj1 HT)|exact Ht|exact Ho|exact Ho'].
Qed.

Lemma second_side : forall G2 g1 g2 e B2 t2, closing2 G2 g1 g2 -> check_nt G2 e B2 t2 -> synthesizable e ->
  exists A t G, elab_synth G2 e A t /\ Gr (instantiate g2 A) (instantiate g2 B2) G /\
    G (instantiate g2 t) (instantiate g2 t2).
Proof.
  intros G2 g1 g2 e B2 t2 Hc Hnt He. pose proof (closing2_refl_r _ _ _ Hc) as Hc'.
  destruct (nt_synth_inv _ _ _ _ Hnt He) as [(A & Hs & HB & HAB)|(A & t & c & Hs & Hsub & ->)].
  - destruct (side_conv _ _ _ _ _ _ Hc' Hs HB HAB) as [G [HG Ho]]. exists A, t2, G; repeat split; assumption.
  - destruct (side_sub _ _ _ _ _ _ _ Hc' Hs Hsub) as [G [HG Ho]]. exists A, t, G; repeat split; assumption.
Qed.

Lemma case_ec_lam : forall G1 G2 g1 g2 x e A B t A' B' t',
  link G1 G2 g1 g2 -> TR g1 g2 (TPi x A B) (TPi x A' B') ->
  fresh_in G1 x -> fresh_in G2 x ->
  elab_check (extend G1 x A) e B t -> elab_check (extend G2 x A') e B' t' ->
  CheckP (extend G1 x A) e B t ->
  rel_at (instantiate g1 (TLam x t)) (instantiate g2 (TLam x t'))
    (instantiate g1 (TPi x A B)) (instantiate g2 (TPi x A' B')).
Proof.
  intros G1 G2 g1 g2 x e A B t A' B' t' Hl [HTp [HTl HTr]] Hx1 Hx2 Hc Hc' IHc.
  pose proof Hl as [Hc1 [Hc2 _]]. destruct (closing2_closed _ _ _ Hc1) as [Hg1 Hg2].
  destruct (closing2_away _ _ _ _ Hc1 Hx1) as [Ha1 Ha2].
  rewrite !inst_pi in HTp, HTl, HTr by assumption. rewrite !inst_pi, !inst_lam by assumption.
  rewrite !(drop_away g1 x), !(drop_away g2 x) in * by assumption.
  destruct (pi_rty _ _ _ _ _ _ _ _ HTp (cv_refl _) (cv_refl _)) as [HUp HVp].
  destruct (pi_rty _ _ _ _ _ _ _ _ HTl (cv_refl _) (cv_refl _)) as [HUl HVl].
  destruct (pi_rty _ _ _ _ _ _ _ _ HTr (cv_refl _) (cv_refl _)) as [HUr HVr].
  destruct HTp as [k [R HR]].
  eapply sem_lam with (k := k); [exists R; exact HR|]. intros a1 a2 Hca1 Hca2 Ha.
  pose proof (typing_context _ _ _ (check_typed _ _ _ _ Hc)) as Hw1.
  pose proof (typing_context _ _ _ (check_typed _ _ _ _ Hc')) as Hw2.
  pose proof (link_extend _ _ _ _ _ _ _ _ _ Hl Hx1 Hx2 Hw1 Hw2 (conj HUp (conj HUl HUr)) Hca1 Hca2 Ha) as Hlext.
  pose proof (fun T => inst_cons_conv g1 x a1 T Hg1 Ha1 Hca1) as C1.
  pose proof (fun T => inst_cons_conv g2 x a2 T Hg2 Ha2 Hca2) as C2.
  assert (Ha11 : rel_at a1 a1 (instantiate g1 A) (instantiate g1 A')).
  { eapply rel_at_retype; [exact (rel_at_left_of _ _ _ _ Ha)|apply tyw_rty; exact (rty_tyw_l _ _ HUl)|exact HUl]. }
  assert (Ha22 : rel_at a2 a2 (instantiate g2 A) (instantiate g2 A')).
  { eapply rel_at_retype; [exact (rel_at_right_of _ _ _ _ Ha)|apply rty_sym, HUr|apply tyw_rty; exact (rty_tyw_r _ _ HUr)]. }
  assert (HText : TR ((x, a1) :: g1) ((x, a2) :: g2) B B').
  { repeat apply conj.
    - eapply rty_conv; [exact (HVp _ _ Hca1 Hca2 Ha)|apply cv_sym, C1|apply cv_sym, C2].
    - eapply rty_conv; [exact (HVl _ _ Hca1 Hca1 Ha11)|apply cv_sym, C1|apply cv_sym, C1].
    - eapply rty_conv; [exact (HVr _ _ Hca2 Hca2 Ha22)|apply cv_sym, C2|apply cv_sym, C2]. }
  pose proof (IHc _ _ _ Hc' _ _ Hlext HText) as Rt.
  eapply rel_at_conv; [exact Rt|apply C1|apply C2|apply C1|apply C2].
Qed.

Lemma case_ec_pair : forall G1 G2 g1 g2 x e f A B t u x' A' B' t' u',
  link G1 G2 g1 g2 -> TR g1 g2 (TSigma x A B) (TSigma x' A' B') ->
  elab_check G1 e A t -> elab_check G1 f (subst t x B) u ->
  elab_check G2 e A' t' -> elab_check G2 f (subst t' x' B') u' ->
  CheckP G1 e A t -> CheckP G1 f (subst t x B) u ->
  rel_at (instantiate g1 (TPair t u)) (instantiate g2 (TPair t' u'))
    (instantiate g1 (TSigma x A B)) (instantiate g2 (TSigma x' A' B')).
Proof.
  intros G1 G2 g1 g2 x e f A B t u x' A' B' t' u' Hl [HTp [HTl HTr]] He Hf He' Hf' IHe IHf.
  pose proof Hl as [Hc1 [Hc2 _]]. destruct (closing2_closed _ _ _ Hc1) as [Hg1 Hg2].
  rewrite !inst_sigma in HTp, HTl, HTr by assumption. rewrite !inst_sigma by assumption.
  destruct (sigma_rty _ _ _ _ _ _ _ _ HTp (cv_refl _) (cv_refl _)) as [HUp HVp].
  destruct (sigma_rty _ _ _ _ _ _ _ _ HTl (cv_refl _) (cv_refl _)) as [HUl HVl].
  destruct (sigma_rty _ _ _ _ _ _ _ _ HTr (cv_refl _) (cv_refl _)) as [HUr HVr].
  assert (HTA : TR g1 g2 A A') by exact (conj HUp (conj HUl HUr)).
  pose proof (IHe _ _ _ He' _ _ Hl HTA) as Rt.
  pose proof (IHe _ _ _ He' _ _ (link_diag_l _ _ _ _ Hl) (TR_diag_l _ _ _ _ HTA)) as Rt1.
  pose proof (IHe _ _ _ He' _ _ (link_diag_r _ _ _ _ Hl) (TR_diag_r _ _ _ _ HTA)) as Rt2.
  destruct (inst_closed_typed _ _ _ _ _ Hc1 (check_typed _ _ _ _ He)) as [Ht1 Ht2].
  destruct (inst_closed_typed _ _ _ _ _ Hc2 (check_typed _ _ _ _ He')) as [Ht1' Ht2'].
  pose proof (cv_alpha (inst_subst g1 t x B Hg1)) as S1.
  pose proof (cv_alpha (inst_subst g1 t' x' B' Hg1)) as S1'.
  pose proof (cv_alpha (inst_subst g2 t x B Hg2)) as S2.
  pose proof (cv_alpha (inst_subst g2 t' x' B' Hg2)) as S2'.
  assert (HTB : TR g1 g2 (subst t x B) (subst t' x' B')).
  { repeat apply conj.
    - eapply rty_conv; [exact (HVp _ _ Ht1 Ht2' Rt)|apply cv_sym, S1|apply cv_sym, S2'].
    - eapply rty_conv; [exact (HVl _ _ Ht1 Ht1' Rt1)|apply cv_sym, S1|apply cv_sym, S1'].
    - eapply rty_conv; [exact (HVr _ _ Ht2 Ht2' Rt2)|apply cv_sym, S2|apply cv_sym, S2']. }
  pose proof (IHf _ _ _ Hf' _ _ Hl HTB) as Ru.
  destruct (inst_closed_typed _ _ _ _ _ Hc1 (check_typed _ _ _ _ Hf)) as [Hu1 _].
  destruct (inst_closed_typed _ _ _ _ _ Hc2 (check_typed _ _ _ _ Hf')) as [_ Hu2].
  destruct HTp as [k [R HR]]. rewrite !inst_tpair.
  eapply sem_pair; [exists R; exact HR|exact Ht1|exact Ht2'|exact Hu1|exact Hu2|exact Rt|].
  eapply rel_at_conv; [exact Ru|apply cv_refl|apply cv_refl|exact S1|exact S2'].
Qed.

Lemma row_view_nodup : forall Gamma IT D rs, row_view Gamma IT D rs -> NoDup (row_names rs).
Proof. intros Gamma IT D rs H; destruct H as [rs [_ [HN _]] _ _]; exact HN. Qed.

Lemma case_ec_constructor : forall G1 G2 g1 g2 name e IT F G i rs n D xs IT' F' G' i' rs' n' D' xs',
  link G1 G2 g1 g2 -> TR g1 g2 (CloseAt IT F G i) (CloseAt IT' F' G' i') ->
  close_input G1 IT F G i -> row_view G1 IT (TApp F i) rs -> nth_error rs n = Some (name, D) ->
  close_input G2 IT' F' G' i' -> row_view G2 IT' (TApp F' i') rs' -> nth_error rs' n' = Some (name, D') ->
  elab_check G1 e (TInterp IT D (carrier IT G)) xs -> elab_check G2 e (TInterp IT' D' (carrier IT' G')) xs' ->
  CheckP G1 e (TInterp IT D (carrier IT G)) xs ->
  rel_at (instantiate g1 (TIn (TPair (enum_position n) xs))) (instantiate g2 (TIn (TPair (enum_position n') xs')))
    (instantiate g1 (CloseAt IT F G i)) (instantiate g2 (CloseAt IT' F' G' i')).
Proof.
  intros G1 G2 g1 g2 name e IT F G i rs n D xs IT' F' G' i' rs' n' D' xs' Hl [HTp [HTl HTr]]
    Hin Hv Hn Hin' Hv' Hn' He He' IHe.
  pose proof Hl as [Hc1 [Hc2 _]].
  pose proof (closing2_refl_l _ _ _ Hc1) as Hc11. pose proof (closing2_refl_r _ _ _ Hc2) as Hc22.
  pose proof (closing2_refl_l _ _ _ Hc2) as Hc21. pose proof (closing2_refl_r _ _ _ Hc1) as Hc12.
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc11 Hc22 Hin Hin' Hv Hv' HTp) as [Hnames [Hrow Hiff]].
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc11 Hc21 Hin Hin' Hv Hv' HTl) as [_ [Hrowl _]].
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc12 Hc22 Hin Hin' Hv Hv' HTr) as [_ [Hrowr _]].
  assert (En : n' = n).
  { pose proof (row_names_nth _ _ _ _ Hn) as N1. pose proof (row_names_nth _ _ _ _ Hn') as N2.
    rewrite Hnames in N1. exact (nodup_same_name _ _ _ _ (row_view_nodup _ _ _ _ Hv') N2 N1). }
  subst n'.
  assert (HTP : TR g1 g2 (TInterp IT D (carrier IT G)) (TInterp IT' D' (carrier IT' G'))).
  { exact (conj (proj2 (Hrow _ _ _ _ _ Hn Hn')) (conj (proj2 (Hrowl _ _ _ _ _ Hn Hn')) (proj2 (Hrowr _ _ _ _ _ Hn Hn')))). }
  pose proof (IHe _ _ _ He' _ _ Hl HTP) as Rx.
  destruct (inst_closed_typed _ _ _ _ _ Hc1 (check_typed _ _ _ _ He)) as [Hx1 _].
  destruct (inst_closed_typed _ _ _ _ _ Hc2 (check_typed _ _ _ _ He')) as [_ Hx2].
  rewrite !inst_tin, !inst_tpair, !(instantiate_closed _ (enum_position n)) by apply closed_position.
  apply Hiff. exists n, name, D, D', (instantiate g1 xs), (instantiate g2 xs'); repeat apply conj;
    try assumption; apply cv_refl.
Qed.

Lemma cases_cons_inv : forall Gamma k IT X Q bs name D rs hs,
  elab_cases Gamma k IT X Q bs ((name, D) :: rs) hs ->
  exists h hs', hs = h :: hs' /\ elab_cases Gamma k IT X Q bs rs hs' /\
    ((exists p e t, In (name, (p, e)) bs /\ fresh_in Gamma p /\
        elab_check (extend Gamma p (TInterp IT D X)) e Q t /\ h = TLam p t) \/
     (exists d, ~ In name (clause_names bs) /\ dead Gamma IT D X d /\ h = dead_handler k Q d)).
Proof.
  intros Gamma k IT X Q bs name D rs hs H; inversion H; subst.
  - do 2 eexists; split; [reflexivity|split; [eassumption|left; do 3 eexists; repeat split; eassumption]].
  - do 2 eexists; split; [reflexivity|split; [eassumption|right; eexists; repeat split; eassumption]].
Qed.

Lemma case_es_case : forall G1 G2 g1 g2 e Q bs IT F G i x rs k hs IT' F' G' i' x' rs' k' hs',
  link G1 G2 g1 g2 -> close_input G1 IT F G i -> close_input G2 IT' F' G' i' ->
  elab_synth G2 e (CloseAt IT' F' G' i') x' -> SynthP G1 e (CloseAt IT F G i) x ->
  typing G1 Q (TSort k) -> typing G2 Q (TSort k') ->
  row_view G1 IT (TApp F i) rs -> row_view G2 IT' (TApp F' i') rs' -> NoDup (clause_names bs) ->
  elab_cases G1 k IT (carrier IT G) Q bs rs hs -> elab_cases G2 k' IT' (carrier IT' G') Q bs rs' hs' ->
  CasesP G1 k IT (carrier IT G) Q bs rs hs ->
  rty (instantiate g1 Q) (instantiate g2 Q) /\
  rel_at (instantiate g1 (case_term k IT F G i Q rs hs x)) (instantiate g2 (case_term k' IT' F' G' i' Q rs' hs' x'))
    (instantiate g1 Q) (instantiate g2 Q).
Proof.
  intros G1 G2 g1 g2 e Q bs IT F G i x rs k hs IT' F' G' i' x' rs' k' hs' Hl Hin Hin' Hs' IHs HQ1 HQ2 Hv Hv' HN
    Hcs Hcs' IHcs.
  pose proof Hl as [Hc1 [Hc2 _]].
  pose proof (closing2_refl_l _ _ _ Hc1) as Hc11. pose proof (closing2_refl_r _ _ _ Hc2) as Hc22.
  pose proof (closing2_refl_l _ _ _ Hc2) as Hc21. pose proof (closing2_refl_r _ _ _ Hc1) as Hc12.
  pose proof (TR_wf _ _ _ _ _ Hl (ex_intro _ k HQ1) (ex_intro _ k' HQ2)) as HTQ.
  destruct (IHs _ _ _ Hs' _ _ Hl) as [HRp Rx].
  destruct (IHs _ _ _ Hs' _ _ (link_diag_l _ _ _ _ Hl)) as [HRl _].
  destruct (IHs _ _ _ Hs' _ _ (link_diag_r _ _ _ _ Hl)) as [HRr _].
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc11 Hc22 Hin Hin' Hv Hv' HRp) as [Hnames [Hrow Hiff]].
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc11 Hc21 Hin Hin' Hv Hv' HRl) as [_ [Hrowl _]].
  destruct (close_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc12 Hc22 Hin Hin' Hv Hv' HRr) as [_ [Hrowr _]].
  assert (HTrows : forall m name D D', nth_error rs m = Some (name, D) -> nth_error rs' m = Some (name, D') ->
    TR g1 g2 (TInterp IT D (carrier IT G)) (TInterp IT' D' (carrier IT' G'))).
  { intros m name D D' H1 H2.
    exact (conj (proj2 (Hrow _ _ _ _ _ H1 H2)) (conj (proj2 (Hrowl _ _ _ _ _ H1 H2)) (proj2 (Hrowr _ _ _ _ _ H1 H2)))). }
  destruct (proj1 (Hiff _ _) Rx) as (m & name & D & D' & v1 & v2 & Hm & Hm' & Hv1 & Hv2 & Hx1 & Hx2 & Hvv).
  destruct (cases_handler_exists _ _ _ _ _ _ _ _ Hcs _ _ Hm) as [h Hh].
  destruct (cases_handler_exists _ _ _ _ _ _ _ _ Hcs' _ _ Hm') as [h' Hh'].
  pose proof (IHcs _ _ _ _ _ _ Hcs' HN Hnames g1 g2 Hl HQ1 HQ2 HTQ HTrows _ _ _ _ _ _ _ _ Hm Hm' Hh Hh' Hv1 Hv2 Hvv) as R.
  split; [exact (proj1 HTQ)|].
  eapply rel_at_conv; [exact R| | |apply cv_refl|apply cv_refl]; apply cv_sym; eapply case_term_conv; eassumption.
Qed.

Lemma lam_app_conv : forall Gamma g1 g2 p t v, closing2 Gamma g1 g2 -> fresh_in Gamma p -> closed v ->
  conv (TApp (instantiate g1 (TLam p t)) v) (instantiate ((p, v) :: g1) t).
Proof.
  intros Gamma g1 g2 p t v Hc Hp Hv. destruct (closing2_closed _ _ _ Hc) as [Hg _].
  destruct (closing2_away _ _ _ _ Hc Hp) as [Ha _].
  rewrite inst_lam, (drop_away g1 p) by assumption.
  eapply cv_trans; [apply beta_conv|]. apply cv_sym, inst_cons_conv; assumption.
Qed.

Theorem elab_coherence :
  (forall G1 e A1 t1, elab_synth G1 e A1 t1 -> SynthP G1 e A1 t1) /\
  (forall G1 e A1 t1, elab_check G1 e A1 t1 -> CheckP G1 e A1 t1) /\
  (forall G1 k IT X Q bs rs hs, elab_cases G1 k IT X Q bs rs hs -> CasesP G1 k IT X Q bs rs hs).
Proof.
  apply (elaboration_induction
    (fun G1 e A1 t1 _ => SynthP G1 e A1 t1)
    (fun G1 e A1 t1 _ => CheckP G1 e A1 t1)
    (fun G1 k IT X Q bs rs hs _ => CasesP G1 k IT X Q bs rs hs)).
  - (* es_var *) intros G1 n A1 Hwf Hl G2 A2 t2 H2 g1 g2 [Hc1 [Hc2 Hlk]].
    inversion H2; subst.
    match goal with Hl2 : lookup G2 n = Some A2 |- _ => pose proof (Hlk _ _ _ Hl Hl2) as HR end.
    split; [exact HR|].
    eapply rel_at_retype; [exact (closing2_lookup _ _ _ Hc1 _ _ Hl)|apply tyw_rty; exact (rty_tyw_l _ _ HR)|].
    eapply rty_trans; [apply rty_sym; exact (closing2_lookup_rty _ _ _ _ _ Hc1 Hl)|exact HR].
  - (* es_ann *) intros G1 e A1 t1 HA1 Hc IHc G2 A2 t2 H2 g1 g2 Hl.
    inversion H2; subst.
    match goal with HA2 : type_wf G2 A2, Hc2 : elab_check G2 e A2 t2 |- _ =>
      pose proof (TR_wf _ _ _ _ _ Hl HA1 HA2) as HT; split; [exact (proj1 HT)|exact (IHc _ _ _ Hc2 _ _ Hl HT)] end.
  - (* es_app *) intros G1 x f a A B t u HP Hf IHf Ha IHa G2 A2 t2 H2 g1 g2 Hl.
    inversion H2; subst. eapply case_es_app; eassumption.
  - (* es_signature *) intros G1 i IT rs Hi HIT Hrows G2 A2 t2 H2 g1 g2 [Hc1 _].
    inversion H2; subst.
    pose proof (synth_typed _ _ _ _ (es_signature Hi HIT Hrows)) as Ht.
    pose proof (rel_fundamental _ _ _ Ht _ _ Hc1) as HF.
    split; [eapply rel_at_rty; exact HF|exact HF].
  - (* es_close *) intros G1 IT Fx Gx f gg HIT HF IHF HG IHG G2 A2 t2 H2 g1 g2 Hl.
    pose proof Hl as [Hc1 [Hc2 _]].
    inversion H2; subst.
    match goal with HF2 : elab_check G2 Fx (Def IT) ?f2, HG2 : elab_check G2 Gx (Def IT) ?g2' |- _ =>
      rename HF2 into HF'; rename HG2 into HG' end.
    pose proof (check_typed _ _ _ _ HF) as HFt. pose proof (check_typed _ _ _ _ HF') as HFt'.
    pose proof (TR_wf _ _ _ _ _ Hl (type_wf_of_typing _ _ _ HFt) (type_wf_of_typing _ _ _ HFt')) as HTD.
    pose proof (IHF _ _ _ HF' _ _ Hl HTD) as RF. pose proof (IHG _ _ _ HG' _ _ Hl HTD) as RG.
    destruct (closing2_closed _ _ _ Hc1) as [Hg1 Hg2].
    destruct (inst_closed_typed _ _ _ _ _ Hc1 HIT) as [HI1 HI2].
    pose proof (rel_fundamental _ _ _ HIT _ _ Hc1) as RI. rewrite !instantiate_sort in RI.
    pose proof (inst_Family g1 Hg1 IT HI1) as Hconv1. pose proof (inst_Family g2 Hg2 IT HI2) as Hconv2.
    pose proof (inst_Def g1 Hg1 IT HI1) as HD1. pose proof (inst_Def g2 Hg2 IT HI2) as HD2.
    match goal with |- context [instantiate g2 (TClose IT ?f2 ?g2')] =>
      assert (R : rel_at (instantiate g1 (TClose IT f gg)) (instantiate g2 (TClose IT f2 g2'))
        (instantiate g1 (Family IT)) (instantiate g2 (Family IT))) end.
    { rewrite !inst_tclose. eapply rel_at_conv; [apply sem_close; [exact RI
        |eapply rel_at_conv; [exact RF|apply cv_refl|apply cv_refl|exact HD1|exact HD2]
        |eapply rel_at_conv; [exact RG|apply cv_refl|apply cv_refl|exact HD1|exact HD2]]
        |apply cv_refl|apply cv_refl|apply cv_sym, Hconv1|apply cv_sym, Hconv2]. }
    split; [eapply rel_at_rty; exact R|exact R].
  - (* es_case *) intros G1 e Q bs IT F G i x rs k hs Hin Hs IHs HQ Hv HN Hall Hcs IHcs G2 A2 t2 H2 g1 g2 Hl.
    inversion H2; subst. eapply case_es_case; eassumption.
  - (* ec_core *) intros G1 t A1 Ht. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 [Hc1 [Hc2 Hlk]] HT.
    destruct (nt_core_inv _ _ _ _ Hnt) as [-> Ht2].
    eapply rel_at_retype; [exact (rel_fundamental _ _ _ Ht _ _ Hc1)|apply tyw_rty; exact (rty_tyw_l _ _ (proj1 HT))|].
    exact (proj2 (proj2 HT)).
  - (* ec_conversion *) intros G1 e A B t Hs IHs HB HAB. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 Hl HT.
    pose proof Hl as [Hc1 [Hc2 _]].
    eapply case_via_synth; [exact Hl|exact HT| |eapply second_side; [exact Hc2|exact Hnt|exact (synth_synthesizable _ _ _ _ Hs)]].
    destruct (side_conv _ g1 _ _ _ _ (closing2_refl_l _ _ _ Hc1) Hs HB HAB) as [G [HG Ho]].
    exact (ex_intro _ A (ex_intro _ t (ex_intro _ G (conj IHs (conj HG Ho))))).
  - (* ec_target_conversion *) intros G1 e A B t Hc IHc HB HAB G2 A2 t2 H2 g1 g2 Hl HT.
    eapply rel_at_conv; [apply (IHc _ _ _ H2 _ _ Hl)|apply cv_refl|apply cv_refl|apply instantiate_conversion, HAB|apply cv_refl].
    eapply TR_conv; [exact HT|apply cv_sym, HAB|apply cv_refl].
  - (* ec_subsumption *) intros G1 e A B t c Hs IHs Hsub. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 Hl HT.
    pose proof Hl as [Hc1 [Hc2 _]].
    eapply case_via_synth; [exact Hl|exact HT| |eapply second_side; [exact Hc2|exact Hnt|exact (synth_synthesizable _ _ _ _ Hs)]].
    destruct (side_sub _ g1 _ _ _ _ _ (closing2_refl_l _ _ _ Hc1) Hs Hsub) as [G [HG Ho]].
    exact (ex_intro _ A (ex_intro _ t (ex_intro _ G (conj IHs (conj HG Ho))))).
  - (* ec_lam *) intros G1 x e A B t Hx HP Hc IHc. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 Hl HT.
    destruct (nt_lam_inv _ _ _ _ _ Hnt) as (A' & B' & t' & -> & -> & Hx' & HP' & Hc').
    eapply case_ec_lam; eassumption.
  - (* ec_pair *) intros G1 x e f A B t u HS He IHe Hf IHf. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 Hl HT.
    destruct (nt_pair_inv _ _ _ _ _ Hnt) as (x' & A' & B' & t' & u' & -> & -> & HS' & He' & Hf').
    eapply case_ec_pair; eassumption.
  - (* ec_constructor *) intros G1 name e IT F G i rs n D xs Hin Hv Hn He IHe. apply CheckP_of_nt. intros G2 A0 t2 Hnt g1 g2 Hl HT.
    destruct (nt_constructor_inv _ _ _ _ _ Hnt) as (IT' & F' & G' & i' & rs' & n' & D' & xs' & -> & -> & Hin' & Hv' & Hn' & He').
    eapply case_ec_constructor; eassumption.
  - (* cases_nil *) intros G1 k IT X Q bs G2 k' IT' X' rs' hs' H2 HN Hnames g1 g2 Hl HQ1 HQ2 HTQ HTrows m name D D' h h' v1 v2 Hm.
    destruct m; discriminate.
  - (* cases_live *) intros G1 k IT X Q bs name D rs p e t hs Hin Hp Hc IHc Hcs IHcs.
    intros G2 k' IT' X' rs' hs' H2 HN Hnames g1 g2 Hl HQ1 HQ2 HTQ HTrows m name0 D0 D0' h h' v1 v2 Hm Hm' Hh Hh' Hv1 Hv2 Hvv.
    destruct rs' as [|[name' D'] rs'']; [discriminate Hnames|].
    cbn in Hnames. injection Hnames as Hn0 Hnames'. subst name'.
    destruct (cases_cons_inv _ _ _ _ _ _ _ _ _ _ H2) as (h0 & hs'' & -> & Hcs' & Hhead).
    pose proof Hl as [Hc1 [Hc2 _]].
    destruct m as [|m].
    + cbn in Hm, Hm', Hh, Hh'. injection Hm as E1 E2; subst name0 D0. injection Hm' as E3; subst D0'.
      injection Hh as E4; subst h. injection Hh' as E5; subst h'.
      destruct Hhead as [(p' & e' & t' & Hin' & Hp' & Hc' & ->)|(d & Hnot & Hd & ->)].
      * pose proof (nodup_fst_unique bs name (p, e) (p', e') HN Hin Hin') as Epe. injection Epe as E6 E7; subst p' e'.
        pose proof (typing_context _ _ _ (check_typed _ _ _ _ Hc)) as Hw1.
        pose proof (typing_context _ _ _ (check_typed _ _ _ _ Hc')) as Hw2.
        pose proof (link_extend _ _ _ _ _ _ _ _ _ Hl Hp Hp' Hw1 Hw2 (HTrows 0 name D D' eq_refl eq_refl) Hv1 Hv2 Hvv) as Hlext.
        pose proof (typing_fresh_not_free _ _ _ _ HQ1 Hp) as Hq1.
        assert (HText : TR ((p, v1) :: g1) ((p, v2) :: g2) Q Q) by (unfold TR; rewrite (inst_cons_fresh g1 p v1 Q), (inst_cons_fresh g2 p v2 Q) by exact Hq1; exact HTQ).
        pose proof (IHc _ _ _ Hc' _ _ Hlext HText) as R.
        rewrite (inst_cons_fresh g1 p v1 Q), (inst_cons_fresh g2 p v2 Q) in R by exact Hq1.
        eapply rel_at_conv; [exact R| | |apply cv_refl|apply cv_refl].
        -- apply cv_sym. eapply lam_app_conv; [exact Hc1|exact Hp|exact Hv1].
        -- apply cv_sym. eapply lam_app_conv; [exact (closing2_sym _ _ _ Hc2)|exact Hp'|exact Hv2].
      * exfalso. apply Hnot. unfold clause_names. apply in_map_iff. exists (name, (p, e)); split; [reflexivity|exact Hin].
    + cbn in Hm, Hm', Hh, Hh'.
    eapply (IHcs _ _ _ _ _ _ Hcs' HN Hnames' g1 g2 Hl HQ1 HQ2 HTQ); [|exact Hm|exact Hm'|exact Hh|exact Hh'|exact Hv1|exact Hv2|exact Hvv].
    intros m0 n0 D1 D1' H1 H1'. exact (HTrows (S m0) n0 D1 D1' H1 H1').
  - (* cases_dead *) intros G1 k IT X Q bs name D rs d hs Hnot Hd Hcs IHcs.
    intros G2 k' IT' X' rs' hs' H2 HN Hnames g1 g2 Hl HQ1 HQ2 HTQ HTrows m name0 D0 D0' h h' v1 v2 Hm Hm' Hh Hh' Hv1 Hv2 Hvv.
    destruct rs' as [|[name' D'] rs'']; [discriminate Hnames|].
    cbn in Hnames. injection Hnames as Hn0 Hnames'. subst name'.
    destruct (cases_cons_inv _ _ _ _ _ _ _ _ _ _ H2) as (h0 & hs'' & -> & Hcs' & Hhead).
    pose proof Hl as [Hc1 [Hc2 _]].
    destruct m as [|m].
    + cbn in Hm. injection Hm as E1 E2; subst name0 D0. exfalso.
      exact (dead_empty _ _ _ _ _ _ Hd (closing2_refl_l _ _ _ Hc1) v1 v1 Hv1 (rel_at_left_of _ _ _ _ Hvv)).
    + cbn in Hm, Hm', Hh, Hh'.
    eapply (IHcs _ _ _ _ _ _ Hcs' HN Hnames' g1 g2 Hl HQ1 HQ2 HTQ); [|exact Hm|exact Hm'|exact Hh|exact Hh'|exact Hv1|exact Hv2|exact Hvv].
    intros m0 n0 D1 D1' H1 H1'. exact (HTrows (S m0) n0 D1 D1' H1 H1').
Qed.

Theorem checking_coherence_rel : forall Gamma e A t u,
  elab_check Gamma e A t -> elab_check Gamma e A u -> observational_eq Gamma A t u.
Proof.
  intros Gamma e A t u Ht Hu.
  pose proof (check_typed _ _ _ _ Ht) as Htt. pose proof (check_typed _ _ _ _ Hu) as Hut.
  apply rel_observational; [exact Htt|exact Hut|]. intros g1 g2 Hc.
  pose proof (link_same _ _ _ Hc) as Hl.
  pose proof (type_wf_of_typing _ _ _ Htt) as HA.
  exact (proj1 (proj2 elab_coherence) _ _ _ _ Ht _ _ _ Hu _ _ Hl (TR_wf _ _ _ _ _ Hl HA HA)).
Qed.

Print Assumptions checking_coherence_rel.
