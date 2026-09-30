(* The concrete cumulative universe model. Description types start at level
   one; their parameter and all description payload domains remain small. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBSmallTypeModel.
Import ListNotations Full.

Lemma small_atom_not_description : forall I R, ~ small_atom (TIDesc I) R.
Proof. intros I R H; inversion H. Qed.

Inductive primitive_at (level : nat) : term -> (term -> Prop) -> Prop :=
| primitive_small : forall A R, small_atom A R -> primitive_at level A R
| primitive_description : forall IT RI,
    1 <= level -> type_interp small_atom IT RI ->
    primitive_at level (TIDesc IT) (description_computable small_atom RI).

Lemma primitive_candidate : forall level A R, primitive_at level A R -> candidate R.
Proof. intros level A R H; destruct H; [now apply small_atom_candidate with A|apply description_computable_candidate]. Qed.
Lemma primitive_not_neutral : forall level A R, primitive_at level A R -> ~ neutral A.
Proof. intros level A R H; destruct H; [eapply small_atom_not_neutral; eassumption|cbn [neutral]; tauto]. Qed.
Lemma primitive_not_pi : forall level A B R, ~ primitive_at level (TPi A B) R.
Proof. intros level A B R H; inversion H; subst; eapply small_atom_not_pi; eassumption. Qed.
Lemma primitive_not_sigma : forall level A B R, ~ primitive_at level (TSigma A B) R.
Proof. intros level A B R H; inversion H; subst; eapply small_atom_not_sigma; eassumption. Qed.
Lemma primitive_not_sort : forall level k R, ~ primitive_at level (TSort k) R.
Proof. intros level k R H; inversion H; subst; eapply small_atom_not_sort; eassumption. Qed.
Lemma primitive_unique : forall level A R S,
  primitive_at level A R -> primitive_at level A S -> predicate_equiv R S.
Proof.
  intros level A R S H; destruct H; intro HS; inversion HS; subst.
  - eapply small_atom_unique; eassumption.
  - exfalso; eapply small_atom_not_description; eassumption.
  - exfalso; eapply small_atom_not_description; eassumption.
  - apply description_computable_equiv.
    eapply type_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
      |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
      |eassumption|eassumption|apply cv_refl].
Qed.
Lemma primitive_cumulative : forall n m, n <= m -> forall A R,
  primitive_at n A R -> primitive_at m A R.
Proof. intros n m Hnm A R H; destruct H; [now apply primitive_small|apply primitive_description; [lia|assumption]]. Qed.

Definition calculus_type := universe_model primitive_at.
Definition calculus_interp := universe_interp primitive_at.
Definition calculus_elements := universe_elements primitive_at.

Ltac solve_primitive_model :=
  solve [exact primitive_candidate|exact primitive_not_neutral|exact primitive_not_pi
    |exact primitive_not_sigma|exact primitive_not_sort|exact primitive_unique|exact primitive_cumulative].

Theorem calculus_type_candidate : forall n, candidate (calculus_type n).
Proof. intros n; apply universe_model_candidate. Qed.
Theorem calculus_interp_candidate : forall n A R, calculus_interp n A R -> candidate R.
Proof. intros; eapply universe_interp_candidate; try solve_primitive_model; eassumption. Qed.
Theorem calculus_interp_unique : forall n m A B R S,
  calculus_interp n A R -> calculus_interp m B S -> conv A B -> predicate_equiv R S.
Proof. intros; eapply universe_interp_unique; try solve_primitive_model; eassumption. Qed.
Theorem calculus_interp_cumulative : forall n m, n <= m -> forall A R,
  calculus_interp n A R -> calculus_interp m A R.
Proof. intros; eapply universe_interp_cumulative; try solve_primitive_model; eassumption. Qed.
Theorem calculus_type_cumulative : forall n m, n <= m -> forall A,
  calculus_type n A -> calculus_type m A.
Proof. intros; eapply universe_model_cumulative; try solve_primitive_model; eassumption. Qed.
Theorem calculus_interp_canonical : forall n A,
  calculus_type n A -> calculus_interp n A (calculus_elements n A).
Proof. intros; eapply universe_interp_canonical; try solve_primitive_model; eassumption. Qed.
Theorem calculus_sort_interp : forall k n, k < n ->
  calculus_interp n (TSort k) (calculus_type k).
Proof. intros; apply universe_sort_interpretation; assumption. Qed.
Theorem calculus_pi_formation : forall j k A B,
  calculus_type j A -> (forall a, calculus_elements j A a -> calculus_type k (subst a 0 B)) ->
  calculus_type (Nat.max j k) (TPi A B).
Proof. intros; eapply universe_pi_formation; try solve_primitive_model; eassumption. Qed.
Theorem calculus_sigma_formation : forall j k A B,
  calculus_type j A -> (forall a, calculus_elements j A a -> calculus_type k (subst a 0 B)) ->
  calculus_type (Nat.max j k) (TSigma A B).
Proof. intros; eapply universe_sigma_formation; try solve_primitive_model; eassumption. Qed.

Theorem small_type_in_universe : forall A R,
  type_interp small_atom A R -> forall n, calculus_interp n A R.
Proof.
  intros A R H n; eapply type_interp_monotone; [|exact H].
  intros T P HP; apply la_base, primitive_small; exact HP.
Qed.
Theorem universe_zero_small_type : forall A R,
  calculus_interp 0 A R -> type_interp small_atom A R.
Proof.
  intros A R H; eapply type_interp_monotone; [|exact H].
  intros T P HP; inversion HP; subst.
  - match goal with HB : primitive_at 0 _ _ |- _ => inversion HB; subst end; [assumption|lia].
  - destruct k; discriminate.
Qed.
Lemma full_SN_description_type : forall IT, full_SN IT -> full_SN (TIDesc IT).
Proof. apply full_SN_unary; description_components. Qed.
Lemma description_type_normal : forall IT, normal_form IT -> normal_form (TIDesc IT).
Proof. intros IT H u HU; inversion HU; subst; [discriminate|eapply H; eassumption]. Qed.
Theorem calculus_description_formation : forall IT RI,
  type_interp small_atom IT RI -> forall n, 1 <= n ->
  calculus_interp n (TIDesc IT) (description_computable small_atom RI).
Proof.
  intros IT RI HI n Hn.
  pose proof (type_interp_normalizing _ _ _ HI) as HSI.
  destruct (normalize_full _ HSI) as [I' [HR HN]].
  eapply it_atom with (n:=TIDesc I').
  - now apply full_SN_description_type.
  - now apply red_star_TIDesc.
  - now apply description_type_normal.
  - apply la_base, primitive_description; [exact Hn|].
    eapply type_interp_reductions; eassumption.
Qed.
Theorem calculus_small_atom_normal : forall A R,
  small_atom A R -> normal_form A -> forall n, calculus_interp n A R.
Proof.
  intros A R HA HN n; eapply it_atom with (n:=A).
  - now apply normal_form_accessible.
  - constructor.
  - exact HN.
  - now apply la_base, primitive_small.
Qed.
Theorem calculus_unit_type : forall n, calculus_interp n TUnitT full_SN.
Proof. apply calculus_small_atom_normal; [constructor|intros u H; inversion H; discriminate]. Qed.
Theorem calculus_uid_type : forall n, calculus_interp n TUId full_SN.
Proof. apply calculus_small_atom_normal; [constructor|intros u H; inversion H; discriminate]. Qed.
Theorem calculus_enum_universe : forall n, calculus_interp n TEnumU enumeration_computable.
Proof. apply calculus_small_atom_normal; [constructor|intros u H; inversion H; discriminate]. Qed.
Theorem calculus_enum_type : forall E, full_SN E -> forall n,
  calculus_interp n (TEnumT E) (enum_elements E).
Proof.
  intros E HE n; destruct (normalize_full _ HE) as [E' [HR HN]].
  eapply it_equiv with (R:=enum_elements E').
  - eapply it_atom with (n:=TEnumT E').
    + eapply full_SN_unary; [description_components|exact HE].
    + now apply red_star_TEnumT.
    + intros u HU; inversion HU; subst; [discriminate|eapply HN; eassumption].
    + apply la_base, primitive_small, sa_enum.
  - apply enum_elements_conversion, cv_sym, reductions_conversion; exact HR.
Qed.

Lemma full_SN_rigid_application : forall f, full_SN f -> forall a,
  full_SN a -> forall h, term_head f = Some h -> full_SN (TApp f a).
Proof.
  intros f HF; induction HF as [f HF IHf]; intros a HA h HH.
  induction HA as [a HA IHa]; constructor; intros u HU; inversion HU; subst.
  - destruct f; cbn [root_step term_head] in *; discriminate.
  - eapply IHf; [eassumption|constructor; exact HA|eapply reduction_head; eassumption].
  - now apply IHa.
Qed.
Lemma normal_form_rigid_application : forall f a h,
  normal_form f -> normal_form a -> term_head f = Some h -> normal_form (TApp f a).
Proof.
  intros f a h HF HA HH u HU; inversion HU; subst.
  - destruct f; cbn [root_step term_head] in *; discriminate.
  - eapply HF; eassumption.
  - eapply HA; eassumption.
Qed.
Lemma full_SN_mui : forall IT D, full_SN IT -> full_SN D -> full_SN (TMuI IT D).
Proof. apply full_SN_binary; description_components. Qed.
Lemma mui_normal : forall IT D, normal_form IT -> normal_form D -> normal_form (TMuI IT D).
Proof. apply normal_form_binary; description_components. Qed.
Lemma full_SN_close : forall IT F G,
  full_SN IT -> full_SN F -> full_SN G -> full_SN (TClose IT F G).
Proof.
  intros IT F G HI; revert F G.
  induction HI as [IT HI IHi]; intros F G HF HG.
  revert G HG; induction HF as [F HF IHf]; intros G HG.
  induction HG as [G HG IHg].
  constructor; intros u HU; inversion HU; subst; [discriminate| | |].
  - apply IHi; [eassumption|constructor; exact HF|constructor; exact HG].
  - apply IHf; [eassumption|constructor; exact HG].
  - apply IHg; eassumption.
Qed.
Lemma close_normal : forall IT F G,
  normal_form IT -> normal_form F -> normal_form G -> normal_form (TClose IT F G).
Proof. intros IT F G HI HF HG u HU; inversion HU; subst; [discriminate|eapply HI|eapply HF|eapply HG]; eassumption. Qed.

Theorem calculus_mu_type : forall IT D i RI F,
  type_interp small_atom IT RI -> full_SN D -> RI i ->
  (forall j, RI j -> description_interp small_atom RI (TApp D j) (F j)) ->
  forall n, calculus_interp n (TApp (TMuI IT D) i) (description_fixed_point RI F i).
Proof.
  intros IT D i RI F HI HD Hi HF n.
  pose proof (type_interp_normalizing _ _ _ HI) as HSI.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (candidate_normalizing CRI Hi) as HSi.
  destruct (normalize_full _ HSI) as [IT' [RIT NIT]].
  destruct (normalize_full _ HD) as [D' [RD ND]].
  destruct (normalize_full _ HSi) as [i' [Ri Ni]].
  assert (Hi' : RI i') by (eapply candidate_reducts; eassumption).
  eapply it_equiv with (R:=description_fixed_point RI F i').
  - eapply it_atom with (n:=TApp (TMuI IT' D') i').
    + eapply full_SN_rigid_application; [now apply full_SN_mui|exact HSi|reflexivity].
    + apply red_star_TApp; [now apply red_star_TMuI|exact Ri].
    + eapply normal_form_rigid_application; [now apply mui_normal|exact Ni|reflexivity].
    + apply la_base, primitive_small, small_mu_atom.
      * eapply type_interp_reductions; eassumption.
      * exact Hi'.
      * intros j Hj; eapply description_interp_reductions; [exact (HF j Hj)|].
        apply red_star_TApp; [exact RD|constructor].
  - eapply small_fixed_point_index_equiv; [exact HF|exact Hi'|exact Hi|].
    apply cv_sym, reductions_conversion; exact Ri.
Qed.
Theorem calculus_close_type : forall IT D G i RI FD FG,
  type_interp small_atom IT RI -> full_SN D -> full_SN G -> RI i ->
  description_interp small_atom RI (TApp D i) FD ->
  (forall j, RI j -> description_interp small_atom RI (TApp G j) (FG j)) ->
  forall n, calculus_interp n (TApp (TClose IT D G) i)
    (rolled_elements (FD (description_fixed_point RI FG))).
Proof.
  intros IT D G i RI FD FG HI HD HG Hi HFD HFG n.
  pose proof (type_interp_normalizing _ _ _ HI) as HSI.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (candidate_normalizing CRI Hi) as HSi.
  destruct (normalize_full _ HSI) as [IT' [RIT NIT]].
  destruct (normalize_full _ HD) as [D' [RD ND]].
  destruct (normalize_full _ HG) as [G' [RG NG]].
  destruct (normalize_full _ HSi) as [i' [Ri Ni]].
  assert (Hi' : RI i') by (eapply candidate_reducts; eassumption).
  eapply it_atom with (n:=TApp (TClose IT' D' G') i').
  - eapply full_SN_rigid_application; [now apply full_SN_close|exact HSi|reflexivity].
  - apply red_star_TApp; [now apply red_star_TClose|exact Ri].
  - eapply normal_form_rigid_application; [now apply close_normal|exact Ni|reflexivity].
  - apply la_base, primitive_small, small_close_atom.
    + eapply type_interp_reductions; eassumption.
    + exact Hi'.
    + eapply description_interp_reductions; [exact HFD|now apply red_star_TApp].
    + intros j Hj; eapply description_interp_reductions; [exact (HFG j Hj)|].
      apply red_star_TApp; [exact RG|constructor].
Qed.

Print Assumptions calculus_interp_unique.
Print Assumptions calculus_pi_formation.
Print Assumptions calculus_description_formation.
Print Assumptions calculus_enum_type.
Print Assumptions calculus_mu_type.
Print Assumptions calculus_close_type.
