(* Computability of close induction. The fixed-point refinement handles the
   recursive diagonal; outer signatures are eliminated one rolled layer. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDataComputability.
Import ListNotations Full.

Definition close_ind_plug p x := match p with
  TCloseInd IT G P st D j _ => TCloseInd IT G P st D j x | _ => TVar 0 end.
Definition close_ind_result_type p x := match p with
  TCloseInd IT G P st D j _ => TApp (TApp (TApp P D) j) x | _ => TUnitT end.
Definition close_ind_result p x := type_elements small_atom (close_ind_result_type p x).

Section CloseIndComputability.
Variable RI : term -> Prop.
Hypothesis index_candidate : candidate RI.
Variable base_definition : term.
Variable F : term -> description_functor.
Hypothesis base_meaning : forall j, RI j -> small_description RI (TApp base_definition j) (F j).
Let Mu := description_fixed_point RI F.
Let mu_candidates := small_fixed_point_candidate RI base_definition F base_meaning.
Let mu_stable := ind_mu_stable RI base_definition F base_meaning.
Let functor_monotone := ind_functor_monotone RI base_definition F base_meaning.
Let functor_index_equiv := ind_functor_index_equiv RI base_definition F base_meaning.
Let mu_fold := ind_mu_fold RI base_definition F base_meaning.
Definition close_elements D j := rolled_elements (definition_meaning RI D j Mu).
Lemma close_elements_candidate : forall D, computable_definition RI D -> forall j,
  RI j -> candidate (close_elements D j).
Proof.
  intros D HD j Hj; apply rolled_elements_candidate.
  exact (small_description_candidate _ _ _
    (computable_definition_meaning RI index_candidate D HD j Hj) Mu mu_candidates).
Qed.
Lemma diagonal_definition_computable : forall D,
  full_SN D -> ind_definition RI F D -> computable_definition RI D.
Proof. intros D HS HD; split; [exact HS|intros j Hj; exact (proj1 (HD j Hj))]. Qed.
Lemma diagonal_definition_meaning : forall D,
  full_SN D -> ind_definition RI F D -> forall j, RI j ->
  functor_equiv (definition_meaning RI D j) (F j).
Proof.
  intros D HS HD j Hj; eapply small_description_unique;
    [apply computable_definition_meaning; [exact index_candidate|now apply diagonal_definition_computable|exact Hj]
    |exact (proj2 (HD j Hj))|apply cv_refl].
Qed.
Lemma diagonal_elements : forall D,
  full_SN D -> ind_definition RI F D -> forall j, RI j ->
  predicate_equiv (close_elements D j) (Mu j).
Proof.
  intros D HS HD j Hj t.
  pose proof (rolled_elements_equiv _ _ (diagonal_definition_meaning D HS HD j Hj Mu) t) as HE.
  pose proof (small_fixed_point_rolled_equiv RI base_definition F base_meaning j Hj t) as HM.
  unfold close_elements in *; tauto.
Qed.
Definition close_motive_computable P := forall D,
  computable_definition RI D -> forall j x, RI j -> close_elements D j x ->
  reducible_type small_atom (TApp (TApp (TApp P D) j) x).
Lemma close_motive_reductions : forall P, close_motive_computable P -> forall P',
  rtc reduction P P' -> close_motive_computable P'.
Proof.
  intros P HP P' HR D HD j x Hj Hx; destruct (HP D HD j x Hj Hx) as [R HT]; exists R.
  eapply type_interp_reductions; [exact HT|].
  apply red_star_TApp; [apply red_star_TApp; [apply red_star_TApp; [exact HR|constructor]|constructor]|constructor].
Qed.
Lemma diagonal_motive_computable : forall G P,
  full_SN G -> ind_definition RI F G -> close_motive_computable P ->
  full_SN (diagonal_motive G P) /\ hypothesis_family RI Mu (diagonal_motive G P).
Proof.
  intros G P HG HD HP.
  assert (CS : stable_family RI Mu).
  { intros i j Hi HR; apply (proj2 mu_stable i j);
      [exact Hi|exact (candidate_reduct index_candidate Hi HR)|now apply reductions_conversion, rtc_one]. }
  pose proof (dependent_pair_candidate RI Mu index_candidate mu_candidates CS) as CP.
  assert (HC : dependent_function (dependent_pair RI Mu) (fun _ => reducible_type small_atom)
    (diagonal_motive G P)).
  { apply dependent_lambda_computable; [exact CP|intros; apply reducible_type_candidate
      |intros a b Ha HR t; tauto|].
    intros t [_ [Hi Hx]]; cbn [subst]; rewrite ?subst_lift_zero, ?lift_zero_id.
    apply HP; [now apply diagonal_definition_computable|exact Hi|].
    apply (diagonal_elements G HG HD _ Hi); exact Hx. }
  split; [exact (proj1 HC)|].
  intros j x Hj Hx; apply (proj2 HC).
  exact (dependent_pair_computable RI Mu index_candidate mu_candidates CS j x Hj Hx).
Qed.
Definition close_step_computable IT G P st := forall D,
  computable_definition RI D -> forall j xs h,
  RI j -> definition_meaning RI D j Mu xs ->
  small_value h (TIAll IT (TApp D j) (carrier IT G) xs (diagonal_motive G P)) ->
  small_value (TApp (TApp (TApp (TApp st D) j) xs) h) (TApp (TApp (TApp P D) j) (TIn xs)).
Lemma close_all_type : forall IT G P D j xs,
  full_SN IT -> full_SN G -> ind_definition RI F G -> close_motive_computable P ->
  computable_definition RI D -> RI j -> definition_meaning RI D j Mu xs ->
  reducible_type small_atom (TIAll IT (TApp D j) (carrier IT G) xs (diagonal_motive G P)).
Proof.
  intros IT G P D j xs HI HG HGdef HP HD Hj Hxs.
  destruct (diagonal_motive_computable G P HG HGdef HP) as [HS HF].
  eapply all_computable; [exact index_candidate|exact (proj2 HD j Hj)
    |exact (computable_definition_meaning RI index_candidate D HD j Hj)|exact HI
    |unfold carrier; now apply full_SN_close|exact HS|exact mu_stable|exact HF|exact Hxs].
Qed.
Lemma diagonal_motive_reductions : forall G G' P P',
  rtc reduction G G' -> rtc reduction P P' ->
  rtc reduction (diagonal_motive G P) (diagonal_motive G' P').
Proof.
  intros G G' P P' RG RP; unfold diagonal_motive.
  apply red_star_TLam.
  apply red_star_TApp; [|apply rtc_refl].
  apply red_star_TApp; [|apply rtc_refl].
  apply red_star_TApp; eapply (@rtc_map_rel term term reduction reduction (lift 1 0));
    [intros; now apply reduction_lift|exact RP|intros; now apply reduction_lift|exact RG].
Qed.
Lemma close_step_reductions : forall IT G P st,
  full_SN IT -> full_SN G -> ind_definition RI F G -> close_motive_computable P ->
  close_step_computable IT G P st -> forall IT' G' P' st',
  rtc reduction IT IT' -> rtc reduction G G' -> rtc reduction P P' -> rtc reduction st st' ->
  close_step_computable IT' G' P' st'.
Proof.
  intros IT G P st HI HG HGdef HP HM IT' G' P' st' RIT RG RP RS D HD j xs h Hj Hxs Hh.
  assert (Hh0 : small_value h (TIAll IT (TApp D j) (carrier IT G) xs (diagonal_motive G P))).
  { eapply small_value_conversion; [exact Hh|eapply close_all_type; eassumption|].
    apply cv_sym, reductions_conversion, red_star_TIAll;
      [exact RIT|constructor|unfold carrier; now apply red_star_TClose|constructor|now apply diagonal_motive_reductions]. }
  eapply small_value_type_reductions.
  - eapply small_value_reductions; [exact (HM D HD j xs h Hj Hxs Hh0)|].
    apply red_star_TApp; [apply red_star_TApp; [apply red_star_TApp; [apply red_star_TApp;
      [exact RS|constructor]|constructor]|constructor]|constructor].
  - apply red_star_TApp; [apply red_star_TApp; [apply red_star_TApp; [exact RP|constructor]|constructor]|constructor].
Qed.
Definition close_ind_valid i p := exists IT G P st D j,
  p = TCloseInd IT G P st D j (TVar 0) /\ Forall full_SN [IT;G;P;st;D] /\
  RI j /\ conv i j /\ ind_definition RI F G /\ ind_definition RI F D /\
  close_motive_computable P /\ close_step_computable IT G P st.
Lemma close_ind_valid_components_reductions : forall i IT G P st D j,
  close_ind_valid i (TCloseInd IT G P st D j (TVar 0)) -> forall IT' G' P' st' D' j',
  rtc reduction IT IT' -> rtc reduction G G' -> rtc reduction P P' ->
  rtc reduction st st' -> rtc reduction D D' -> rtc reduction j j' ->
  close_ind_valid i (TCloseInd IT' G' P' st' D' j' (TVar 0)).
Proof.
  intros i IT G P st D j (IT0 & G0 & P0 & st0 & D0 & j0 & HE & HS & Hj & HC & HG & HD & HP & HM).
  inversion HE; subst; ind_unpack_sns.
  intros IT' G' P' st' D' j' RIT RG RP RS RD Rj.
  exists IT',G',P',st',D',j'; split; [reflexivity|]; split.
  - repeat (apply Forall_cons; [solve [match goal with
      HR : rtc reduction ?t ?u, HS : full_SN ?t |- full_SN ?u => exact (full_SN_reductions _ HS _ HR) end]|]); constructor.
  - split; [exact (candidate_reducts _ index_candidate _ _ Rj Hj)|].
    split; [eapply cv_trans; [exact HC|exact (reductions_conversion _ _ Rj)]|].
    split; [exact (ind_definition_reductions RI F G0 HG G' RG)|].
    split; [exact (ind_definition_reductions RI F D0 HD D' RD)|].
    split; [eapply close_motive_reductions; eassumption|].
    eapply close_step_reductions with (IT:=IT0) (G:=G0) (P:=P0) (st:=st0); eassumption.
Qed.
Lemma close_ind_valid_reduct : forall i p q, close_ind_valid i p -> reduction p q -> close_ind_valid i q.
Proof.
  intros i p q HV HR; destruct HV as (IT & G & P & st & D & j & -> & HS).
  assert (HV : close_ind_valid i (TCloseInd IT G P st D j (TVar 0))) by (exists IT,G,P,st,D,j; auto).
  inversion HR; subst; try discriminate.
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: eapply close_ind_valid_components_reductions; [exact HV| | | | | |]; solve [constructor|now apply rtc_one].
Qed.
Lemma close_ind_valid_index : forall i j, conv i j -> forall p, close_ind_valid i p <-> close_ind_valid j p.
Proof.
  intros i j HC p; split; intros (IT & G & P & st & D & z & HE & HS & Hz & HCz & HG & HD & HP & HM);
    exists IT,G,P,st,D,z;
    refine (conj HE (conj HS (conj Hz (conj _ (conj HG (conj HD (conj HP HM))))))).
  - eapply cv_trans; [apply cv_sym; exact HC|exact HCz].
  - eapply cv_trans; [exact HC|exact HCz].
Qed.
Lemma close_ind_result_interpreted : forall i p x,
  RI i -> close_ind_valid i p -> Mu i x ->
  small_interp (close_ind_result_type p x) (close_ind_result p x).
Proof.
  intros i p x Hi (IT & G & P & st & D & j & -> & HS & Hj & HC & HG & HD & HP & HM) Hx.
  ind_unpack_sns; apply small_type_canonical, HP; [now apply diagonal_definition_computable|exact Hj|].
  apply (diagonal_elements D ltac:(assumption) HD j Hj).
  apply (proj2 mu_stable i j); [exact Hi|exact Hj|exact HC|exact Hx].
Qed.
Lemma close_ind_result_candidate : forall i, RI i -> forall p,
  close_ind_valid i p -> forall x, Mu i x -> candidate (close_ind_result p x).
Proof. intros; eapply small_type_candidate, close_ind_result_interpreted; eassumption. Qed.
Lemma close_ind_result_stable : forall i, RI i -> forall p,
  close_ind_valid i p -> stable_family (Mu i) (close_ind_result p).
Proof.
  intros i Hi p Hp x y Hx HR.
  pose proof (candidate_reduct (mu_candidates i Hi) Hx HR) as Hy.
  eapply small_interp_unique;
    [exact (close_ind_result_interpreted i p x Hi Hp Hx)|exact (close_ind_result_interpreted i p y Hi Hp Hy)|].
  destruct Hp as (IT & G & P & st & D & j & -> & HS); cbn [close_ind_result_type].
  apply reductions_conversion, red_star_TApp; [constructor|now apply rtc_one].
Qed.
Lemma close_ind_parameter_type_reduction : forall i p q,
  close_ind_valid i p -> reduction p q -> forall x,
  rtc reduction (close_ind_result_type p x) (close_ind_result_type q x).
Proof.
  intros i p q (IT & G & P & st & D & j & -> & HS) HR x.
  inversion HR; subst; try discriminate.
  all: cbn [close_ind_result_type].
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: repeat first [apply rtc_refl | apply red_star_TApp | apply rtc_one; assumption].
Qed.
Lemma close_ind_parameter_stable : forall i, RI i -> forall p q,
  close_ind_valid i p -> reduction p q -> forall x, Mu i x ->
  predicate_equiv (close_ind_result p x) (close_ind_result q x).
Proof.
  intros i Hi p q Hp HR x Hx; eapply small_interp_unique;
    [exact (close_ind_result_interpreted i p x Hi Hp Hx)
    |exact (close_ind_result_interpreted i q x Hi (close_ind_valid_reduct i p q Hp HR) Hx)|].
  apply reductions_conversion; eapply close_ind_parameter_type_reduction; eassumption.
Qed.
Lemma close_ind_parameter_normalizing : forall i p, close_ind_valid i p -> full_SN p.
Proof.
  intros i p (IT & G & P & st & D & j & -> & HS & Hj & Hrest).
  ind_unpack_sns; apply normalization_by_head_expansion.
  - cbn [term_children].
    repeat (apply Forall_cons; [solve [assumption | exact (candidate_normalizing index_candidate Hj)
      |exact (candidate_variable _ normalizing_candidate 0)]|]); constructor.
  - intros t v HT HV; inversion HT; subst.
    match goal with H : rtc reduction (TVar 0) ?x |- _ =>
      assert (HE : TVar 0 = x) by (apply normal_reductions_identity;
        [intros y HY; inversion HY; discriminate|exact H]); subst x end.
    inversion HV; subst; discriminate.
Qed.
Lemma close_ind_argument_reduction : forall i p, close_ind_valid i p -> forall x y,
  reduction x y -> reduction (close_ind_plug p x) (close_ind_plug p y).
Proof. intros i p (IT & G & P & st & D & j & -> & HS) x y H; cbn [close_ind_plug]; now apply red_TCloseInd_x. Qed.
Lemma close_ind_plug_neutral : forall i p, close_ind_valid i p -> forall x, neutral (close_ind_plug p x).
Proof. intros i p (IT & G & P & st & D & j & -> & HS) x; exact I. Qed.
Lemma close_ind_neutral_step : forall i p, close_ind_valid i p -> forall x u,
  neutral x -> reduction (close_ind_plug p x) u ->
  (exists q, reduction p q /\ u = close_ind_plug q x) \/
  (exists y, reduction x y /\ u = close_ind_plug p y).
Proof.
  intros i p (IT & G & P & st & D & j & -> & HS) x u HN HR.
  cbn [close_ind_plug] in HR; inversion HR; subst.
  all: try solve [right; eexists; split; [eassumption|reflexivity]].
  all: try solve [destruct x; cbn [neutral root_step] in *; contradiction || discriminate].
  all: left; match goal with |- exists q, _ /\ ?u = _ =>
    lazymatch u with TCloseInd ?IT ?G ?P ?st ?D ?j _ =>
      exists (TCloseInd IT G P st D j (TVar 0)); split;
        [eauto using red_TCloseInd_IT, red_TCloseInd_G, red_TCloseInd_P, red_TCloseInd_s,
          red_TCloseInd_F, red_TCloseInd_i|reflexivity]
    end end.
Qed.
Definition close_ind_refinement i t := Mu i t /\
  forall p, close_ind_valid i p -> close_ind_result p t (close_ind_plug p t).
Lemma close_ind_refinement_candidate : Indexed.candidates RI close_ind_refinement.
Proof.
  intros i Hi; apply eliminator_refinement_candidate with (parameter_step:=reduction).
  - exact (mu_candidates i Hi).
  - exact (close_ind_result_candidate i Hi).
  - exact (close_ind_result_stable i Hi).
  - exact (close_ind_parameter_normalizing i).
  - exact (close_ind_valid_reduct i).
  - exact (close_ind_parameter_stable i Hi).
  - exact (close_ind_argument_reduction i).
  - exact (close_ind_plug_neutral i).
  - exact (close_ind_neutral_step i).
Qed.
Lemma close_ind_refinement_stable : stable_indexed_family RI close_ind_refinement.
Proof.
  split; [exact close_ind_refinement_candidate|].
  intros i j Hi Hj HC t; unfold close_ind_refinement.
  pose proof (proj2 mu_stable i j Hi Hj HC t) as HE.
  split; intros [Ht HF]; split; [now apply HE| |now apply HE|];
    intros p Hp; apply HF; apply (close_ind_valid_index i j HC); exact Hp.
Qed.
Lemma close_ind_refinement_inclusion : Indexed.inclusion RI close_ind_refinement Mu.
Proof. intros i Hi t Ht; exact (proj1 Ht). Qed.
Definition close_ind_recursive_body IT G P st :=
  TCloseInd (lift 2 0 IT) (lift 2 0 G) (lift 2 0 P) (lift 2 0 st) (lift 2 0 G) (TVar 1) (TVar 0).
Lemma close_ind_recursive_subst : forall IT G P st i x,
  subst x 0 (subst i 1 (close_ind_recursive_body IT G P st)) = TCloseInd IT G P st G i x.
Proof.
  intros; cbn [close_ind_recursive_body subst].
  rewrite ?subst_lift_prefix by lia; cbn [subst].
  cbn; now rewrite ?subst_lift_zero, ?lift_zero_id.
Qed.
Lemma close_ind_recursive_computable : forall IT G P st,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  hypothesis_method RI close_ind_refinement (diagonal_motive G P)
    (TLam (TLam (close_ind_recursive_body IT G P st))).
Proof.
  intros IT G P st HS HG HP HM; ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;G;P;st;G]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  assert (HC : forall i x, RI i -> close_ind_refinement i x ->
    small_interp (TApp (TApp (TApp P G) i) x)
      (type_elements small_atom (TApp (TApp (TApp P G) i) x))).
  { intros i x Hi Hx; apply small_type_canonical, HP;
      [now apply diagonal_definition_computable|exact Hi|].
    apply (diagonal_elements G ltac:(assumption) HG _ Hi); exact (proj1 Hx). }
  assert (HCS : forall i, RI i -> stable_family (close_ind_refinement i)
    (fun x => type_elements small_atom (TApp (TApp (TApp P G) i) x))).
  { intros i Hi x y Hx HR; eapply small_interp_unique;
      [exact (HC i x Hi Hx)|exact (HC i y Hi (candidate_reduct (close_ind_refinement_candidate i Hi) Hx HR))|].
    apply reductions_conversion, red_star_TApp; [constructor|now apply rtc_one]. }
  destruct (dependent_double_lambda_computable RI close_ind_refinement
    (fun i x => type_elements small_atom (TApp (TApp (TApp P G) i) x)) index_candidate
    close_ind_refinement_candidate (fun i x Hi Hx => small_type_candidate _ _ (HC i x Hi Hx)) HCS
    (close_ind_recursive_body IT G P st)) as [HN HA].
  - intros i x Hi Hx; rewrite close_ind_recursive_subst.
    apply (proj2 Hx (TCloseInd IT G P st G i (TVar 0))).
    exists IT,G,P,st,G,i;
      exact (conj eq_refl (conj HS0 (conj Hi (conj (cv_refl i) (conj HG (conj HG (conj HP HM))))))).
  - split; [exact HN|].
    intros i x Hi Hx; eapply small_value_conversion.
    + exists (type_elements small_atom (TApp (TApp (TApp P G) i) x)); split;
        [exact (HC i x Hi Hx)|exact (HA i x Hi Hx)].
    + exact (proj2 (diagonal_motive_computable G P ltac:(assumption) HG HP) i x Hi (proj1 Hx)).
    + apply cv_sym, diagonal_motive_application_conversion.
Qed.
Lemma close_ind_seed_root : forall IT G P st D j xs,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  computable_definition RI D -> RI j -> definition_meaning RI D j close_ind_refinement xs ->
  small_value
    (TApp (TApp (TApp (TApp st D) j) xs)
      (THyps IT (TApp D j) (carrier IT G) (diagonal_motive G P)
        (TLam (TLam (close_ind_recursive_body IT G P st))) xs))
    (TApp (TApp (TApp P D) j) (TIn xs)).
Proof.
  intros IT G P st D j xs HS HG HP HM HD Hj Hxs; ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;G;P;st]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  pose proof (computable_definition_meaning RI index_candidate D HD j Hj) as HDmean.
  assert (Hmu : definition_meaning RI D j Mu xs).
  { eapply description_interp_monotone; [exact HDmean|exact close_ind_refinement_inclusion|exact Hxs]. }
  apply HM; [exact HD|exact Hj|exact Hmu|].
  destruct (close_all_type IT G P D j xs ltac:(assumption) ltac:(assumption) HG HP HD Hj Hmu) as [R HR].
  exists R; split; [exact HR|].
  destruct (diagonal_motive_computable G P ltac:(assumption) HG HP) as [HDsn HDfam].
  eapply hyps_computable; [exact index_candidate|exact (proj2 HD j Hj)|exact HDmean
    |assumption|unfold carrier; now apply full_SN_close|exact HDsn|exact close_ind_refinement_stable
    |intros i x Hi Hx; exact (HDfam i x Hi (proj1 Hx))
    | |exact Hxs|exact HR].
  apply close_ind_recursive_computable; [exact HS0|exact HG|exact HP|exact HM].
Qed.
Lemma close_ind_seed_computable : forall i, RI i -> forall xs, F i close_ind_refinement xs ->
  forall p, close_ind_valid i p -> close_ind_result p (TIn xs) (close_ind_plug p (TIn xs)).
Proof.
  intros i Hi xs Hxs p Hp.
  assert (Hmu : Mu i (TIn xs)).
  { apply mu_fold; [exact Hi|].
    eapply functor_monotone; [exact close_ind_refinement_inclusion|exact Hi|exact Hxs]. }
  pose proof (close_ind_result_interpreted i p (TIn xs) Hi Hp Hmu) as HResult.
  pose proof (small_description_candidate _ _ _ (base_meaning i Hi) close_ind_refinement close_ind_refinement_candidate) as CF.
  pose proof (candidate_normalizing CF Hxs) as HSxs.
  destruct Hp as (IT & G & P & st & D & j & -> & HS & Hj & HC & HG & HD & HP & HM).
  ind_unpack_sns; cbn [close_ind_plug close_ind_result close_ind_result_type] in *.
  assert (HS0 : Forall full_SN [IT;G;P;st;D]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  apply computability_by_head_expansion; [exact (small_type_candidate _ _ HResult)| | |].
  - cbn [term_children]; repeat (apply Forall_cons;
      [solve [assumption|exact (candidate_normalizing index_candidate Hj)|now apply full_SN_in]|]); constructor.
  - intros t Ht; inversion Ht; exact I.
  - intros t v Ht Hv; inversion Ht; subst.
    match goal with H : rtc reduction (TIn xs) ?x |- _ =>
      destruct (in_reductions _ _ H) as [xs' [-> Rxs]] end.
    inversion Hv; subst; cbn [root_step] in *.
    match goal with H : Some _ = Some _ |- _ => inversion H; subst v end.
    assert (HV : close_ind_valid i (TCloseInd IT G P st D j (TVar 0))).
    { exists IT,G,P,st,D,j; exact (conj eq_refl (conj HS0 (conj Hj (conj HC (conj HG (conj HD (conj HP HM))))))). }
    assert (HV' : close_ind_valid i (TCloseInd IT' G' P' s' F' i' (TVar 0))) by
      (eapply close_ind_valid_components_reductions; [exact HV|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption]).
    destruct HV' as (IT0 & G0 & P0 & st0 & D0 & j0 & HE & HS' & Hj' & HC' & HG' & HD' & HP' & HM').
    inversion HE; subst IT0 G0 P0 st0 D0 j0; ind_unpack_sns.
    assert (Hxs' : definition_meaning RI F' i' close_ind_refinement xs').
    { apply (diagonal_definition_meaning F' ltac:(assumption) HD' i' Hj').
      apply (functor_index_equiv i i' Hi Hj' HC').
      exact (candidate_reducts _ CF _ _ Rxs Hxs). }
    assert (HS' : Forall full_SN [IT';G';P';s']) by
      (repeat (apply Forall_cons; [assumption|]); constructor).
    pose proof (close_ind_seed_root IT' G' P' s' F' i' xs' HS' HG' HP' HM'
      (diagonal_definition_computable F' ltac:(assumption) HD') Hj' Hxs') as Hroot.
    destruct Hroot as [S [HSR Hval]].
    apply (small_interp_unique _ _ _ _ HSR HResult); [|exact Hval].
    apply cv_sym, reductions_conversion, red_star_TApp; [|now apply red_star_TIn].
    apply red_star_TApp; [now apply red_star_TApp|assumption].
Qed.
Lemma close_ind_all_refined : Indexed.inclusion RI Mu close_ind_refinement.
Proof.
  intros i Hi x Hx; apply (Hx close_ind_refinement close_ind_refinement_candidate).
  intros j Hj xs Hxs; split.
  - apply mu_fold; [exact Hj|].
    eapply functor_monotone; [exact close_ind_refinement_inclusion|exact Hj|exact Hxs].
  - exact (close_ind_seed_computable j Hj xs Hxs).
Qed.
Lemma close_ind_recursive_total_computable : forall IT G P st,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  hypothesis_method RI Mu (diagonal_motive G P)
    (TLam (TLam (close_ind_recursive_body IT G P st))).
Proof.
  intros IT G P st HS HG HP HM.
  destruct (close_ind_recursive_computable IT G P st HS HG HP HM) as [HN HF].
  split; [exact HN|]; intros i x Hi Hx; apply HF; [exact Hi|now apply close_ind_all_refined].
Qed.
Lemma close_ind_total_seed_root : forall IT G P st D j xs,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  computable_definition RI D -> RI j -> definition_meaning RI D j Mu xs ->
  small_value
    (TApp (TApp (TApp (TApp st D) j) xs)
      (THyps IT (TApp D j) (carrier IT G) (diagonal_motive G P)
        (TLam (TLam (close_ind_recursive_body IT G P st))) xs))
    (TApp (TApp (TApp P D) j) (TIn xs)).
Proof.
  intros IT G P st D j xs HS HG HP HM HD Hj Hxs; ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;G;P;st]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  apply HM; [exact HD|exact Hj|exact Hxs|].
  destruct (close_all_type IT G P D j xs ltac:(assumption) ltac:(assumption) HG HP HD Hj Hxs) as [R HR].
  exists R; split; [exact HR|].
  destruct (diagonal_motive_computable G P ltac:(assumption) HG HP) as [HDsn HDfam].
  eapply hyps_computable; [exact index_candidate|exact (proj2 HD j Hj)
    |exact (computable_definition_meaning RI index_candidate D HD j Hj)
    |assumption|unfold carrier; now apply full_SN_close|exact HDsn|exact mu_stable|exact HDfam
    | |exact Hxs|exact HR].
  apply close_ind_recursive_total_computable; [exact HS0|exact HG|exact HP|exact HM].
Qed.
Lemma close_ind_total_seed_computable : forall IT G P st D j xs,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  computable_definition RI D -> RI j -> definition_meaning RI D j Mu xs ->
  small_value (TCloseInd IT G P st D j (TIn xs)) (TApp (TApp (TApp P D) j) (TIn xs)).
Proof.
  intros IT G P st D j xs HS HG HP HM HD Hj Hxs; ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;G;P;st]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  pose proof (computable_definition_meaning RI index_candidate D HD j Hj) as HDmean.
  pose proof (small_description_candidate _ _ _ HDmean Mu mu_candidates) as CD.
  pose proof (candidate_normalizing CD Hxs) as HSxs.
  assert (Hx : close_elements D j (TIn xs)) by (now apply rolled_elements_intro).
  pose proof (small_type_canonical _ (HP D HD j _ Hj Hx)) as HT.
  eexists; split; [exact HT|].
  apply computability_by_head_expansion; [exact (small_type_candidate _ _ HT)| | |].
  - cbn [term_children]; repeat (apply Forall_cons;
      [solve [assumption|exact (proj1 HD)|exact (candidate_normalizing index_candidate Hj)|now apply full_SN_in]|]); constructor.
  - intros t Ht; inversion Ht; exact I.
  - intros t v Ht Hv; inversion Ht; subst.
    match goal with H : rtc reduction (TIn xs) ?x |- _ =>
      destruct (in_reductions _ _ H) as [xs' [-> Rxs]] end.
    inversion Hv; subst; cbn [root_step] in *.
    match goal with H : Some _ = Some _ |- _ => inversion H; subst v end.
    assert (HG' : ind_definition RI F G') by (eapply ind_definition_reductions; [exact HG|eassumption]).
    assert (HP' : close_motive_computable P') by (eapply close_motive_reductions; [exact HP|eassumption]).
    assert (HM' : close_step_computable IT' G' P' s') by
      (eapply close_step_reductions with (IT:=IT) (G:=G) (P:=P) (st:=st); eassumption).
    assert (HD' : computable_definition RI F') by (eapply computable_definition_reductions; [exact HD|eassumption]).
    assert (Hj' : RI i') by (eapply candidate_reducts; [exact index_candidate|eassumption|exact Hj]).
    assert (HS' : Forall full_SN [IT';G';P';s']) by
      (repeat (apply Forall_cons; [solve [match goal with
        HR : rtc reduction ?t ?u, HS : full_SN ?t |- full_SN ?u => exact (full_SN_reductions _ HS _ HR) end]|]); constructor).
    assert (Hxs' : definition_meaning RI F' i' Mu xs').
    { eapply (proj1 (definition_meaning_conversion RI index_candidate D F' j i' HD HD' Hj Hj'
        ltac:(now apply reductions_conversion) ltac:(now apply reductions_conversion) Mu xs'));
      exact (candidate_reducts _ CD _ _ Rxs Hxs). }
    destruct (close_ind_total_seed_root IT' G' P' s' F' i' xs' HS' HG' HP' HM' HD' Hj' Hxs') as [R [HR Hval]].
    apply (small_interp_unique _ _ _ _ HR HT); [|exact Hval].
    apply cv_sym, reductions_conversion, red_star_TApp; [|now apply red_star_TIn].
    apply red_star_TApp; [now apply red_star_TApp|assumption].
Qed.

Lemma close_ind_compatible_parameters : forall IT G P st D j p,
  compatible (rtc reduction) (TCloseInd IT G P st D j (TVar 0)) p ->
  exists IT' G' P' st' D' j', p = TCloseInd IT' G' P' st' D' j' (TVar 0) /\
  rtc reduction IT IT' /\ rtc reduction G G' /\ rtc reduction P P' /\
  rtc reduction st st' /\ rtc reduction D D' /\ rtc reduction j j'.
Proof.
  intros IT G P st D j p H; inversion H; subst.
  match goal with HR : rtc reduction (TVar 0) ?x |- _ =>
    assert (HE : TVar 0 = x) by (apply normal_reductions_identity;
      [intros y HY; inversion HY; discriminate|exact HR]); subst x end.
  do 6 eexists; repeat split; eassumption.
Qed.
Lemma close_ind_dummy_step : forall IT G P st D j q,
  reduction (TCloseInd IT G P st D j (TVar 0)) q ->
  compatible (rtc reduction) (TCloseInd IT G P st D j (TVar 0)) q.
Proof.
  intros IT G P st D j q H; inversion H; subst; try discriminate.
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: constructor; solve [apply rtc_refl|now apply rtc_one].
Qed.
Lemma close_ind_dummy_normalizing : forall IT G P st D j,
  Forall full_SN [IT;G;P;st;D;j] -> full_SN (TCloseInd IT G P st D j (TVar 0)).
Proof.
  intros IT G P st D j HS; ind_unpack_sns; apply normalization_by_head_expansion.
  - cbn [term_children]; repeat (apply Forall_cons;
      [solve [assumption|exact (candidate_variable _ normalizing_candidate 0)]|]); constructor.
  - intros t v HT HV; inversion HT; subst.
    match goal with H : rtc reduction (TVar 0) ?x |- _ =>
      assert (HE : TVar 0 = x) by (apply normal_reductions_identity;
        [intros y HY; inversion HY; discriminate|exact H]); subst x end.
    inversion HV; subst; discriminate.
Qed.
Lemma close_ind_dummy_neutral_step : forall IT G P st D j x u,
  neutral x -> reduction (TCloseInd IT G P st D j x) u ->
  (exists q, reduction (TCloseInd IT G P st D j (TVar 0)) q /\ u = close_ind_plug q x) \/
  (exists y, reduction x y /\ u = TCloseInd IT G P st D j y).
Proof.
  intros IT G P st D j x u HN HR; inversion HR; subst.
  all: try solve [right; eexists; split; [eassumption|reflexivity]].
  all: try solve [destruct x; cbn [neutral root_step] in *; contradiction || discriminate].
  all: left; match goal with |- exists q, _ /\ ?u = _ =>
    lazymatch u with TCloseInd ?IT ?G ?P ?st ?D ?j _ =>
      exists (TCloseInd IT G P st D j (TVar 0)); split;
        [eauto using red_TCloseInd_IT, red_TCloseInd_G, red_TCloseInd_P, red_TCloseInd_s,
          red_TCloseInd_F, red_TCloseInd_i|reflexivity]
    end end.
Qed.

Theorem close_ind_computable : forall IT G P st D j x,
  Forall full_SN [IT;G;P;st] -> ind_definition RI F G ->
  close_motive_computable P -> close_step_computable IT G P st ->
  computable_definition RI D -> RI j -> close_elements D j x ->
  small_value (TCloseInd IT G P st D j x) (TApp (TApp (TApp P D) j) x).
Proof.
  intros IT G P st D j x HS HG HP HM HD Hj Hx.
  pose proof HS as HS0; ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;G;P;st]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  pose proof (computable_definition_meaning RI index_candidate D HD j Hj) as HDmean.
  pose proof (small_description_candidate _ _ _ HDmean Mu mu_candidates) as CD.
  pose proof (close_elements_candidate D HD j Hj) as CC.
  set (Result := fun y => type_elements small_atom (TApp (TApp (TApp P D) j) y)).
  assert (HT : forall y, close_elements D j y -> small_interp (TApp (TApp (TApp P D) j) y) (Result y))
    by (intros y Hy; apply small_type_canonical; exact (HP D HD j y Hj Hy)).
  assert (CR : forall y, close_elements D j y -> candidate (Result y)) by
    (intros y Hy; exact (small_type_candidate _ _ (HT y Hy))).
  assert (CS : stable_family (close_elements D j) Result).
  { intros y z Hy HR; eapply small_interp_unique;
      [exact (HT y Hy)|exact (HT z (candidate_reduct CC Hy HR))|].
    apply reductions_conversion, red_star_TApp; [constructor|now apply rtc_one]. }
  exists (Result x); split; [exact (HT x Hx)|].
  change (Result x (close_ind_plug (TCloseInd IT G P st D j (TVar 0)) x)).
  eapply saturated_elimination with
    (parameter_step:=reduction)
    (valid_parameter:=compatible (rtc reduction) (TCloseInd IT G P st D j (TVar 0)))
    (seed:=fun z => exists u, z = TIn u /\ definition_meaning RI D j Mu u).
  - intros z [u [-> Hu]]; apply full_SN_in; exact (candidate_normalizing CD Hu).
  - exact CR.
  - exact CS.
  - intros p q Hv HR.
    pose proof Hv as Hparts.
    destruct (close_ind_compatible_parameters _ _ _ _ _ _ _ Hparts)
      as (IT' & G' & P' & st' & D' & j' & -> & Hrest).
    eapply compatible_reductions_trans; [exact Hv|now apply close_ind_dummy_step].
  - intros p Hv y z HR.
    destruct (close_ind_compatible_parameters _ _ _ _ _ _ _ Hv)
      as (IT' & G' & P' & st' & D' & j' & -> & Hrest).
    cbn [close_ind_plug]; now apply red_TCloseInd_x.
  - intros p Hv y.
    destruct (close_ind_compatible_parameters _ _ _ _ _ _ _ Hv)
      as (IT' & G' & P' & st' & D' & j' & -> & Hrest); exact I.
  - intros p Hv y z HN HR.
    destruct (close_ind_compatible_parameters _ _ _ _ _ _ _ Hv)
      as (IT' & G' & P' & st' & D' & j' & -> & Hrest).
    eapply close_ind_dummy_neutral_step; eassumption.
  - intros p Hv z [u [-> Hu]].
    destruct (close_ind_compatible_parameters _ _ _ _ _ _ _ Hv)
      as (IT' & G' & P' & st' & D' & j' & -> & RIT & RG & RP & RS & RD & Rj).
    cbn [close_ind_plug].
    assert (HG' : ind_definition RI F G') by (eapply ind_definition_reductions; [exact HG|exact RG]).
    assert (HP' : close_motive_computable P') by (eapply close_motive_reductions; [exact HP|exact RP]).
    assert (HM' : close_step_computable IT' G' P' st') by
      (eapply close_step_reductions with (IT:=IT) (G:=G) (P:=P) (st:=st); eassumption).
    pose proof (computable_definition_reductions RI D HD D' RD) as HD'.
    pose proof (candidate_reducts _ index_candidate _ _ Rj Hj) as Hj'.
    assert (HS' : Forall full_SN [IT';G';P';st']) by
      (repeat (apply Forall_cons; [solve [match goal with
        HR : rtc reduction ?t ?u, HS : full_SN ?t |- full_SN ?u => exact (full_SN_reductions _ HS _ HR) end]|]); constructor).
    assert (Hu' : definition_meaning RI D' j' Mu u).
    { apply (proj1 (definition_meaning_conversion RI index_candidate D D' j j' HD HD' Hj Hj'
        (reductions_conversion _ _ RD) (reductions_conversion _ _ Rj) Mu u)); exact Hu. }
    destruct (close_ind_total_seed_computable IT' G' P' st' D' j' u HS' HG' HP' HM' HD' Hj' Hu') as [R [HR Hvalue]].
    apply (small_interp_unique _ _ _ _ HR (HT (TIn u) (rolled_elements_intro _ _ Hu))); [|exact Hvalue].
    apply cv_sym, reductions_conversion, red_star_TApp; [|constructor].
    apply red_star_TApp; [now apply red_star_TApp|exact Rj].
  - apply close_ind_dummy_normalizing.
    repeat (apply Forall_cons; [solve [assumption|exact (proj1 HD)|exact (candidate_normalizing index_candidate Hj)]|]); constructor.
  - apply compatible_reductions_refl.
  - exact Hx.
Qed.
End CloseIndComputability.

Print Assumptions close_ind_all_refined.
Print Assumptions close_ind_computable.
