(* Semantic induction on the positive fixed point. Recursive calls are
   justified on the refined children selected by each description. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBSwitchComputability nameless.DBEliminatorCandidates nameless.DBBetaExpansion.
Import ListNotations Full.
Ltac ind_unpack_sns := repeat match goal with H : Forall full_SN (_ :: _) |- _ => inversion H; subst; clear H end.

Lemma small_value_conversion : forall t A B,
  small_value t A -> reducible_type small_atom B -> conv A B -> small_value t B.
Proof.
  intros t A B [R [HR Ht]] HB HC; exists R; split; [|exact Ht].
  eapply type_interp_conversion; [exact HR|exact (candidate_normalizing (reducible_type_candidate small_atom) HB)|exact HC].
Qed.
Definition ind_plug p x :=
  match p with TInd IT D P st j _ => TInd IT D P st j x | _ => TVar 0 end.
Definition ind_result_type p x :=
  match p with TInd IT D P st j _ => TApp P (TPair j x) | _ => TUnitT end.
Definition ind_result p x := type_elements small_atom (ind_result_type p x).

Section IndComputability.
Variable RI : term -> Prop.
Hypothesis index_candidate : candidate RI.
Variable base_definition : term.
Variable F : term -> description_functor.
Hypothesis base_meaning : forall j, RI j -> small_description RI (TApp base_definition j) (F j).
Let Mu := description_fixed_point RI F.
Lemma ind_mu_candidates : Indexed.candidates RI Mu.
Proof. exact (small_fixed_point_candidate RI base_definition F base_meaning). Qed.
Lemma ind_mu_stable : stable_indexed_family RI Mu.
Proof.
  split; [exact ind_mu_candidates|].
  exact (small_fixed_point_index_equiv RI base_definition F base_meaning).
Qed.
Lemma ind_functor_monotone : forall X Y, Indexed.inclusion RI X Y ->
  Indexed.inclusion RI (fun i => F i X) (fun i => F i Y).
Proof. intros X Y HXY i Hi t Ht; eapply description_interp_monotone; [exact (base_meaning i Hi)|exact HXY|exact Ht]. Qed.
Lemma ind_mu_fold : forall i, RI i -> forall xs, F i Mu xs -> Mu i (TIn xs).
Proof. intros i Hi xs Hxs; eapply Indexed.mu_fold; [exact ind_functor_monotone|exact Hi|exact Hxs]. Qed.
Lemma ind_functor_index_equiv : forall i j, RI i -> RI j -> conv i j ->
  forall X, predicate_equiv (F i X) (F j X).
Proof.
  intros i j Hi Hj HC X; eapply small_description_unique;
    [exact (base_meaning i Hi)|exact (base_meaning j Hj)|].
  apply cv_compatible, cp_TApp; [apply cv_refl|exact HC].
Qed.
Definition ind_definition D := forall j, RI j ->
  small_code RI (TApp D j) /\ small_description RI (TApp D j) (F j).
Lemma ind_definition_reductions : forall D, ind_definition D -> forall D',
  rtc reduction D D' -> ind_definition D'.
Proof.
  intros D HD D' HR j Hj; destruct (HD j Hj) as [HC HM]; split.
  - eapply candidate_reducts; [apply description_computable_candidate| |exact HC].
    apply red_star_TApp; [exact HR|constructor].
  - eapply description_interp_reductions; [exact HM|].
    apply red_star_TApp; [exact HR|constructor].
Qed.
Definition ind_method IT D P st := forall j xs h, RI j -> F j Mu xs ->
  small_value h (TIAll IT (TApp D j) (TMuI IT D) xs P) ->
  small_value (TApp (TApp (TApp st j) xs) h) (TApp P (TPair j (TIn xs))).
Lemma ind_all_type : forall IT D P j xs,
  full_SN IT -> full_SN D -> full_SN P -> ind_definition D ->
  hypothesis_family RI Mu P -> RI j -> F j Mu xs ->
  reducible_type small_atom (TIAll IT (TApp D j) (TMuI IT D) xs P).
Proof.
  intros IT D P j xs HI HD HP HF HQ Hj Hxs.
  destruct (HF j Hj) as [HC HM].
  eapply all_computable; [exact index_candidate|exact HC|exact HM|exact HI
    |now apply full_SN_mui|exact HP|exact ind_mu_stable|exact HQ|exact Hxs].
Qed.
Lemma ind_method_reductions : forall IT D P st,
  full_SN IT -> full_SN D -> full_SN P -> ind_definition D ->
  hypothesis_family RI Mu P -> ind_method IT D P st -> forall IT' D' P' st',
  rtc reduction IT IT' -> rtc reduction D D' -> rtc reduction P P' -> rtc reduction st st' ->
  ind_method IT' D' P' st'.
Proof.
  intros IT D P st HI HD HP HF HQ HM IT' D' P' st' RIT RD RP RS j xs h Hj Hxs Hh.
  assert (Hh0 : small_value h (TIAll IT (TApp D j) (TMuI IT D) xs P)).
  { eapply small_value_conversion; [exact Hh|eapply ind_all_type; eassumption|].
    apply cv_sym, reductions_conversion, red_star_TIAll;
      [exact RIT|apply red_star_TApp; [exact RD|constructor]|now apply red_star_TMuI|constructor|exact RP]. }
  eapply small_value_type_reductions.
  - eapply small_value_reductions; [exact (HM j xs h Hj Hxs Hh0)|].
    apply red_star_TApp; [apply red_star_TApp; [apply red_star_TApp; [exact RS|constructor]|constructor]|constructor].
  - apply red_star_TApp; [exact RP|constructor].
Qed.
Definition ind_valid i p := exists IT D P st j,
  p = TInd IT D P st j (TVar 0) /\ Forall full_SN [IT;D;P;st] /\
  RI j /\ conv i j /\ ind_definition D /\ hypothesis_family RI Mu P /\ ind_method IT D P st.
Lemma ind_valid_components_reductions : forall i IT D P st j,
  ind_valid i (TInd IT D P st j (TVar 0)) -> forall IT' D' P' st' j',
  rtc reduction IT IT' -> rtc reduction D D' -> rtc reduction P P' ->
  rtc reduction st st' -> rtc reduction j j' ->
  ind_valid i (TInd IT' D' P' st' j' (TVar 0)).
Proof.
  intros i IT D P st j [IT0 [D0 [P0 [st0 [j0 [HE [HS [Hj [HC [HF [HQ HM]]]]]]]]]]].
  inversion HE; subst; ind_unpack_sns.
  intros IT' D' P' st' j' RIT RD RP RS Rj.
  exists IT',D',P',st',j'; split; [reflexivity|].
  split.
  - repeat (apply Forall_cons; [solve [match goal with
      HR : rtc reduction ?t ?u, HS : full_SN ?t |- full_SN ?u =>
        exact (full_SN_reductions _ HS _ HR) end]|]); constructor.
  - split; [exact (candidate_reducts _ index_candidate _ _ Rj Hj)|].
    split; [eapply cv_trans; [exact HC|exact (reductions_conversion _ _ Rj)]|].
    split; [eapply ind_definition_reductions; eassumption|].
    split; [eapply hypothesis_family_reductions; eassumption|].
    eapply ind_method_reductions with (IT:=IT0) (D:=D0) (P:=P0) (st:=st0); eassumption.
Qed.
Lemma ind_valid_reduct : forall i p q, ind_valid i p -> reduction p q -> ind_valid i q.
Proof.
  intros i p q HV HR; destruct HV as [IT [D [P [st [j [-> HS]]]]]].
  assert (HV : ind_valid i (TInd IT D P st j (TVar 0))) by (exists IT,D,P,st,j; auto).
  inversion HR; subst; try discriminate.
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: eapply ind_valid_components_reductions; [exact HV| | | | |]; solve [constructor|now apply rtc_one].
Qed.
Lemma ind_valid_index : forall i j, conv i j -> forall p, ind_valid i p <-> ind_valid j p.
Proof.
  intros i j HC p; split; intros [IT [D [P [st [z [HE [HS [Hz [HCz [HD [HP HM]]]]]]]]]]];
    exists IT,D,P,st,z; refine (conj HE (conj HS (conj Hz (conj _ (conj HD (conj HP HM)))))).
  - eapply cv_trans; [apply cv_sym; exact HC|exact HCz].
  - eapply cv_trans; [exact HC|exact HCz].
Qed.
Lemma ind_result_interpreted : forall i p x,
  RI i -> ind_valid i p -> Mu i x -> small_interp (ind_result_type p x) (ind_result p x).
Proof.
  intros i p x Hi [IT [D [P [st [j [-> [HS [Hj [HC [HD [HP HM]]]]]]]]]]] Hx.
  apply small_type_canonical, HP; [exact Hj|].
  apply (proj2 ind_mu_stable i j); [exact Hi|exact Hj|exact HC|exact Hx].
Qed.
Lemma ind_result_candidate : forall i, RI i -> forall p,
  ind_valid i p -> forall x, Mu i x -> candidate (ind_result p x).
Proof. intros; eapply small_type_candidate, ind_result_interpreted; eassumption. Qed.
Lemma ind_result_stable : forall i, RI i -> forall p,
  ind_valid i p -> stable_family (Mu i) (ind_result p).
Proof.
  intros i Hi p Hp x y Hx HR.
  pose proof (candidate_reduct (ind_mu_candidates i Hi) Hx HR) as Hy.
  eapply small_interp_unique;
    [exact (ind_result_interpreted i p x Hi Hp Hx)|exact (ind_result_interpreted i p y Hi Hp Hy)|].
  destruct Hp as [IT [D [P [st [j [-> _]]]]]]; cbn [ind_result_type].
  apply reductions_conversion, red_star_TApp; [constructor|].
  apply red_star_TPair; [constructor|now apply rtc_one].
Qed.
Lemma ind_parameter_type_reduction : forall i p q, ind_valid i p -> reduction p q ->
  forall x, rtc reduction (ind_result_type p x) (ind_result_type q x).
Proof.
  intros i p q [IT [D [P [st [j [-> HS]]]]]] HR x.
  inversion HR; subst; try discriminate.
  all: cbn [ind_result_type].
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: repeat first [apply rtc_refl | apply red_star_TApp | apply red_star_TPair | apply rtc_one; assumption].
Qed.
Lemma ind_parameter_stable : forall i, RI i -> forall p q,
  ind_valid i p -> reduction p q -> forall x, Mu i x ->
  predicate_equiv (ind_result p x) (ind_result q x).
Proof.
  intros i Hi p q Hp HR x Hx; eapply small_interp_unique;
    [exact (ind_result_interpreted i p x Hi Hp Hx)
    |exact (ind_result_interpreted i q x Hi (ind_valid_reduct i p q Hp HR) Hx)|].
  apply reductions_conversion; eapply ind_parameter_type_reduction; eassumption.
Qed.
Lemma ind_parameter_normalizing : forall i p, ind_valid i p -> full_SN p.
Proof.
  intros i p [IT [D [P [st [j [-> [HS [Hj Hrest]]]]]]]].
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
Lemma ind_argument_reduction : forall i p, ind_valid i p -> forall x y,
  reduction x y -> reduction (ind_plug p x) (ind_plug p y).
Proof. intros i p [IT [D [P [st [j [-> _]]]]]] x y H; cbn [ind_plug]; now apply red_TInd_x. Qed.
Lemma ind_plug_neutral : forall i p, ind_valid i p -> forall x, neutral (ind_plug p x).
Proof. intros i p [IT [D [P [st [j [-> _]]]]]] x; exact I. Qed.
Lemma ind_neutral_step : forall i p, ind_valid i p -> forall x u,
  neutral x -> reduction (ind_plug p x) u ->
  (exists q, reduction p q /\ u = ind_plug q x) \/
  (exists y, reduction x y /\ u = ind_plug p y).
Proof.
  intros i p [IT [D [P [st [j [-> _]]]]]] x u HN HR.
  cbn [ind_plug] in HR; inversion HR; subst.
  all: try solve [right; eexists; split; [eassumption|reflexivity]].
  all: try solve [destruct x; cbn [neutral root_step] in *; contradiction || discriminate].
  all: left; match goal with |- exists q, _ /\ ?u = _ =>
    lazymatch u with TInd ?IT ?D ?P ?st ?j _ =>
      exists (TInd IT D P st j (TVar 0)); split;
        [eauto using red_TInd_IT, red_TInd_D, red_TInd_P, red_TInd_s, red_TInd_i|reflexivity]
    end end.
Qed.
Definition ind_refinement i t := Mu i t /\ forall p, ind_valid i p -> ind_result p t (ind_plug p t).
Lemma ind_refinement_candidate : Indexed.candidates RI ind_refinement.
Proof.
  intros i Hi; apply eliminator_refinement_candidate with (parameter_step:=reduction).
  - exact (ind_mu_candidates i Hi).
  - exact (ind_result_candidate i Hi).
  - exact (ind_result_stable i Hi).
  - exact (ind_parameter_normalizing i).
  - exact (ind_valid_reduct i).
  - exact (ind_parameter_stable i Hi).
  - exact (ind_argument_reduction i).
  - exact (ind_plug_neutral i).
  - exact (ind_neutral_step i).
Qed.
Lemma ind_refinement_stable : stable_indexed_family RI ind_refinement.
Proof.
  split; [exact ind_refinement_candidate|].
  intros i j Hi Hj HC t; unfold ind_refinement.
  pose proof (proj2 ind_mu_stable i j Hi Hj HC t) as HE.
  split; intros [Ht HF]; split; [now apply HE| |now apply HE|];
    intros p Hp; apply HF; apply (ind_valid_index i j HC); exact Hp.
Qed.
Lemma ind_refinement_inclusion : Indexed.inclusion RI ind_refinement Mu.
Proof. intros i Hi t Ht; exact (proj1 Ht). Qed.
Lemma ind_refined_motive : forall P, hypothesis_family RI Mu P ->
  hypothesis_family RI ind_refinement P.
Proof. intros P HP i x Hi Hx; exact (HP i x Hi (proj1 Hx)). Qed.
Definition ind_recursive_body IT D P st :=
  TInd (lift 2 0 IT) (lift 2 0 D) (lift 2 0 P) (lift 2 0 st) (TVar 1) (TVar 0).
Lemma ind_recursive_subst : forall IT D P st i x,
  subst x 0 (subst i 1 (ind_recursive_body IT D P st)) = TInd IT D P st i x.
Proof.
  intros; cbn [ind_recursive_body subst].
  rewrite ?subst_lift_prefix by lia; cbn [subst].
  cbn; now rewrite ?subst_lift_zero, ?lift_zero_id.
Qed.
Lemma ind_recursive_computable : forall IT D P st,
  Forall full_SN [IT;D;P;st] -> ind_definition D ->
  hypothesis_family RI Mu P -> ind_method IT D P st ->
  hypothesis_method RI ind_refinement P (TLam (TLam (ind_recursive_body IT D P st))).
Proof.
  intros IT D P st HS HD HP HM.
  assert (HC : forall i x, RI i -> ind_refinement i x ->
    small_interp (TApp P (TPair i x)) (type_elements small_atom (TApp P (TPair i x)))).
  { intros i x Hi Hx; apply small_type_canonical; exact (HP i x Hi (proj1 Hx)). }
  assert (HCS : forall i, RI i -> stable_family (ind_refinement i)
    (fun x => type_elements small_atom (TApp P (TPair i x)))).
  { intros i Hi x y Hx HR; eapply small_interp_unique;
      [exact (HC i x Hi Hx)|exact (HC i y Hi (candidate_reduct (ind_refinement_candidate i Hi) Hx HR))|].
    apply reductions_conversion, red_star_TApp; [constructor|].
    apply red_star_TPair; [constructor|now apply rtc_one]. }
  destruct (dependent_double_lambda_computable RI ind_refinement
    (fun i x => type_elements small_atom (TApp P (TPair i x))) index_candidate
    ind_refinement_candidate (fun i x Hi Hx => small_type_candidate _ _ (HC i x Hi Hx)) HCS
    (ind_recursive_body IT D P st)) as [HN HA].
  - intros i x Hi Hx; rewrite ind_recursive_subst.
    apply (proj2 Hx (TInd IT D P st i (TVar 0))).
    exists IT,D,P,st,i; refine (conj eq_refl (conj HS (conj Hi (conj (cv_refl i) (conj HD (conj HP HM)))))).
  - split; [exact HN|].
    intros i x Hi Hx; exists (type_elements small_atom (TApp P (TPair i x))); split;
      [exact (HC i x Hi Hx)|exact (HA i x Hi Hx)].
Qed.
Lemma ind_seed_root : forall IT D P st j xs,
  Forall full_SN [IT;D;P;st] -> ind_definition D ->
  hypothesis_family RI Mu P -> ind_method IT D P st -> RI j -> F j ind_refinement xs ->
  small_value
    (TApp (TApp (TApp st j) xs)
      (THyps IT (TApp D j) (TMuI IT D) P
        (TLam (TLam (ind_recursive_body IT D P st))) xs))
    (TApp P (TPair j (TIn xs))).
Proof.
  intros IT D P st j xs HS HD HP HM Hj Hxs.
  ind_unpack_sns.
  assert (HS0 : Forall full_SN [IT;D;P;st]) by
    (repeat (apply Forall_cons; [assumption|]); constructor).
  assert (Hmu : F j Mu xs) by (eapply ind_functor_monotone; [exact ind_refinement_inclusion|exact Hj|exact Hxs]).
  apply HM; [exact Hj|exact Hmu|].
  destruct (ind_all_type IT D P j xs ltac:(assumption) ltac:(assumption) ltac:(assumption) HD HP Hj Hmu) as [R HR].
  exists R; split; [exact HR|].
  destruct (HD j Hj) as [Hcode Hmeaning].
  eapply hyps_computable; [exact index_candidate|exact Hcode|exact Hmeaning
    |assumption|now apply full_SN_mui|assumption|exact ind_refinement_stable
    |now apply ind_refined_motive| |exact Hxs|exact HR].
  apply ind_recursive_computable; [exact HS0|exact HD|exact HP|exact HM].
Qed.
Lemma ind_seed_computable : forall i, RI i -> forall xs, F i ind_refinement xs ->
  forall p, ind_valid i p -> ind_result p (TIn xs) (ind_plug p (TIn xs)).
Proof.
  intros i Hi xs Hxs p Hp.
  assert (Hmu : Mu i (TIn xs)).
  { apply ind_mu_fold; [exact Hi|].
    eapply ind_functor_monotone; [exact ind_refinement_inclusion|exact Hi|exact Hxs]. }
  pose proof (ind_result_interpreted i p (TIn xs) Hi Hp Hmu) as HResult.
  pose proof (small_description_candidate _ _ _ (base_meaning i Hi) ind_refinement ind_refinement_candidate) as CF.
  pose proof (candidate_normalizing CF Hxs) as HSxs.
  destruct Hp as [IT [D [P [st [j [-> [HS [Hj [HC [HD [HP HM]]]]]]]]]]].
  ind_unpack_sns; cbn [ind_plug ind_result ind_result_type] in *.
  assert (HS0 : Forall full_SN [IT;D;P;st]) by
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
    assert (HV : ind_valid i (TInd IT D P st j (TVar 0))).
    { exists IT,D,P,st,j; exact (conj eq_refl (conj HS0 (conj Hj (conj HC (conj HD (conj HP HM)))))). }
    assert (HV' : ind_valid i (TInd IT' D' P' s' i' (TVar 0))) by
      (eapply ind_valid_components_reductions; [exact HV|eassumption|eassumption|eassumption|eassumption|eassumption]).
    destruct HV' as (IT0 & D0 & P0 & st0 & j0 & HE & HS' & Hj' & HC' & HD' & HP' & HM').
    inversion HE; subst IT0 D0 P0 st0 j0.
    assert (Hxs' : F i' ind_refinement xs').
    { apply (ind_functor_index_equiv i i' Hi Hj' HC').
      exact (candidate_reducts _ CF _ _ Rxs Hxs). }
    pose proof (ind_seed_root IT' D' P' s' i' xs' HS' HD' HP' HM' Hj' Hxs') as Hroot.
    destruct Hroot as [S [HSR Hval]].
    apply (calculus_interp_unique 0 0 _ _ _ _ (small_type_in_universe _ _ HSR 0)
      (small_type_in_universe _ _ HResult 0)); [|exact Hval].
    apply cv_sym, reductions_conversion, red_star_TApp; [assumption|].
    apply red_star_TPair; [assumption|now apply red_star_TIn].
Qed.

Theorem ind_computable : forall IT D P st j x,
  Forall full_SN [IT;D;P;st] -> ind_definition D ->
  hypothesis_family RI Mu P -> ind_method IT D P st -> RI j -> Mu j x ->
  small_value (TInd IT D P st j x) (TApp P (TPair j x)).
Proof.
  intros IT D P st j x HS HD HP HM Hj Hx.
  assert (HPref : Indexed.prefixed RI (fun X i => F i X) ind_refinement).
  { intros i Hi xs Hxs; split.
    - apply ind_mu_fold; [exact Hi|].
      eapply ind_functor_monotone; [exact ind_refinement_inclusion|exact Hi|exact Hxs].
    - exact (ind_seed_computable i Hi xs Hxs). }
  pose proof (Hx ind_refinement ind_refinement_candidate HPref) as Href.
  exists (type_elements small_atom (TApp P (TPair j x))); split.
  - apply small_type_canonical; exact (HP j x Hj Hx).
  - apply (proj2 Href (TInd IT D P st j (TVar 0))).
    exists IT,D,P,st,j; exact (conj eq_refl (conj HS (conj Hj (conj (cv_refl j) (conj HD (conj HP HM)))))).
Qed.
End IndComputability.

Print Assumptions ind_refinement_candidate.
Print Assumptions ind_computable.
