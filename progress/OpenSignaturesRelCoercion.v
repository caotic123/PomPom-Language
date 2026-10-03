(* Realizability of coercions: every coercion derivation realizes a
   semantic coercion graph under related closing environments. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelGraphComp.
Import ListNotations.

Definition sub_typed := subtyping_from_rules named_weakening named_type_correctness
  named_preservation (dead_from_rules named_weakening).
Definition desc_sub_typed := description_subtyping_from_rules named_weakening (dead_from_rules named_weakening).
Definition dead_typed := dead_from_rules named_weakening.

(* ------------------------------------------------------------------ *)
(* Semantic basics under a closing environment *)

Lemma closing2_refl_r : forall Gamma g1 g2, closing2 Gamma g1 g2 -> closing2 Gamma g2 g2.
Proof.
  intros Gamma g1 g2 H; induction H; [apply c2_nil|].
  apply c2_cons; try assumption. eapply rel_at_right_of; eassumption.
Qed.

Lemma inst_closed1 : forall Gamma g t A, closing2 Gamma g g -> typing Gamma t A -> closed (instantiate g t).
Proof. intros; eapply inst_closed_typed; eassumption. Qed.

Lemma fund_self : forall Gamma g t A, closing2 Gamma g g -> typing Gamma t A ->
  rel_at (instantiate g t) (instantiate g t) (instantiate g A) (instantiate g A).
Proof. intros; apply (rel_fundamental _ _ _ H0 _ _ H). Qed.

Lemma tyw_inst : forall Gamma g A, closing2 Gamma g g -> type_wf Gamma A -> tyw (instantiate g A).
Proof.
  intros Gamma g A Hc [k Hk]. pose proof (fund_self _ _ _ _ Hc Hk) as H.
  rewrite instantiate_sort in H. apply rel_at_sort in H. destruct H as [R HR]; exists k, R; exact HR.
Qed.

Lemma closed_type_inst : forall Gamma g A, closing2 Gamma g g -> type_wf Gamma A -> closed (instantiate g A).
Proof. intros Gamma g A Hc [k Hk]; eapply inst_closed1; eassumption. Qed.

Lemma type_wf_of_typing : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Proof. intros; eapply named_type_correctness; eassumption. Qed.

Lemma coe_app : forall Gamma g c A B a, closing2 Gamma g g -> typing Gamma c (arrow A B) ->
  type_wf Gamma A -> type_wf Gamma B ->
  closed a -> rel_at a a (instantiate g A) (instantiate g A) ->
  closed (TApp (instantiate g c) a) /\
  rel_at (TApp (instantiate g c) a) (TApp (instantiate g c) a) (instantiate g B) (instantiate g B).
Proof.
  intros Gamma g c A B a Hc Ht HA HB Ha Haa. destruct (closing2_closed _ _ _ Hc) as [Hg _].
  pose proof (closed_type_inst _ _ _ Hc HA) as HAc. pose proof (closed_type_inst _ _ _ Hc HB) as HBc.
  split; [apply closed_app; [eapply inst_closed1; eassumption|exact Ha]|].
  pose proof (fund_self _ _ _ _ Hc Ht) as Hf.
  eapply rel_at_conv in Hf; [|apply cv_refl|apply cv_refl|apply inst_arrow; assumption|apply inst_arrow; assumption].
  exact (sem_arrow_app _ _ _ _ _ _ _ _ Hf Haa Ha Ha).
Qed.

Lemma Bot_empty : forall t u, ~ rel_at t u Bot Bot.
Proof.
  intros t u H. destruct (rel_at_enum _ _ _ _ [] H (cv_refl _)) as [m [Hm _]]. cbn in Hm; lia.
Qed.

Lemma closed_Bot : closed Bot.
Proof. reflexivity. Qed.

Lemma dead_empty : forall Gamma IT D X d g, dead Gamma IT D X d -> closing2 Gamma g g ->
  forall t u, closed t -> ~ rel_at t u (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D X)).
Proof.
  intros Gamma IT D X d g Hd Hc t u Ht Htu.
  pose proof (dead_typed _ _ _ _ _ Hd) as Hty.
  destruct (dead_input _ _ _ _ _ Hd) as [HIT [HD HX]].
  assert (HTw : type_wf Gamma (TInterp IT D X)) by (exists 0; apply ty_interp; assumption).
  assert (HBw : type_wf Gamma Bot).
  { exists 0. apply ty_enumt. apply ty_nile. eapply typing_context; exact HIT. }
  destruct (coe_app _ _ _ _ _ t Hc Hty HTw HBw Ht (rel_at_left_of _ _ _ _ Htu)) as [_ Hb].
  rewrite (instantiate_closed g Bot) in Hb by reflexivity. exact (Bot_empty _ _ Hb).
Qed.

(* ------------------------------------------------------------------ *)
(* Beta laws of the coercion formers *)

Lemma subst_ccase : forall u x k a b c d e f h,
  subst u x (TCloseCase k a b c d e f h) =
  TCloseCase k (subst u x a) (subst u x b) (subst u x c) (subst u x d) (subst u x e) (subst u x f) (subst u x h).
Proof. reflexivity. Qed.

Lemma fresh_in_list : forall ts t, In t ts -> ~ In (fresh ts) (free_vars t).
Proof. intros; apply fresh_not_free; assumption. Qed.

Lemma close_coercion_beta : forall IT F H G i q t,
  conv (TApp (close_coercion IT F H G i q) t) (TIn (TApp q (unroll IT F G i t))).
Proof.
  intros IT F H G i q t; unfold close_coercion.
  set (x := fresh [IT; F; H; G; i; q]).
  assert (HIT : ~ In x (free_vars IT)) by (apply fresh_in_list; cbn; auto).
  assert (HF : ~ In x (free_vars F)) by (apply fresh_in_list; cbn; auto).
  assert (HG : ~ In x (free_vars G)) by (apply fresh_in_list; cbn; auto 6).
  assert (Hi : ~ In x (free_vars i)) by (apply fresh_in_list; cbn; auto 7).
  assert (Hq : ~ In x (free_vars q)) by (apply fresh_in_list; cbn; auto 8).
  eapply cv_trans; [apply beta_conv|]. unfold unroll.
  rewrite subst_in, subst_app, subst_ccase, subst_var_same.
  rewrite (subst_fresh q), (subst_fresh IT), (subst_fresh F), (subst_fresh G), (subst_fresh i) by assumption.
  rewrite (subst_fresh (constant (payload IT F G i))), (subst_fresh identity); [apply cv_refl| |].
  - cbn; tauto.
  - unfold constant, payload, carrier; cbn [free_vars]. rewrite in_remove_iff.
    intros [Hin _]. repeat rewrite in_app_iff in Hin. tauto.
Qed.

Lemma unroll_in : forall IT F G i xs, conv (unroll IT F G i (TIn xs)) xs.
Proof.
  intros; unfold unroll. eapply cv_trans; [apply conv_root; reflexivity|]. apply conv_root; reflexivity.
Qed.

Lemma pi_coercion_beta : forall y c d f a, closed f -> closed a ->
  conv (TApp (TApp (pi_coercion y c d) f) a) (TApp (subst a y d) (TApp f (TApp (subst a y c) a))).
Proof.
  intros y c d f a Hf Ha; unfold pi_coercion.
  set (fv := fresh [c; d; TVar y]).
  assert (Hc : ~ In fv (free_vars c)) by (apply fresh_in_list; cbn; auto).
  assert (Hd : ~ In fv (free_vars d)) by (apply fresh_in_list; cbn; auto).
  assert (Hy0 : ~ In fv (free_vars (TVar y))) by (apply fresh_in_list; cbn; auto).
  assert (Hy : fv <> y) by (intro E; apply Hy0; rewrite E; cbn; auto).
  eapply cv_trans; [apply conv_app_f, beta_conv|].
  rewrite subst_lam_closed by assumption.
  rewrite !subst_app, subst_var_same, subst_var_other by (exact Hy).
  rewrite (subst_fresh d), (subst_fresh c) by assumption.
  eapply cv_trans; [apply beta_conv|].
  rewrite !subst_app, subst_var_same, (subst_not_free f) by (apply closed_not_in; exact Hf).
  apply cv_refl.
Qed.

Lemma choice_sum : forall IT C X E, closed IT -> closed C -> closed X -> closed E ->
  conv (TInterp IT (TIChoice E C) X)
    (TSigma (fresh [IT; E; C; X]) (TEnumT E) (TInterp IT (TApp C (TVar (fresh [IT; E; C; X]))) X)) /\
  forall m, subst (enum_position m) (fresh [IT; E; C; X]) (TInterp IT (TApp C (TVar (fresh [IT; E; C; X]))) X)
    = TInterp IT (TApp C (enum_position m)) X.
Proof.
  intros IT C X E HIT HC HX HE; split; [apply conv_root; reflexivity|].
  intros m; rewrite subst_interp, subst_app, subst_var_same.
  rewrite (subst_not_free IT), (subst_not_free C), (subst_not_free X) by (apply closed_not_in; assumption).
  reflexivity.
Qed.

Lemma row_enum_code : forall rs, row_enum rs = code (row_names rs).
Proof. induction rs as [|[s D] rs IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma row_names_nth : forall rs m name D, nth_error rs m = Some (name, D) -> nth_error (row_names rs) m = Some name.
Proof. intros rs m name D H; unfold row_names; rewrite nth_error_map, H; reflexivity. Qed.

Lemma row_handlers_at : forall Gamma IT X Y target source hs,
  row_handlers Gamma IT X Y target source hs ->
  forall n name D, nth_error source n = Some (name, D) ->
  exists h, nth_error hs n = Some h /\
    ((exists m D', nth_error target m = Some (name, D') /\ conv (TInterp IT D X) (TInterp IT D' X) /\
        h = retag_handler m) \/
     (exists d, dead Gamma IT D X d /\ h = dead_handler 0 Y d)).
Proof.
  intros Gamma IT X Y target source hs H; induction H; intros [|j] tag C Hnth; cbn [nth_error] in Hnth; try discriminate.
  - inversion Hnth; subst. exists (retag_handler n); split; [reflexivity|left; exists n, D'; repeat split; assumption].
  - cbn [nth_error]; eapply IHrow_handlers; eassumption.
  - inversion Hnth; subst. exists (dead_handler 0 Y d); split; [reflexivity|right; exists d; split; [assumption|reflexivity]].
  - cbn [nth_error]; eapply IHrow_handlers; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Realizability of description coercions *)

Lemma identity_for_closed : forall ts, closed (identity_for ts).
Proof.
  intros ts; unfold identity_for; apply closed_lam_of; intros y Hy; cbn in Hy; destruct Hy as [Hy|[]]; congruence.
Qed.
Lemma identity_for_app : forall ts t, conv (TApp (identity_for ts) t) t.
Proof. intros; unfold identity_for; eapply cv_trans; [apply beta_conv|]; rewrite subst_var_same; apply cv_refl. Qed.

Lemma retag_handler_closed : forall n, closed (retag_handler n).
Proof.
  intros n; unfold retag_handler; apply closed_lam_of; intros y Hy; cbn [free_vars] in Hy.
  rewrite in_app_iff in Hy; destruct Hy as [Hy|Hy];
    [exact (False_ind _ (closed_not_in _ _ (closed_position n) Hy))|cbn in Hy; destruct Hy as [Hy|[]]; congruence].
Qed.

Lemma inst_app_closed : forall g f a, closed a -> instantiate g (TApp f a) = TApp (instantiate g f) a.
Proof. intros g f a Ha; rewrite instantiate_app, (instantiate_closed g a) by exact Ha; reflexivity. Qed.

(* Output of an applied instantiated coercion, by an open conversion law. *)
Lemma inst_app_conv : forall g f a u, closed a -> conv (TApp f a) u ->
  conv (TApp (instantiate g f) a) (instantiate g u).
Proof. intros g f a u Ha H; rewrite <- inst_app_closed by exact Ha; apply instantiate_conversion, H. Qed.

Lemma eq_graph_intro : forall A B a b, rty A B -> closed a -> closed b -> rel_at a a A A -> conv a b ->
  eq_graph A B a b.
Proof.
  intros A B a b HAB Ha Hb Haa Hab; refine (conj Ha (conj Hb _)).
  eapply rel_at_conv; [apply rel_at_rty_both; [exact Haa|exact HAB]|apply cv_refl|exact Hab|apply cv_refl|apply cv_refl].
Qed.

Lemma desc_input_types : forall Gamma IT D X, description_input Gamma IT D X ->
  typing Gamma (TInterp IT D X) (TSort 0).
Proof. intros Gamma IT D X [H1 [H2 H3]]; apply ty_interp; assumption. Qed.

Lemma tyw_inst0 : forall Gamma g T, closing2 Gamma g g -> typing Gamma T (TSort 0) -> tyw (instantiate g T).
Proof. intros; eapply tyw_inst; [eassumption|exists 0; assumption]. Qed.

Lemma row_branches_free : forall IT rs x, In x (free_vars (row_branches IT rs)) ->
  In x (free_vars IT) \/ In x (free_vars (row_tuple rs)).
Proof.
  intros IT rs x H; unfold row_branches in H; cbn [free_vars] in H.
  rewrite in_remove_iff in H; destruct H as [H Hne]. rewrite row_enum_closed in H.
  repeat rewrite in_app_iff in H. cbn [In] in H.
  destruct H as [[]|[H|[H|[H|[]]]]]; [rewrite in_remove_iff in H; left; tauto|right; exact H|congruence].
Qed.

Lemma row_branches_scoped : forall Gamma IT rs, typing Gamma IT (TSort 0) -> row_input Gamma IT rs ->
  scoped Gamma (row_branches IT rs).
Proof.
  intros Gamma IT rs HIT [_ [_ Hrows]] x Hx.
  destruct (row_branches_free _ _ _ Hx) as [HI|HR]; [exact (typing_scoped _ _ _ HIT x HI)|].
  destruct (row_tuple_free _ _ HR) as [D [HD HxD]].
  apply in_map_iff in HD; destruct HD as [[s D'] [<- Hin]].
  eapply (typing_scoped _ _ _ (proj1 (Forall_forall _ _) Hrows _ Hin)); exact HxD.
Qed.

(* The source of a row coercion is an enum-tagged sum indexed by row names. *)
Lemma row_sum : forall Gamma g IT D X rs, closing2 Gamma g g -> row_view Gamma IT D rs ->
  typing Gamma X (Family IT) ->
  exists z P, conv (instantiate g (TInterp IT D X)) (TSigma z (TEnumT (row_enum rs)) P) /\
    forall m name Dm, nth_error rs m = Some (name, Dm) ->
      conv (subst (enum_position m) z P) (instantiate g (TInterp IT Dm X)).
Proof.
  intros Gamma g IT D X rs Hc Hv HX. destruct Hv as [rs Hin HD Hcode].
  pose proof Hin as [HIT _].
  destruct (closing2_closed _ _ _ Hc) as [Hg _].
  assert (HCs : closed (instantiate g (row_branches IT rs))).
  { exact (proj1 (inst_closed _ _ _ _ Hc (row_branches_scoped _ _ _ HIT Hin))). }
  pose proof (inst_closed1 _ _ _ _ Hc HIT) as HITc. pose proof (inst_closed1 _ _ _ _ Hc HX) as HXc.
  assert (HE : closed (row_enum rs)) by (unfold closed; apply row_enum_closed).
  destruct (choice_sum _ _ _ _ HITc HCs HXc HE) as [Hsum Hsub].
  eexists; eexists; split.
  - rewrite inst_tinterp. eapply cv_trans; [|exact Hsum].
    apply cv_compatible, cp_TInterp; [apply cv_refl| |apply cv_refl].
    eapply cv_trans; [apply instantiate_conversion, Hcode|].
    unfold row_code; rewrite inst_ichoice, (instantiate_closed g (row_enum rs)) by apply row_enum_closed.
    apply cv_refl.
  - intros m name Dm Hm. rewrite Hsub, inst_tinterp.
    apply cv_compatible, cp_TInterp; [apply cv_refl| |apply cv_refl].
    rewrite <- inst_app_closed by apply closed_position.
    apply instantiate_conversion. eapply row_branches_position; exact Hm.
Qed.

Lemma row_nth_typed : forall Gamma IT rs m name Dm, row_input Gamma IT rs ->
  nth_error rs m = Some (name, Dm) -> typing Gamma Dm (TIDesc IT).
Proof.
  intros Gamma IT rs m name Dm [_ [_ Hrows]] Hm.
  exact (proj1 (Forall_forall _ _) Hrows _ (nth_error_In _ _ Hm)).
Qed.

Lemma row_nth_exists : forall (rs : row) m, m < List.length (row_names rs) ->
  exists name Dm, nth_error rs m = Some (name, Dm).
Proof.
  intros rs m Hm; unfold row_names in Hm; rewrite length_map in Hm.
  destruct (nth_error rs m) as [[name Dm]|] eqn:E; [eauto|apply nth_error_None in E; lia].
Qed.

Theorem desc_real : forall Gamma IT D D' X q, desc_sub Gamma IT D D' X q -> forall g, closing2 Gamma g g ->
  exists Gp, Gr (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D' X)) Gp /\
    forall xs, closed xs -> rel_at xs xs (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D X)) ->
      Gp xs (TApp (instantiate g q) xs).
Proof.
  intros Gamma IT D D' X q H g Hc. pose proof (desc_sub_typed _ _ _ _ _ _ H) as Hq.
  destruct H as [Gamma IT D D' X Hi Hi' Hconv
                |Gamma IT D D' X d Hd Hi'
                |Gamma IT D D' X rs rt hs Hi Hi' Hvs Hvt Hh].
  - pose proof (tyw_inst0 _ _ _ Hc (desc_input_types _ _ _ _ Hi)) as HS.
    assert (HST : rty (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D' X))).
    { apply tyw_conv; [exact HS|]. apply instantiate_conversion, cv_compatible, cp_TInterp; [apply cv_refl|exact Hconv|apply cv_refl]. }
    exists (eq_graph (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D' X))); split; [apply gr_eq, HST|].
    intros xs Hxs Hxx. rewrite (instantiate_closed g (identity_for _)) by apply identity_for_closed.
    apply eq_graph_intro; [exact HST|exact Hxs|apply closed_app; [apply identity_for_closed|exact Hxs]|exact Hxx|].
    apply cv_sym, identity_for_app.
  - exists empty_rel; split.
    + apply gr_empty; [exact (tyw_inst0 _ _ _ Hc (desc_input_types _ _ _ _ (dead_input _ _ _ _ _ Hd)))
        |exact (tyw_inst0 _ _ _ Hc (desc_input_types _ _ _ _ Hi'))|].
      intros t u Ht; exact (dead_empty _ _ _ _ _ _ Hd Hc t u Ht).
    + intros xs Hxs Hxx; exfalso; exact (dead_empty _ _ _ _ _ _ Hd Hc xs xs Hxs Hxx).
  - pose proof Hi as [HIT [HDt HX]].
    pose proof (desc_input_types _ _ _ _ Hi) as HTS. pose proof (desc_input_types _ _ _ _ Hi') as HTT.
    pose proof (tyw_inst0 _ _ _ Hc HTS) as HTSw. pose proof (tyw_inst0 _ _ _ Hc HTT) as HTTw.
    destruct (row_sum _ g _ _ _ _ Hc Hvs HX) as [zs [Ps [HSs HPs]]].
    destruct (row_sum _ g _ _ _ _ Hc Hvt HX) as [zt [Pt [HSt HPt]]].
    destruct Hvs as [rs Hin _ _]. destruct Hvt as [rt Hint _ _]. pose proof Hint as [_ [HNt _]].
    assert (Hlive : forall m name Dm n D'', nth_error rs m = Some (name, Dm) -> nth_error rt n = Some (name, D'') ->
      conv (TInterp IT Dm X) (TInterp IT D'' X) ->
      rty (subst (enum_position m) zs Ps) (subst (enum_position n) zt Pt)).
    { intros m name Dm n D'' Hm Hn Hcv.
      pose proof (tyw_inst0 _ _ _ Hc (ty_interp HIT (row_nth_typed _ _ _ _ _ _ Hin Hm) HX)) as Hw.
      eapply rty_conv; [exact (tyw_rty _ Hw)|apply cv_sym, (HPs _ _ _ Hm)|].
      eapply cv_trans; [apply instantiate_conversion, Hcv|apply cv_sym, (HPt _ _ _ Hn)]. }
    exists (sum_graph (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D' X)) zs Ps zt Pt
      (row_names rs) (row_names rt)). split.
    + eapply gr_sum; [exact HTSw|exact HTTw|exact HSs|rewrite row_enum_code; apply cv_refl
        |exact HSt|rewrite row_enum_code; apply cv_refl|exact HNt|].
      intros m Hm. destruct (row_nth_exists _ _ Hm) as [name [Dm Hnth]].
      destruct (row_handlers_at _ _ _ _ _ _ _ Hh _ _ _ Hnth) as [h [Hhm [(n & D'' & Hn & Hcv & ->)|(d & Hd & ->)]]].
      * left. exists n, name; repeat apply conj; [eapply row_names_nth; exact Hnth|eapply row_names_nth; exact Hn|].
        eapply Hlive; eassumption.
      * right. intros t u Ht Htu. apply (dead_empty _ _ _ _ _ _ Hd Hc t u Ht).
        eapply rel_at_conv; [exact Htu|apply cv_refl|apply cv_refl|apply (HPs _ _ _ Hnth)|apply (HPs _ _ _ Hnth)].
    + intros p Hp Hpp.
      destruct (sum_rel_iff _ _ _ _ _ _ _ _ (row_names rs) (tyw_rty _ HTSw) HSs
        ltac:(rewrite row_enum_code; apply cv_refl) HSs) as [_ [_ Hiff]].
      destruct (proj1 (Hiff p p) Hpp) as (m & v & v2 & Hm & Hv & Hv2 & Hpc & _ & Hvv).
      destruct (row_nth_exists _ _ Hm) as [name [Dm Hnth]].
      destruct (row_handlers_at _ _ _ _ _ _ _ Hh _ _ _ Hnth) as [h [Hhm [(n & D'' & Hn & Hcv & ->)|(d & Hd & ->)]]].
      * destruct (coe_app _ _ _ _ _ p Hc Hq (ex_intro _ 0 HTS) (ex_intro _ 0 HTT) Hp Hpp) as [Hout Hoo].
        assert (Hconv : conv (TApp (instantiate g (row_map 0 IT rs X (TInterp IT D' X) hs)) p)
          (TPair (enum_position n) v)).
        { eapply cv_trans; [apply conv_app_a, Hpc|].
          eapply cv_trans; [apply inst_app_conv; [apply closed_pair; [apply closed_position|exact Hv]|eapply row_map_selected; eassumption]|].
          rewrite (instantiate_closed g (TApp (retag_handler n) v)) by (apply closed_app; [apply retag_handler_closed|exact Hv]).
          apply retag_handler_beta. }
        refine (conj Hp (conj Hout (conj Hpp (conj Hoo _)))).
        exists m, n, name, v, v; repeat apply conj; try assumption;
          [eapply row_names_nth; exact Hnth|eapply row_names_nth; exact Hn|].
        eapply rel_at_retype; [exact (rel_at_left_of _ _ _ _ Hvv)|apply tyw_rty, (rty_tyw_l _ _ (Hlive _ _ _ _ _ Hnth Hn Hcv))|].
        exact (Hlive _ _ _ _ _ Hnth Hn Hcv).
      * exfalso. apply (dead_empty _ _ _ _ _ _ Hd Hc v v Hv).
        eapply rel_at_conv; [exact (rel_at_left_of _ _ _ _ Hvv)|apply cv_refl|apply cv_refl|apply (HPs _ _ _ Hnth)|apply (HPs _ _ _ Hnth)].
Qed.

(* ------------------------------------------------------------------ *)
(* Realizability of coercions *)

Lemma away_not_dom : forall g y, closed_away g y -> ~ In y (map fst g).
Proof.
  intros g y H; induction H as [|[z u] g [Hne _] _ IH]; cbn; [tauto|].
  intros [E|E]; [exact (Hne E)|exact (IH E)].
Qed.

Lemma inst_open_closed : forall Gamma g y A' d T, closing2 Gamma g g -> fresh_in Gamma y ->
  typing (extend Gamma y A') d T -> closed (TLam y (instantiate g d)).
Proof.
  intros Gamma g y A' d T Hc Hy Hd. destruct (closing2_closed _ _ _ Hc) as [Hg _].
  apply closed_lam_of; intros z Hz.
  destruct (inst_free _ _ _ Hg Hz) as [Hzd Hzg].
  destruct (typing_scoped _ _ _ Hd z Hzd) as [B HB].
  destruct (Nat.eq_dec z y) as [->|Hne]; [reflexivity|].
  rewrite lookup_extend_other in HB by (intro E; apply Hne; symmetry; exact E).
  exfalso; apply Hzg, (proj1 (closing2_dom _ _ _ Hc _ _ HB)).
Qed.

Lemma Bot_tyw : tyw Bot.
Proof. exists 0, (enum_rel 0); exact (enum_interp TNilE TNilE [] (cv_refl _) (cv_refl _)). Qed.

Theorem sub_real : forall Gamma A B c, sub Gamma A B c -> forall g, closing2 Gamma g g ->
  exists G, Gr (instantiate g A) (instantiate g B) G /\
    forall a, closed a -> rel_at a a (instantiate g A) (instantiate g A) -> G a (TApp (instantiate g c) a).
Proof.
  intros Gamma A B c H; induction H as
    [Gamma A B HA HB Hconv
    |Gamma A B C c d H1 IH1 H2 IH2
    |Gamma A k HA
    |Gamma x y A B A' B' c d Hy HP HP' Hc1 IHc Hd1 IHd
    |Gamma IT F H G i q HinF HinH Hdq];
    intros g Hc; destruct (closing2_closed _ _ _ Hc) as [Hg _].
  - pose proof (tyw_inst _ _ _ Hc HA) as HAw.
    assert (HAB : rty (instantiate g A) (instantiate g B)) by (apply tyw_conv; [exact HAw|apply instantiate_conversion, Hconv]).
    exists (eq_graph (instantiate g A) (instantiate g B)); split; [apply gr_eq, HAB|].
    intros a Ha Haa. rewrite (instantiate_closed g (identity_for _)) by apply identity_for_closed.
    apply eq_graph_intro; [exact HAB|exact Ha|apply closed_app; [apply identity_for_closed|exact Ha]|exact Haa|].
    apply cv_sym, identity_for_app.
  - destruct (IH1 g Hc) as [G1 [HG1 R1]]; destruct (IH2 g Hc) as [G2 [HG2 R2]].
    destruct (Gr_comp _ _ _ _ _ HG1 HG2) as [G3 [HG3 Hi]].
    exists G3; split; [exact HG3|]. intros a Ha Haa.
    pose proof (R1 a Ha Haa) as Ham. destruct (Gr_typed _ _ _ _ _ HG1 Ham) as [_ [Hm [_ Hmm]]].
    pose proof (R2 _ Hm Hmm) as Hmb. pose proof (Hi _ _ _ Ham Hmb) as Hab.
    destruct (Gr_typed _ _ _ _ _ HG3 Hab) as [_ [Hb [_ Hbb]]].
    pose proof (sub_typed _ _ _ _ (su_trans H1 H2)) as Ht.
    eapply Gr_closure; [exact HG3|exact Hab|exact Ha|apply closed_app; [eapply inst_closed1; [exact Hc|exact Ht]|exact Ha]|exact Haa|].
    eapply rel_at_conv; [exact Hbb|apply cv_refl| |apply cv_refl|apply cv_refl].
    apply cv_sym. eapply cv_trans; [apply inst_app_conv; [exact Ha|apply compose_coercion_beta]|].
    rewrite instantiate_app, inst_app_closed by exact Ha. apply cv_refl.
  - exists empty_rel; split.
    + rewrite (instantiate_closed g Bot) by reflexivity. apply gr_empty; [exact Bot_tyw|exact (tyw_inst _ _ _ Hc (ex_intro _ k HA))|].
      intros t u _; apply Bot_empty.
    + intros a _ Haa; rewrite (instantiate_closed g Bot) in Haa by reflexivity; exact (Bot_empty _ _ Haa).
  - destruct (closing2_away _ _ _ _ Hc Hy) as [Hay _].
    pose proof (away_not_dom _ _ Hay) as Hyg.
    pose proof (sub_typed _ _ _ _ Hc1) as Htc.
    pose proof (sub_typed _ _ _ _ Hd1) as Htd.
    assert (Htp : typing Gamma (pi_coercion y c d) (arrow (TPi x A B) (TPi y A' B'))) by (apply sub_typed; apply su_pi; assumption).
    pose proof (typing_context _ _ _ Htd) as Hwf.
    pose proof (inst_closed1 _ _ _ _ Hc Htc) as Hcc.
    pose proof (inst_open_closed _ _ _ _ _ _ Hc Hy Htd) as HDc.
    pose proof (typing_fresh_not_free _ _ _ _ Htc Hy) as Hyc.
    pose proof (tyw_inst _ _ _ Hc HP) as HPw. pose proof (tyw_inst _ _ _ Hc HP') as HP'w.
    rewrite inst_pi in HPw by exact Hg. rewrite inst_pi, (drop_away g y) in HP'w by assumption.
    destruct HP as [kP HPt].
    set (V := instantiate (drop x g) B) in *. set (V' := instantiate g B') in *.
    destruct (pi_rty _ _ _ _ _ _ _ _ (tyw_rty _ HPw) (cv_refl _) (cv_refl _)) as [_ HVrel].
    destruct (IHc g Hc) as [Gd [HGd Rd]].
    assert (Hfd : forall a' a, Gd a' a -> rel_at a (TApp (instantiate g c) a') (instantiate g A) (instantiate g A)).
    { intros a' a Hd'. destruct (Gr_typed _ _ _ _ _ HGd Hd') as [Ha' [Ha [Ha'a' _]]].
      exact (Gr_func _ _ _ HGd _ HGd _ _ _ _ Hd' (Rd a' Ha' Ha'a') Ha'a'). }
    assert (Hcodom : forall a' a, Gd a' a -> exists G0, Gr (subst a x V) (subst a' y V') G0 /\
      forall t, closed t -> rel_at t t (subst a x V) (subst a x V) -> G0 t (TApp (instantiate ((y, a') :: g) d) t)).
    { intros a' a Hd'. destruct (Gr_typed _ _ _ _ _ HGd Hd') as [Ha' [Ha [Ha'a' Haa]]].
      pose proof (closing2_extend _ _ _ _ _ _ _ Hc Hy Hwf Ha' Ha' Ha'a') as Hc'.
      destruct (IHd _ Hc') as [G0 [HG0 R0]].
      assert (Hca' : closed (TApp (instantiate g c) a')) by (apply closed_app; assumption).
      assert (Hsrc : conv (instantiate ((y, a') :: g) (coerced_codomain x y c B)) (subst (TApp (instantiate g c) a') x V)).
      { unfold coerced_codomain.
        eapply cv_trans; [apply inst_cons_conv; [exact Hg|exact Hay|exact Ha']|].
        eapply cv_trans; [apply conv_subst, cv_alpha, inst_subst, Hg|].
        rewrite instantiate_app, (inst_var_absent g y) by exact Hyg.
        destruct (Nat.eq_dec y x) as [<-|Hne].
        - eapply cv_trans; [apply cv_alpha, subst_subst_same|].
          rewrite subst_app, subst_var_same, (subst_not_free (instantiate g c)) by (apply closed_not_in; exact Hcc).
          apply cv_refl.
        - eapply cv_trans; [apply cv_alpha, subst_subst_closed; [exact Ha'|exact Hne]|].
          rewrite subst_app, subst_var_same, (subst_not_free (instantiate g c)) by (apply closed_not_in; exact Hcc).
          rewrite (subst_not_free V); [apply cv_refl|].
          intros Hin. destruct (inst_free _ _ _ (drop_closed _ _ Hg) Hin) as [HinB _].
          apply (typing_fresh_not_free _ _ _ _ HPt Hy). cbn [free_vars].
          rewrite in_app_iff, in_remove_iff; right; split; [exact HinB|exact Hne]. }
      assert (Htgt : conv (instantiate ((y, a') :: g) B') (subst a' y V')) by (apply inst_cons_conv; assumption).
      pose proof (Hfd _ _ Hd') as Hac.
      assert (HVa : rty (subst (TApp (instantiate g c) a') x V) (subst a x V))
        by (apply HVrel; [exact Hca'|exact Ha|apply rel_at_sym, Hac]).
      assert (Hs : rty (instantiate ((y, a') :: g) (coerced_codomain x y c B)) (subst a x V)).
      { eapply rty_trans; [apply tyw_conv; [exact (proj1 (Gr_tyw _ _ _ HG0))|exact Hsrc]|exact HVa]. }
      assert (Ht : rty (instantiate ((y, a') :: g) B') (subst a' y V'))
        by (apply tyw_conv; [exact (proj2 (Gr_tyw _ _ _ HG0))|exact Htgt]).
      exists G0; split; [eapply Gr_transport; eassumption|].
      intros t Ht0 Htt. apply R0; [exact Ht0|]. eapply rel_at_retype; [exact Htt|apply rty_sym, Hs|apply rty_sym, Hs]. }
    assert (Hpi1 : instantiate g (TPi x A B) = TPi x (instantiate g A) V) by (apply inst_pi, Hg).
    assert (Hpi2 : instantiate g (TPi y A' B') = TPi y (instantiate g A') V')
      by (unfold V'; rewrite inst_pi, (drop_away g y) by assumption; reflexivity).
    rewrite Hpi1, Hpi2.
    exists (pi_graph (TPi x (instantiate g A) V) (TPi y (instantiate g A') V') Gd
      (fun a' a => canonG (subst a x V) (subst a' y V'))). split.
    + eapply gr_pi with (c := instantiate g c) (D := TLam y (instantiate g d));
        [exact HPw|exact HP'w|apply cv_refl|apply cv_refl|exact HGd|exact Hcc|exact Rd| |exact HDc|].
      * intros a' a Hd'. destruct (Hcodom a' a Hd') as [G0 [HG0 _]]. exact (canonG_gr _ _ _ HG0).
      * intros a' a t Hd' Ht Htt. destruct (Hcodom a' a Hd') as [G0 [HG0 R0]].
        destruct (Gr_typed _ _ _ _ _ HGd Hd') as [Ha' _].
        pose proof (R0 t Ht Htt) as Hr. destruct (Gr_typed _ _ _ _ _ HG0 Hr) as [_ [Ho [_ Hoo]]].
        exists G0; split; [exact HG0|].
        eapply Gr_closure; [exact HG0|exact Hr|exact Ht|apply closed_app; [apply closed_app; assumption|exact Ht]|exact Htt|].
        eapply rel_at_conv; [exact Hoo|apply cv_refl| |apply cv_refl|apply cv_refl].
        apply conv_app_f. eapply cv_trans; [apply inst_cons_conv; assumption|]. apply cv_sym, beta_conv.
    + intros f Hf Hff.
      assert (Hff' : rel_at f f (instantiate g (TPi x A B)) (instantiate g (TPi x A B))) by (rewrite Hpi1; exact Hff).
      destruct (coe_app _ _ _ _ _ f Hc Htp (ex_intro _ kP HPt) HP' Hf Hff') as [Ho Hoo].
      rewrite Hpi2 in Hoo.
      refine (conj Hf (conj Ho (conj Hff (conj Hoo _)))).
      intros a' a Hd'. destruct (Hcodom a' a Hd') as [G0 [HG0 R0]].
      destruct (Gr_typed _ _ _ _ _ HGd Hd') as [Ha' [Ha [Ha'a' Haa]]].
      pose proof (Hfd _ _ Hd') as Hac.
      assert (Hca' : closed (TApp (instantiate g c) a')) by (apply closed_app; assumption).
      pose proof (HVrel _ _ Hca' Ha (rel_at_sym _ _ _ _ Hac)) as HVa.
      assert (Hct : closed (TApp f (TApp (instantiate g c) a'))) by (apply closed_app; assumption).
      assert (Htf : rel_at (TApp f (TApp (instantiate g c) a')) (TApp f a) (subst a x V) (subst a x V)).
      { eapply rel_at_retype; [eapply pi_app_rel; [exact Hff|apply cv_refl|apply cv_refl|exact Hca'|exact Ha|apply rel_at_sym, Hac]
          |exact HVa|apply tyw_rty; exact (rty_tyw_r _ _ HVa)]. }
      pose proof (R0 _ Hct (rel_at_left_of _ _ _ _ Htf)) as Hr.
      destruct (Gr_typed _ _ _ _ _ HG0 Hr) as [_ [Hro [_ Hroo]]].
      exists G0; split; [exact HG0|].
      eapply Gr_closure; [exact HG0|exact Hr|apply closed_app; assumption|apply closed_app; assumption|exact Htf|].
      eapply rel_at_conv; [exact Hroo|apply cv_refl| |apply cv_refl|apply cv_refl].
      apply cv_sym.
      rewrite <- (inst_app_closed g (pi_coercion y c d) f) by exact Hf.
      rewrite <- (inst_app_closed g (TApp (pi_coercion y c d) f) a') by exact Ha'.
      eapply cv_trans; [apply instantiate_conversion, pi_coercion_beta; assumption|].
      rewrite (subst_fresh c) by exact Hyc.
      rewrite !instantiate_app, (instantiate_closed g f) by exact Hf.
      rewrite (instantiate_closed g a') by exact Ha'.
      apply conv_app; [|apply cv_refl].
      eapply cv_trans; [apply cv_alpha, inst_subst, Hg|].
      rewrite (instantiate_closed g a') by exact Ha'. rewrite (drop_away g y) by exact Hay.
      apply cv_sym, inst_cons_conv; assumption.
  - assert (Hsub : sub Gamma (CloseAt IT F G i) (CloseAt IT H G i) (close_coercion IT F H G i q)) by (apply su_close; assumption).
    pose proof (sub_typed _ _ _ _ Hsub) as Ht.
    destruct (subtyping_formations _ _ _ _ Hsub) as [HwF HwH].
    destruct (desc_real _ _ _ _ _ _ Hdq g Hc) as [Gp [HGp Rp]].
    change (TInterp IT (TApp F i) (carrier IT G)) with (payload IT F G i) in HGp, Rp.
    change (TInterp IT (TApp H i) (carrier IT G)) with (payload IT H G i) in HGp.
    rewrite (inst_payload g IT F G i), (inst_payload g IT H G i) in HGp. rewrite (inst_payload g IT F G i) in Rp.
    exists (roll_graph (instantiate g (CloseAt IT F G i)) (instantiate g (CloseAt IT H G i)) Gp). split.
    + eapply gr_roll with (IT := instantiate g IT) (F := instantiate g F) (G := instantiate g G) (i := instantiate g i)
        (IT' := instantiate g IT) (F' := instantiate g H) (G' := instantiate g G) (i' := instantiate g i);
        [exact (tyw_inst _ _ _ Hc HwF)|exact (tyw_inst _ _ _ Hc HwH)|rewrite inst_CloseAt; apply cv_refl
        |rewrite inst_CloseAt; apply cv_refl|exact HGp].
    + intros a Ha Haa.
      assert (HcF : conv (instantiate g (CloseAt IT F G i))
        (CloseAt (instantiate g IT) (instantiate g F) (instantiate g G) (instantiate g i))) by (rewrite inst_CloseAt; apply cv_refl).
      destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ (tyw_rty _ (tyw_inst _ _ _ Hc HwF)) HcF HcF) as [_ Hiff].
      destruct (proj1 (Hiff a a) Haa) as (v & v2 & Hv & Hv2 & Hav & _ & Hvv).
      destruct (coe_app _ _ _ _ _ a Hc Ht HwF HwH Ha Haa) as [Ho Hoo].
      pose proof (Rp v Hv (rel_at_left_of _ _ _ _ Hvv)) as Hgp.
      destruct (Gr_typed _ _ _ _ _ HGp Hgp) as [_ [Hqv _]].
      refine (conj Ha (conj Ho (conj Haa (conj Hoo _)))).
      exists v, (TApp (instantiate g q) v); repeat apply conj; try assumption.
      eapply cv_trans; [apply inst_app_conv; [exact Ha|apply close_coercion_beta]|].
      rewrite inst_tin, instantiate_app. apply conv_in, conv_app_a.
      unfold unroll. rewrite inst_ccase, (instantiate_closed g a) by exact Ha.
      rewrite (instantiate_closed g identity) by reflexivity.
      eapply cv_trans; [apply cv_compatible, cp_TCloseCase; [apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|apply cv_refl|exact Hav]|].
      eapply cv_trans; [apply conv_root; reflexivity|]. apply conv_root; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Coherence of coercions *)

Lemma coercions_related : forall Gamma A B c d, sub Gamma A B c -> sub Gamma A B d ->
  forall g1 g2, closing2 Gamma g1 g2 ->
  rel_at (instantiate g1 c) (instantiate g2 d) (instantiate g1 (arrow A B)) (instantiate g2 (arrow A B)).
Proof.
  intros Gamma A B c d Hc Hd g1 g2 H12.
  pose proof (sub_typed _ _ _ _ Hc) as Htc.
  destruct (subtyping_formations _ _ _ _ Hc) as [HA HB].
  pose proof (closing2_refl_r _ _ _ H12) as H22.
  destruct (closing2_closed _ _ _ H22) as [Hg2 _].
  pose proof (rel_fundamental _ _ _ Htc _ _ H12) as F1.
  eapply rel_at_trans; [exact F1|].
  pose proof (closed_type_inst _ _ _ H22 HA) as HAc. pose proof (closed_type_inst _ _ _ H22 HB) as HBc.
  assert (Harr : conv (instantiate g2 (arrow A B)) (arrow (instantiate g2 A) (instantiate g2 B)))
    by (apply inst_arrow; assumption).
  destruct (rel_at_tyw _ _ _ _ (rel_at_right_of _ _ _ _ F1)) as [[k [R HR]] _].
  eapply rel_at_conv; [|apply cv_refl|apply cv_refl|apply cv_sym, Harr|apply cv_sym, Harr].
  eapply sem_arrow_lam with (k := k); [exists R; eapply interp_conv; [exact HR|exact Harr|exact Harr]|].
  intros a1 a2 Ha1 Ha2 Ha.
  destruct (sub_real _ _ _ _ Hc g2 H22) as [Gc [HGc Rc]].
  destruct (sub_real _ _ _ _ Hd g2 H22) as [Gd [HGd Rd]].
  exact (Gr_func _ _ _ HGc _ HGd _ _ _ _ (Rc a1 Ha1 (rel_at_left_of _ _ _ _ Ha))
    (Rd a2 Ha2 (rel_at_right_of _ _ _ _ Ha)) Ha).
Qed.

Theorem coercion_coherence_rel : forall Gamma A B c d,
  sub Gamma A B c -> sub Gamma A B d -> observational_eq Gamma (arrow A B) c d.
Proof.
  intros Gamma A B c d Hc Hd.
  apply rel_observational; [exact (sub_typed _ _ _ _ Hc)|exact (sub_typed _ _ _ _ Hd)|].
  apply coercions_related; assumption.
Qed.

Print Assumptions coercion_coherence_rel.
