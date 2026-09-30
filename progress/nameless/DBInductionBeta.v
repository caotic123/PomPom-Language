(* Computation of the induction operators, independently of full preservation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBClosePayload.
Import ListNotations.

Lemma def_application : forall Gamma IT F i,
  typing Gamma F (Def IT) -> typing Gamma i IT ->
  typing Gamma (TApp F i) (TIDesc IT).
Proof.
  intros Gamma IT F i HF Hi.
  pose proof (regular_application _ _ _ _ _ HF Hi) as H.
  cbn [Def subst] in H. now rewrite ?subst_lift_zero, ?lift_zero_id in H.
Qed.

Lemma close_method_application : forall Gamma IT G P st F i xs hs,
  typing Gamma st (close_ind_method IT G P) ->
  typing Gamma F (Def IT) -> typing Gamma i IT ->
  typing Gamma xs (payload IT F G i) ->
  typing Gamma hs (TIAll IT (TApp F i) (carrier IT G) xs (diagonal_motive G P)) ->
  typing Gamma (TApp (TApp (TApp (TApp st F) i) xs) hs)
    (TApp (TApp (TApp P F) i) (TIn xs)).
Proof.
  intros Gamma IT G P st F i xs hs Hst HF Hi Hxs Hhs.
  pose proof (regular_application _ _ _ _ _ Hst HF) as H1.
  cbn [close_ind_method payload carrier subst] in H1.
  rewrite ?subst_diagonal_motive, ?subst_lift_prefix in H1 by lia.
  rewrite ?lift_zero_id in H1. cbn [Nat.ltb Nat.leb Nat.eqb] in H1.
  pose proof (regular_application _ _ _ _ _ H1 Hi) as H2.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H2.
  rewrite ?subst_diagonal_motive, ?subst_lift_prefix, ?subst_lift_zero, ?lift_zero_id in H2 by lia.
  pose proof (regular_application _ _ _ _ _ H2 Hxs) as H3.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H3.
  rewrite ?subst_diagonal_motive, ?subst_lift_prefix, ?subst_lift_zero, ?lift_zero_id in H3 by lia.
  pose proof (regular_application _ _ _ _ _ H3 Hhs) as H4.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H4.
  now rewrite ?subst_lift_prefix, ?subst_lift_zero, ?lift_zero_id in H4 by lia.
Qed.

Lemma regular_lambda : forall Gamma A b B,
  type_wf Gamma A -> typing (A::Gamma) b B -> typing Gamma (TLam b) (TPi A B).
Proof.
  intros Gamma A b B [j HA] Hb.
  destruct (type_correctness _ _ _ Hb) as [k HB].
  eapply ty_lam; [eapply ty_pi; eassumption|exact Hb].
Qed.

Lemma recursive_method_intro : forall Gamma IT X P b,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing (TApp (lift 1 0 X) (TVar 0)::IT::Gamma) b
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))) ->
  typing Gamma (TLam (TLam b)) (recursive_method IT X P).
Proof.
  intros Gamma IT X P b HI HX Hb.
  apply regular_lambda; [exists 0; exact HI|].
  apply regular_lambda; [|exact Hb]. exists 0.
  pose proof (weakening _ _ _ _ _ HX HI) as HX'. rewrite lift_Family in HX'.
  assert (Hv : typing (IT::Gamma) (TVar 0) (lift 1 0 IT))
    by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
  exact (regular_application _ _ _ _ _ HX' Hv).
Qed.

Lemma diagonal_motive_application_conversion : forall G P i x,
  conv (TApp (diagonal_motive G P) (TPair i x))
    (TApp (TApp (TApp P G) i) x).
Proof.
  intros. eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  cbn [diagonal_motive subst]. rewrite ?subst_lift_zero, ?lift_zero_id.
  apply cv_compatible, cp_TApp; [apply cv_compatible, cp_TApp|];
    auto using cv_refl; apply cv_step, st_root; reflexivity.
Qed.

Lemma payload_formation : forall Gamma IT F G i,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma (payload IT F G i) (TSort 0).
Proof.
  intros. apply ty_interp; eauto using def_application, smart_close.
Qed.

Lemma regular_fst : forall Gamma A B p,
  typing Gamma p (TSigma A B) -> typing Gamma (TFst p) A.
Proof.
  intros Gamma A B p H. destruct (type_correctness _ _ _ H) as [k HS].
  eapply smart_fst; eassumption.
Qed.
Lemma regular_snd : forall Gamma A B p,
  typing Gamma p (TSigma A B) -> typing Gamma (TSnd p) (subst (TFst p) 0 B).
Proof.
  intros Gamma A B p H. destruct (type_correctness _ _ _ H) as [k HS].
  eapply smart_snd; eassumption.
Qed.

Lemma total_snd : forall Gamma IT X p,
  typing Gamma p (total IT X) -> typing Gamma (TSnd p) (TApp X (TFst p)).
Proof.
  intros Gamma IT X p H. pose proof (regular_snd _ _ _ _ H) as HS.
  cbn [total subst] in HS. now rewrite ?subst_lift_zero, ?lift_zero_id in HS.
Qed.

Lemma motive_formation : forall Gamma IT X,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing Gamma (motive IT X) (TSort 1).
Proof.
  intros. change (TSort 1) with (TSort (Nat.max 0 1)).
  apply ty_pi; eauto using total_formation, ty_sort, wf_cons, typing_context.
Qed.

Lemma diagonal_motive_typing : forall Gamma IT G P,
  typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
  typing Gamma P (close_motive IT G) ->
  typing Gamma (diagonal_motive G P) (motive IT (carrier IT G)).
Proof.
  intros Gamma IT G P HI HG HP.
  pose proof (smart_close _ _ _ _ HI HG HG) as HX.
  pose proof (total_formation _ _ _ HI HX) as HT.
  eapply ty_lam; [eapply motive_formation; eassumption|].
  pose proof (weakening _ _ _ _ _ HG HT) as HG'.
  pose proof (weakening _ _ _ _ _ HP HT) as HP'.
  rewrite lift_Def in HG'. rewrite lift_close_motive in HP'.
  assert (Hv : typing (total IT (carrier IT G)::Gamma) (TVar 0)
    (total (lift 1 0 IT) (carrier (lift 1 0 IT) (lift 1 0 G)))).
  { change (typing (total IT (carrier IT G)::Gamma) (TVar 0) (total (lift 1 0 IT) (lift 1 0 (carrier IT G)))).
    rewrite <- lift_total.
    apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]. }
  exact (close_motive_application _ _ _ _ _ _ _ HP' HG'
    (regular_fst _ _ _ _ Hv) (total_snd _ _ _ _ Hv)).
Qed.

Lemma close_case_beta : forall Gamma k IT F G i Q b xs,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma Q (TPi (CloseAt IT F G i) (TSort k)) ->
  typing Gamma b (close_case_method IT F G i Q) ->
  typing Gamma (TIn xs) (CloseAt IT F G i) ->
  typing Gamma (TApp b xs) (TApp Q (TIn xs)).
Proof.
  intros Gamma k IT F G i Q b xs HI HF HG Hi HQ Hb Hx.
  assert (Hxs : typing Gamma xs (payload IT F G i)).
  { eapply close_payload_generation; [exact Hx|reflexivity|apply cv_refl|].
    exists 0; eapply payload_formation; eassumption. }
  pose proof (regular_application _ _ _ _ _ Hb Hxs) as H.
  cbn [close_case_method subst] in H.
  now rewrite ?subst_lift_zero, ?lift_zero_id in H.
Qed.

Lemma weakening_two : forall Gamma A B t T j k,
  typing Gamma t T -> typing Gamma A (TSort j) -> typing (A::Gamma) B (TSort k) ->
  typing (B::A::Gamma) (lift 2 0 t) (lift 2 0 T).
Proof.
  intros Gamma A B t T j k H HA HB.
  pose proof (weakening _ _ _ _ _ (weakening _ _ _ _ _ H HA) HB) as H'.
  now rewrite !lift_fuse_zero in H' by lia.
Qed.

Lemma close_recursive_typing : forall Gamma IT G P st,
  typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
  typing Gamma P (close_motive IT G) -> typing Gamma st (close_ind_method IT G P) ->
  typing Gamma
    (TLam (TLam (TCloseInd (lift 2 0 IT) (lift 2 0 G)
      (lift 2 0 P) (lift 2 0 st) (lift 2 0 G) (TVar 1) (TVar 0))))
    (recursive_method IT (carrier IT G) (diagonal_motive G P)).
Proof.
  intros Gamma IT G P st HI HG HP HS.
  pose proof (smart_close _ _ _ _ HI HG HG) as HX.
  pose proof (diagonal_motive_typing _ _ _ _ HI HG HP) as HQ.
  pose proof (weakening _ _ _ _ _ HX HI) as HX1. rewrite lift_Family in HX1.
  assert (Hv : typing (IT::Gamma) (TVar 0) (lift 1 0 IT))
    by (apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity]).
  pose proof (regular_application _ _ _ _ _ HX1 Hv) as HA.
  apply recursive_method_intro; [exact HI|exact HX|].
  pose proof (weakening_two _ _ _ _ _ _ _ HI HI HA) as HI2.
  pose proof (weakening_two _ _ _ _ _ _ _ HG HI HA) as HG2.
  pose proof (weakening_two _ _ _ _ _ _ _ HP HI HA) as HP2.
  pose proof (weakening_two _ _ _ _ _ _ _ HS HI HA) as HS2.
  pose proof (weakening_two _ _ _ _ _ _ _ HQ HI HA) as HQ2.
  rewrite lift_Def in HG2. rewrite lift_close_motive in HP2.
  rewrite lift_close_ind_method in HS2.
  rewrite lift_diagonal_motive, lift_motive in HQ2.
  pose proof (weakening _ _ _ _ _ Hv HA) as Hindex.
  rewrite lift_fuse_zero in Hindex by lia.
  assert (Hvalue : typing (TApp (lift 1 0 (carrier IT G)) (TVar 0)::IT::Gamma)
    (TVar 0) (CloseAt (lift 2 0 IT) (lift 2 0 G) (lift 2 0 G) (TVar 1))).
  { pose proof (smart_var _ 0 _ (wf_cons _ _ _ (typing_context _ _ _ HA) HA) eq_refl) as H.
    cbn [lift] in H. rewrite !lift_fuse_zero in H by lia. exact H. }
  rewrite lift_diagonal_motive.
  eapply ty_conv.
  - eapply smart_close_ind; eassumption.
  - eapply motive_application; [exact HI2| |exact HQ2|exact Hindex|exact Hvalue].
    eapply smart_close; eassumption.
  - apply cv_sym, diagonal_motive_application_conversion.
Qed.

Theorem close_ind_beta : forall Gamma IT G P st F i xs,
  typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
  typing Gamma P (close_motive IT G) -> typing Gamma st (close_ind_method IT G P) ->
  typing Gamma F (Def IT) -> typing Gamma i IT ->
  typing Gamma (TIn xs) (CloseAt IT F G i) ->
  typing Gamma
    (TApp (TApp (TApp (TApp st F) i) xs)
      (THyps IT (TApp F i) (carrier IT G) (diagonal_motive G P)
        (TLam (TLam (TCloseInd (lift 2 0 IT) (lift 2 0 G)
          (lift 2 0 P) (lift 2 0 st) (lift 2 0 G) (TVar 1) (TVar 0)))) xs))
    (TApp (TApp (TApp P F) i) (TIn xs)).
Proof.
  intros Gamma IT G P st F i xs HI HG HP Hst HF Hi Hx.
  assert (Hxs : typing Gamma xs (payload IT F G i)).
  { eapply close_payload_generation; [exact Hx|reflexivity|apply cv_refl|].
    exists 0; eapply payload_formation; eassumption. }
  eapply close_method_application; try eassumption.
  eapply smart_hyps; eauto using def_application, smart_close,
    diagonal_motive_typing, close_recursive_typing.
Qed.

Theorem close_ind_reduction_preservation : forall Gamma t T,
  typing Gamma t T -> forall IT G P st F i x u,
  t = TCloseInd IT G P st F i x -> root_step t = Some u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros JT GG PP ss FF ii xx u Heq Hr; try discriminate.
  - eapply ty_conv; [eapply IHtyping1; eassumption|eassumption|eassumption].
  - eapply ty_cumul; [eapply IHtyping; eassumption|eassumption].
  - inversion Heq; subst. destruct xx; cbn [root_step] in Hr; try discriminate.
    inversion Hr; subst. eapply close_ind_beta; eassumption.
  - eapply ty_cumul_fun; [eapply IHtyping1; eassumption|eassumption|eassumption|eassumption|eassumption].
Qed.

Theorem close_case_reduction_preservation : forall Gamma t T,
  typing Gamma t T -> forall k IT F G i Q b x u,
  t = TCloseCase k IT F G i Q b x -> root_step t = Some u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros kk JT FF GG ii QQ bb xx u Heq Hr; try discriminate.
  - eapply ty_conv; [eapply IHtyping1; eassumption|eassumption|eassumption].
  - eapply ty_cumul; [eapply IHtyping; eassumption|eassumption].
  - inversion Heq; subst. destruct xx; cbn [root_step] in Hr; try discriminate.
    inversion Hr; subst. eapply close_case_beta with (IT:=JT) (F:=FF) (G:=GG) (i:=ii) (k:=kk); eassumption.
  - eapply ty_cumul_fun; [eapply IHtyping1; eassumption|eassumption|eassumption|eassumption|eassumption].
Qed.
