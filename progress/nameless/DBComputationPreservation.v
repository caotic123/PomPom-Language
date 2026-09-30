(* Full compatible computation, including every binder and annotation.
   Eta is kept separate so this preservation theorem has no eta premise. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBFullPreservation.
Import ListNotations.

Inductive computation : term -> term -> Prop :=
| cmp_root : forall t u, root_step t = Some u -> computation t u
| cmp_TPi_A : forall A B A', computation A A' ->
    computation (TPi A B) (TPi A' B)
| cmp_TPi_B : forall A B B', computation B B' ->
    computation (TPi A B) (TPi A B')
| cmp_TLam_b : forall b b', computation b b' ->
    computation (TLam b) (TLam b')
| cmp_TApp_f : forall f a f', computation f f' ->
    computation (TApp f a) (TApp f' a)
| cmp_TApp_a : forall f a a', computation a a' ->
    computation (TApp f a) (TApp f a')
| cmp_TSigma_A : forall A B A', computation A A' ->
    computation (TSigma A B) (TSigma A' B)
| cmp_TSigma_B : forall A B B', computation B B' ->
    computation (TSigma A B) (TSigma A B')
| cmp_TPair_a : forall a b a', computation a a' ->
    computation (TPair a b) (TPair a' b)
| cmp_TPair_b : forall a b b', computation b b' ->
    computation (TPair a b) (TPair a b')
| cmp_TFst_p : forall p p', computation p p' ->
    computation (TFst p) (TFst p')
| cmp_TSnd_p : forall p p', computation p p' ->
    computation (TSnd p) (TSnd p')
| cmp_TConsE_tag : forall tag E tag', computation tag tag' ->
    computation (TConsE tag E) (TConsE tag' E)
| cmp_TConsE_E : forall tag E E', computation E E' ->
    computation (TConsE tag E) (TConsE tag E')
| cmp_TEnumT_E : forall E E', computation E E' ->
    computation (TEnumT E) (TEnumT E')
| cmp_TESucc_n : forall n n', computation n n' ->
    computation (TESucc n) (TESucc n')
| cmp_TEPi_E : forall k E P E', computation E E' ->
    computation (TEPi k E P) (TEPi k E' P)
| cmp_TEPi_P : forall k E P P', computation P P' ->
    computation (TEPi k E P) (TEPi k E P')
| cmp_TSwitch_E : forall k E P p e E', computation E E' ->
    computation (TSwitch k E P p e) (TSwitch k E' P p e)
| cmp_TSwitch_P : forall k E P p e P', computation P P' ->
    computation (TSwitch k E P p e) (TSwitch k E P' p e)
| cmp_TSwitch_p : forall k E P p e p', computation p p' ->
    computation (TSwitch k E P p e) (TSwitch k E P p' e)
| cmp_TSwitch_e : forall k E P p e e', computation e e' ->
    computation (TSwitch k E P p e) (TSwitch k E P p e')
| cmp_TIDesc_IT : forall IT IT', computation IT IT' ->
    computation (TIDesc IT) (TIDesc IT')
| cmp_TIVar_i : forall i i', computation i i' ->
    computation (TIVar i) (TIVar i')
| cmp_TIProd_A : forall A B A', computation A A' ->
    computation (TIProd A B) (TIProd A' B)
| cmp_TIProd_B : forall A B B', computation B B' ->
    computation (TIProd A B) (TIProd A B')
| cmp_TIPi_A : forall A D A', computation A A' ->
    computation (TIPi A D) (TIPi A' D)
| cmp_TIPi_D : forall A D D', computation D D' ->
    computation (TIPi A D) (TIPi A D')
| cmp_TISig_A : forall A D A', computation A A' ->
    computation (TISig A D) (TISig A' D)
| cmp_TISig_D : forall A D D', computation D D' ->
    computation (TISig A D) (TISig A D')
| cmp_TIChoice_E : forall E D E', computation E E' ->
    computation (TIChoice E D) (TIChoice E' D)
| cmp_TIChoice_D : forall E D D', computation D D' ->
    computation (TIChoice E D) (TIChoice E D')
| cmp_TInterp_IT : forall IT D X IT', computation IT IT' ->
    computation (TInterp IT D X) (TInterp IT' D X)
| cmp_TInterp_D : forall IT D X D', computation D D' ->
    computation (TInterp IT D X) (TInterp IT D' X)
| cmp_TInterp_X : forall IT D X X', computation X X' ->
    computation (TInterp IT D X) (TInterp IT D X')
| cmp_TMuI_IT : forall IT D IT', computation IT IT' ->
    computation (TMuI IT D) (TMuI IT' D)
| cmp_TMuI_D : forall IT D D', computation D D' ->
    computation (TMuI IT D) (TMuI IT D')
| cmp_TIn_x : forall x x', computation x x' ->
    computation (TIn x) (TIn x')
| cmp_TInd_IT : forall IT D P s i x IT', computation IT IT' ->
    computation (TInd IT D P s i x) (TInd IT' D P s i x)
| cmp_TInd_D : forall IT D P s i x D', computation D D' ->
    computation (TInd IT D P s i x) (TInd IT D' P s i x)
| cmp_TInd_P : forall IT D P s i x P', computation P P' ->
    computation (TInd IT D P s i x) (TInd IT D P' s i x)
| cmp_TInd_s : forall IT D P s i x s', computation s s' ->
    computation (TInd IT D P s i x) (TInd IT D P s' i x)
| cmp_TInd_i : forall IT D P s i x i', computation i i' ->
    computation (TInd IT D P s i x) (TInd IT D P s i' x)
| cmp_TInd_x : forall IT D P s i x x', computation x x' ->
    computation (TInd IT D P s i x) (TInd IT D P s i x')
| cmp_TIAll_IT : forall IT D X x P IT', computation IT IT' ->
    computation (TIAll IT D X x P) (TIAll IT' D X x P)
| cmp_TIAll_D : forall IT D X x P D', computation D D' ->
    computation (TIAll IT D X x P) (TIAll IT D' X x P)
| cmp_TIAll_X : forall IT D X x P X', computation X X' ->
    computation (TIAll IT D X x P) (TIAll IT D X' x P)
| cmp_TIAll_x : forall IT D X x P x', computation x x' ->
    computation (TIAll IT D X x P) (TIAll IT D X x' P)
| cmp_TIAll_P : forall IT D X x P P', computation P P' ->
    computation (TIAll IT D X x P) (TIAll IT D X x P')
| cmp_THyps_IT : forall IT D X P h x IT', computation IT IT' ->
    computation (THyps IT D X P h x) (THyps IT' D X P h x)
| cmp_THyps_D : forall IT D X P h x D', computation D D' ->
    computation (THyps IT D X P h x) (THyps IT D' X P h x)
| cmp_THyps_X : forall IT D X P h x X', computation X X' ->
    computation (THyps IT D X P h x) (THyps IT D X' P h x)
| cmp_THyps_P : forall IT D X P h x P', computation P P' ->
    computation (THyps IT D X P h x) (THyps IT D X P' h x)
| cmp_THyps_h : forall IT D X P h x h', computation h h' ->
    computation (THyps IT D X P h x) (THyps IT D X P h' x)
| cmp_THyps_x : forall IT D X P h x x', computation x x' ->
    computation (THyps IT D X P h x) (THyps IT D X P h x')
| cmp_TClose_IT : forall IT F G IT', computation IT IT' ->
    computation (TClose IT F G) (TClose IT' F G)
| cmp_TClose_F : forall IT F G F', computation F F' ->
    computation (TClose IT F G) (TClose IT F' G)
| cmp_TClose_G : forall IT F G G', computation G G' ->
    computation (TClose IT F G) (TClose IT F G')
| cmp_TCloseCase_IT : forall k IT F G i Q b x IT', computation IT IT' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F G i Q b x)
| cmp_TCloseCase_F : forall k IT F G i Q b x F', computation F F' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F' G i Q b x)
| cmp_TCloseCase_G : forall k IT F G i Q b x G', computation G G' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G' i Q b x)
| cmp_TCloseCase_i : forall k IT F G i Q b x i', computation i i' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i' Q b x)
| cmp_TCloseCase_Q : forall k IT F G i Q b x Q', computation Q Q' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q' b x)
| cmp_TCloseCase_b : forall k IT F G i Q b x b', computation b b' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b' x)
| cmp_TCloseCase_x : forall k IT F G i Q b x x', computation x x' ->
    computation (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b x')
| cmp_TCloseInd_IT : forall IT G P s F i x IT', computation IT IT' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT' G P s F i x)
| cmp_TCloseInd_G : forall IT G P s F i x G', computation G G' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G' P s F i x)
| cmp_TCloseInd_P : forall IT G P s F i x P', computation P P' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G P' s F i x)
| cmp_TCloseInd_s : forall IT G P s F i x s', computation s s' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G P s' F i x)
| cmp_TCloseInd_F : forall IT G P s F i x F', computation F F' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G P s F' i x)
| cmp_TCloseInd_i : forall IT G P s F i x i', computation i i' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i' x)
| cmp_TCloseInd_x : forall IT G P s F i x x', computation x x' ->
    computation (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i x').

Lemma computation_reduction : forall t u, computation t u -> reduction t u.
Proof. intros t u H; induction H; solve [constructor; assumption]. Qed.

Lemma computation_conversion : forall t u, computation t u -> conv t u.
Proof. intros; apply reduction_conversion, computation_reduction; assumption. Qed.

#[local] Hint Resolve ty_interp ty_iall ty_idesc ty_enumt def_application smart_close
   smart_mui close_at_formation mu_at_formation payload_formation total_formation
   motive_formation def_formation family_formation diagonal_motive_typing
   close_motive_application motive_application smart_in_close smart_in_mui
   family_application recursive_method_formation close_motive_formation
   mu_method_formation close_method_formation close_case_method_formation
   arrow_formation enum_motive_formation sort_codomain_formation ty_epi : formation0 formation1 formation2 formation3.

#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation0) : formation1.
#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation1) : formation2.
#[local] Hint Extern 8 (typing _ _ _) => transport_from_existing ltac:(eauto 7 with formation2) : formation3.

Theorem computation_preservation : forall Gamma t T,
  typing Gamma t T -> forall u, computation t u -> typing Gamma u T.
Proof.
  intros Gamma t T H; induction H; intros u Hr.
  all: try match goal with
    HC : conv ?A ?B, IH : forall u, computation ?t u -> typing ?G u ?A |- typing ?G _ ?B =>
      eapply ty_conv; [eapply IH; exact Hr|eassumption|exact HC]
    end.
  all: try match goal with
    HL : ?j <= ?k, IH : forall u, computation ?t u -> typing ?G u (TSort ?j) |- typing ?G _ (TSort ?k) =>
      eapply ty_cumul; [eapply IH; exact Hr|exact HL]
    end.
  all: try match goal with
    HA : universe_le ?C ?A, HB : universe_le ?B ?D,
    IH : forall u, computation ?t u -> typing ?G u (TPi ?A ?B) |- typing ?G _ (TPi ?C ?D) =>
      eapply ty_cumul_fun; [eapply IH; exact Hr|eassumption|eassumption|exact HA|exact HB]
    end.
  all: inversion Hr; subst; clear Hr.
  all: try solve [match goal with HH : root_step ?src = Some ?dst |- _ =>
    eapply root_preservation with (t:=src); [eauto 2 using typing|exact HH] end].
  all: try solve [econstructor; eauto].
  all: repeat match goal with
    IH : forall u, computation ?src u -> typing ?G u ?T,
    Hr : computation ?src ?dst |- _ =>
    let Hnew := fresh "Hreduced" in pose proof (IH dst Hr) as Hnew; clear IH
  end.
  all: try match goal with HC : computation ?s ?d |- _ =>
    pose proof (computation_reduction _ _ HC) as Hfull end.
  all: try solve [eauto 8 using smart_ipi, smart_isig, smart_ichoice, ty_epi,
    smart_switch, ty_interp, ty_iall, smart_mui, smart_close with formation3].
  all: try solve [eapply ty_conv;
    [first [eapply smart_app|eapply smart_snd|eapply smart_switch|eapply smart_hyps|
      eapply smart_ind|eapply smart_close_case|eapply smart_close_ind|eapply smart_mui|eapply smart_close];
      solve [eauto 8 with formation3] | eassumption | operator_conversion]].
  - apply ty_pi; [assumption|].
    eapply context_conversion; [exact H|eassumption|apply reduction_conversion; eassumption|exact H0].
  - apply ty_sigma; [assumption|].
    eapply context_conversion; [exact H|eassumption|apply reduction_conversion; eassumption|exact H0].
  - destruct (sigma_components _ _ _ H _ _ eq_refl) as [j [l [HA HB]]].
    eapply ty_pair; [exact H|eassumption|].
    eapply ty_conv; [exact H1|exact (substitution _ _ _ _ _ HB Hreduced)|operator_conversion].
Qed.

Theorem computations_preservation : forall t u, rtc computation t u ->
  forall Gamma T, typing Gamma t T -> typing Gamma u T.
Proof. intros t u H; induction H; eauto using computation_preservation. Qed.

Print Assumptions computation_preservation.
