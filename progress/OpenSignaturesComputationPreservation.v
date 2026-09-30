(* Compatible computation under every binder and annotation. This relation
   is separate from the original beta/eta reduction: it supplies a checked
   replacement option, not a proof of the refuted original claim. *)
From Stdlib Require Import List.
Require Export OpenSignaturesPreservation.
Require nameless.DBComputationPreservation.

Inductive computation : term -> term -> Prop :=
| cmp_root : forall t u, root_step t = Some u -> computation t u
| cmp_TPi_A : forall x A B A', computation A A' ->
    computation (TPi x A B) (TPi x A' B)
| cmp_TPi_B : forall x A B B', computation B B' ->
    computation (TPi x A B) (TPi x A B')
| cmp_TLam_b : forall x b b', computation b b' ->
    computation (TLam x b) (TLam x b')
| cmp_TApp_f : forall f a f', computation f f' ->
    computation (TApp f a) (TApp f' a)
| cmp_TApp_a : forall f a a', computation a a' ->
    computation (TApp f a) (TApp f a')
| cmp_TSigma_A : forall x A B A', computation A A' ->
    computation (TSigma x A B) (TSigma x A' B)
| cmp_TSigma_B : forall x A B B', computation B B' ->
    computation (TSigma x A B) (TSigma x A B')
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

Lemma step_computation : forall t u, step t u -> computation t u.
Proof. intros t u H; induction H; solve [constructor; assumption]. Qed.

Lemma encode_computation : forall t u, computation t u -> forall env,
  nameless.DBComputationPreservation.computation (encode env t) (encode env u).
Proof.
  intros t u H; induction H; intros env; cbn [encode];
    try solve [constructor; auto].
  apply nameless.DBComputationPreservation.cmp_root; now apply encode_root_step.
Qed.

Theorem named_computation_preservation : forall Gamma t u T,
  typing Gamma t T -> computation t u -> typing Gamma u T.
Proof.
  intros Gamma t u T Ht Hr.
  destruct (context_representation _ (typing_context _ _ _ Ht))
    as [Delta [env [HC HD]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HD) as HT.
  pose proof (nameless.DBComputationPreservation.computation_preservation
    _ _ _ HT _ (encode_computation _ _ Hr env)) as Hu.
  eapply typing_reflection_given; [exact Hu|exact HC|reflexivity|reflexivity].
Qed.

Print Assumptions named_computation_preservation.
