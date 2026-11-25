(* Machine check of docs/type-rules/calculus.tex, Part I (the core calculus).
   The document writes the rules in the notation of Dagand and McBride,
   "Elaborating Inductive Definitions" (arXiv:1210.6390), and elides the
   presupposition premises it lists once; the statements here are the full
   Rocq rules, with every premise.
   Every statement below is transcribed from that document and proved from
   the Rocq definition, constructor or theorem it cites, so the document
   cannot drift from the sources unnoticed. Rules are restated with the
   document's premises in the constructor's order and closed by [exact];
   derived forms and computation rules are closed by [reflexivity].
   Build: make -C progress check-docs *)
From Stdlib Require Import List Arith String Lia.
Require Import OpenSignatures OpenSignaturesComputationPreservation
  OpenSignaturesEtaRegression OpenSignaturesObservationalLaws
  OpenSignaturesObservationalTypes.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Derived forms; the document introduces each with the operators it abbreviates *)
Goal forall A B, arrow A B = TPi (fresh [A;B]) A B. Proof. reflexivity. Qed.
Goal forall A B, product A B = TSigma (fresh [A;B]) A B. Proof. reflexivity. Qed.
Goal forall A B, ~ In (fresh [A;B]) (free_vars B).
Proof. intros; apply fresh_not_free; cbn; auto. Qed.
Goal Bot = TEnumT TNilE. Proof. reflexivity. Qed.
(* Def I = I -> IDesc I and Fam I = I -> Set_0, up to the binder name. *)
Goal forall IT, alpha_equiv (Def IT) (arrow IT (TIDesc IT)).
Proof.
  intros; unfold Def, arrow. apply constant_pi_alpha.
  - change (free_vars (TIDesc IT)) with (free_vars IT). apply fresh_not_free; cbn; auto.
  - apply fresh_not_free; cbn; auto.
Qed.
Goal forall IT, alpha_equiv (Family IT) (arrow IT (TSort 0)).
Proof. intros; unfold Family, arrow; apply constant_pi_alpha; cbn; tauto. Qed.
Goal forall IT F G i, CloseAt IT F G i = TApp (TClose IT F G) i. Proof. reflexivity. Qed.
Goal forall IT G, carrier IT G = TClose IT G G. Proof. reflexivity. Qed.
Goal forall IT F G i, payload IT F G i = TInterp IT (TApp F i) (carrier IT G).
Proof. reflexivity. Qed.
Goal forall IT X, motive IT X =
  arrow (TSigma (fresh [IT;X]) IT (TApp X (TVar (fresh [IT;X])))) (TSort 0).
Proof. reflexivity. Qed.
Goal forall IT X P, exists i y, i <> y /\ recursive_method IT X P =
  TPi i IT (TPi y (TApp X (TVar i)) (TApp P (TPair (TVar i) (TVar y)))).
Proof. intros; do 2 eexists; split; [|reflexivity]. lia. Qed.
Goal forall k A z, abort k A z = TSwitch k TNilE (constant A) TUnit z.
Proof. reflexivity. Qed.
Goal forall A t, conv (TApp (constant A) t) A. Proof. exact constant_application. Qed.
Goal forall IT F G i x, unroll IT F G i x =
  TCloseCase 0 IT F G i (constant (payload IT F G i)) identity x.
Proof. reflexivity. Qed.
Goal identity = TLam 0 (TVar 0). Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 2: root computation rules, shown in the document beside each operator *)
Goal forall x b a, root_step (TApp (TLam x b) a) = Some (subst a x b). Proof. reflexivity. Qed.
Goal forall a b, root_step (TFst (TPair a b)) = Some a. Proof. reflexivity. Qed.
Goal forall a b, root_step (TSnd (TPair a b)) = Some b. Proof. reflexivity. Qed.
Goal forall k P, root_step (TEPi k TNilE P) = Some TUnitT. Proof. reflexivity. Qed.
Goal forall k l E P, exists n, root_step (TEPi k (TConsE l E) P) =
  Some (product (TApp P TEZero) (TEPi k E (TLam n (TApp P (TESucc (TVar n)))))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall k l E P b bs, root_step (TSwitch k (TConsE l E) P (TPair b bs) TEZero) = Some b.
Proof. reflexivity. Qed.
Goal forall k l E P b bs n, exists m,
  root_step (TSwitch k (TConsE l E) P (TPair b bs) (TESucc n)) =
  Some (TSwitch k E (TLam m (TApp P (TESucc (TVar m)))) bs n).
Proof. intros; eexists; reflexivity. Qed.
Goal forall k IT F G i Q b x, root_step (TCloseCase k IT F G i Q b (TIn x)) = Some (TApp b x).
Proof. reflexivity. Qed.
Goal forall IT D P s i x, exists j y,
  root_step (TInd IT D P s i (TIn x)) =
  Some (TApp (TApp (TApp s i) x)
    (THyps IT (TApp D i) (TMuI IT D) P
      (TLam j (TLam y (TInd IT D P s (TVar j) (TVar y)))) x)).
Proof. intros; do 2 eexists; reflexivity. Qed.
Goal forall G P, exists z, diagonal_motive G P =
  TLam z (TApp (TApp (TApp P G) (TFst (TVar z))) (TSnd (TVar z))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall IT G P s F i x, exists j y,
  root_step (TCloseInd IT G P s F i (TIn x)) =
  Some (TApp (TApp (TApp (TApp s F) i) x)
    (THyps IT (TApp F i) (carrier IT G) (diagonal_motive G P)
      (TLam j (TLam y (TCloseInd IT G P s G (TVar j) (TVar y)))) x)).
Proof. intros; do 2 eexists; reflexivity. Qed.

(* Interpretation column *)
Goal forall IT j X, root_step (TInterp IT (TIVar j) X) = Some (TApp X j). Proof. reflexivity. Qed.
Goal forall IT X, root_step (TInterp IT TI1 X) = Some TUnitT. Proof. reflexivity. Qed.
Goal forall IT X, root_step (TInterp IT TIBot X) = Some Bot. Proof. reflexivity. Qed.
Goal forall IT D1 D2 X, root_step (TInterp IT (TIProd D1 D2) X) =
  Some (product (TInterp IT D1 X) (TInterp IT D2 X)). Proof. reflexivity. Qed.
Goal forall IT S T X, exists s, root_step (TInterp IT (TIPi S T) X) =
  Some (TPi s S (TInterp IT (TApp T (TVar s)) X)). Proof. intros; eexists; reflexivity. Qed.
Goal forall IT S T X, exists s, root_step (TInterp IT (TISig S T) X) =
  Some (TSigma s S (TInterp IT (TApp T (TVar s)) X)). Proof. intros; eexists; reflexivity. Qed.
Goal forall IT E T X, exists c, root_step (TInterp IT (TIChoice E T) X) =
  Some (TSigma c (TEnumT E) (TInterp IT (TApp T (TVar c)) X)).
Proof. intros; eexists; reflexivity. Qed.

(* iAll column *)
Goal forall IT j X y P, root_step (TIAll IT (TIVar j) X y P) = Some (TApp P (TPair j y)).
Proof. reflexivity. Qed.
Goal forall IT X P, root_step (TIAll IT TI1 X TUnit P) = Some TUnitT. Proof. reflexivity. Qed.
Goal forall IT X z P, root_step (TIAll IT TIBot X z P) = Some TUnitT. Proof. reflexivity. Qed.
Goal forall IT D1 D2 X a b P, root_step (TIAll IT (TIProd D1 D2) X (TPair a b) P) =
  Some (product (TIAll IT D1 X a P) (TIAll IT D2 X b P)). Proof. reflexivity. Qed.
Goal forall IT S T X f P, exists s, root_step (TIAll IT (TIPi S T) X f P) =
  Some (TPi s S (TIAll IT (TApp T (TVar s)) X (TApp f (TVar s)) P)).
Proof. intros; eexists; reflexivity. Qed.
Goal forall IT S T X s y P, root_step (TIAll IT (TISig S T) X (TPair s y) P) =
  Some (TIAll IT (TApp T s) X y P). Proof. reflexivity. Qed.
Goal forall IT E T X c y P, root_step (TIAll IT (TIChoice E T) X (TPair c y) P) =
  Some (TIAll IT (TApp T c) X y P). Proof. reflexivity. Qed.

(* hyps column *)
Goal forall IT j X P h y, root_step (THyps IT (TIVar j) X P h y) = Some (TApp (TApp h j) y).
Proof. reflexivity. Qed.
Goal forall IT X P h, root_step (THyps IT TI1 X P h TUnit) = Some TUnit. Proof. reflexivity. Qed.
Goal forall IT X P h z, root_step (THyps IT TIBot X P h z) = Some TUnit. Proof. reflexivity. Qed.
Goal forall IT D1 D2 X P h a b, root_step (THyps IT (TIProd D1 D2) X P h (TPair a b)) =
  Some (TPair (THyps IT D1 X P h a) (THyps IT D2 X P h b)). Proof. reflexivity. Qed.
Goal forall IT S T X P h f, exists s, root_step (THyps IT (TIPi S T) X P h f) =
  Some (TLam s (THyps IT (TApp T (TVar s)) X P h (TApp f (TVar s)))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall IT S T X P h s y, root_step (THyps IT (TISig S T) X P h (TPair s y)) =
  Some (THyps IT (TApp T s) X P h y). Proof. reflexivity. Qed.
Goal forall IT E T X P h c y, root_step (THyps IT (TIChoice E T) X P h (TPair c y)) =
  Some (THyps IT (TApp T c) X P h y). Proof. reflexivity. Qed.

(* No rule unfolds a close type or a mu type. *)
Goal forall IT F G, root_step (TClose IT F G) = None. Proof. reflexivity. Qed.
Goal forall IT F G i, root_step (CloseAt IT F G i) = None. Proof. reflexivity. Qed.
Goal forall IT D i, root_step (MuAt IT D i) = None. Proof. reflexivity. Qed.

(* Section 3: evaluation, reduction, conversion, values.
   Evaluation contexts: exactly the 19 congruences of [step]. *)
Goal forall t u, root_step t = Some u -> step t u. Proof. exact st_root. Qed.
Goal forall f a f', step f f' -> step (TApp f a) (TApp f' a). Proof. exact st_TApp_f. Qed.
Goal forall a b a', step a a' -> step (TPair a b) (TPair a' b). Proof. exact st_TPair_a. Qed.
Goal forall a b b', step b b' -> step (TPair a b) (TPair a b'). Proof. exact st_TPair_b. Qed.
Goal forall p p', step p p' -> step (TFst p) (TFst p'). Proof. exact st_TFst_p. Qed.
Goal forall p p', step p p' -> step (TSnd p) (TSnd p'). Proof. exact st_TSnd_p. Qed.
Goal forall n n', step n n' -> step (TESucc n) (TESucc n'). Proof. exact st_TESucc_n. Qed.
Goal forall x x', step x x' -> step (TIn x) (TIn x'). Proof. exact st_TIn_x. Qed.
Goal forall k E P E', step E E' -> step (TEPi k E P) (TEPi k E' P). Proof. exact st_TEPi_E. Qed.
Goal forall k E P p e E', step E E' -> step (TSwitch k E P p e) (TSwitch k E' P p e).
Proof. exact st_TSwitch_E. Qed.
Goal forall k E P p e p', step p p' -> step (TSwitch k E P p e) (TSwitch k E P p' e).
Proof. exact st_TSwitch_p. Qed.
Goal forall k E P p e e', step e e' -> step (TSwitch k E P p e) (TSwitch k E P p e').
Proof. exact st_TSwitch_e. Qed.
Goal forall IT D X D', step D D' -> step (TInterp IT D X) (TInterp IT D' X).
Proof. exact st_TInterp_D. Qed.
Goal forall IT D X x P D', step D D' -> step (TIAll IT D X x P) (TIAll IT D' X x P).
Proof. exact st_TIAll_D. Qed.
Goal forall IT D X x P x', step x x' -> step (TIAll IT D X x P) (TIAll IT D X x' P).
Proof. exact st_TIAll_x. Qed.
Goal forall IT D X P h x D', step D D' -> step (THyps IT D X P h x) (THyps IT D' X P h x).
Proof. exact st_THyps_D. Qed.
Goal forall IT D X P h x x', step x x' -> step (THyps IT D X P h x) (THyps IT D X P h x').
Proof. exact st_THyps_x. Qed.
Goal forall IT D P s i x x', step x x' -> step (TInd IT D P s i x) (TInd IT D P s i x').
Proof. exact st_TInd_x. Qed.
Goal forall k IT F G i Q b x x', step x x' ->
  step (TCloseCase k IT F G i Q b x) (TCloseCase k IT F G i Q b x').
Proof. exact st_TCloseCase_x. Qed.
Goal forall IT G P s F i x x', step x x' ->
  step (TCloseInd IT G P s F i x) (TCloseInd IT G P s F i x').
Proof. exact st_TCloseInd_x. Qed.
(* "Never under lambda or in an argument." *)
Goal forall x b u, ~ step (TLam x b) u.
Proof. intros x b u H; inversion H; subst; discriminate. Qed.
Goal forall y a u, ~ step (TApp (TVar y) a) u.
Proof.
  intros y a u H; inversion H; subst; [discriminate|].
  match goal with H : step (TVar _) _ |- _ => inversion H; subst; discriminate end.
Qed.
(* eval is the reflexive transitive closure; run is a strategy for it. *)
Goal forall t, eval t t. Proof. exact ev_refl. Qed.
Goal forall t u v, step t u -> eval u v -> eval t v. Proof. exact ev_step. Qed.
Goal forall t u, next_step t = Some u -> step t u. Proof. exact next_step_sound. Qed.
Goal forall fuel t, eval t (run fuel t). Proof. exact run_sound. Qed.

(* Full reduction: root steps, eta, and step is included. *)
Goal forall t u, root_step t = Some u -> reduction t u. Proof. exact red_root. Qed.
Goal forall x f, ~ In x (free_vars f) -> reduction (TLam x (TApp f (TVar x))) f.
Proof. exact red_eta. Qed.
Goal forall t u, step t u -> reduction t u. Proof. exact step_reduction. Qed.
Goal forall x b b', reduction b b' -> reduction (TLam x b) (TLam x b'). Proof. exact red_TLam_b. Qed.
Goal forall f a a', reduction a a' -> reduction (TApp f a) (TApp f a'). Proof. exact red_TApp_a. Qed.

(* Conversion. *)
Goal forall t u, step t u -> conv t u. Proof. exact cv_step. Qed.
Goal forall t, conv t t. Proof. exact cv_refl. Qed.
Goal forall t u, conv t u -> conv u t. Proof. exact cv_sym. Qed.
Goal forall t u v, conv t u -> conv u v -> conv t v. Proof. exact cv_trans. Qed.
Goal forall x f, ~ In x (free_vars f) -> conv (TLam x (TApp f (TVar x))) f. Proof. exact cv_eta. Qed.
Goal forall t u, alpha_equiv t u -> conv t u. Proof. exact cv_alpha. Qed.
Goal forall t u, compatible conv t u -> conv t u. Proof. exact cv_compatible. Qed.
Goal forall t u, reduction t u -> conv t u.
Proof. intros t u H; exact (reduces_conv _ _ (reduces_step H (reduces_refl u))). Qed.

(* Values: the 28 forms listed. *)
Goal forall k, value (TSort k). Proof. constructor. Qed.
Goal forall x A B, value (TPi x A B). Proof. constructor. Qed.
Goal forall x A B, value (TSigma x A B). Proof. constructor. Qed.
Goal forall x b, value (TLam x b). Proof. constructor. Qed.
Goal forall a b, value (TPair a b). Proof. constructor. Qed.
Goal value TUnitT /\ value TUnit /\ value TUId /\ value TEnumU /\ value TNilE /\ value TEZero
  /\ value TI1 /\ value TIBot.
Proof. repeat split; constructor. Qed.
Goal forall s, value (TTag s). Proof. constructor. Qed.
Goal forall l E, value (TConsE l E). Proof. constructor. Qed.
Goal forall E, value (TEnumT E). Proof. constructor. Qed.
Goal forall n, value (TESucc n). Proof. constructor. Qed.
Goal forall IT, value (TIDesc IT). Proof. constructor. Qed.
Goal forall i, value (TIVar i). Proof. constructor. Qed.
Goal forall A B, value (TIProd A B) /\ value (TIPi A B) /\ value (TISig A B) /\ value (TIChoice A B).
Proof. repeat split; constructor. Qed.
Goal forall IT D i, value (TMuI IT D) /\ value (MuAt IT D i). Proof. split; constructor. Qed.
Goal forall IT F G i, value (TClose IT F G) /\ value (CloseAt IT F G i). Proof. split; constructor. Qed.
Goal forall x, value (TIn x). Proof. constructor. Qed.
(* Eliminators and variables are not values. *)
Goal forall x, ~ value (TVar x). Proof. intros x H; inversion H. Qed.
Goal forall IT D X, ~ value (TInterp IT D X). Proof. intros IT D X H; inversion H. Qed.
Goal forall p, ~ value (TFst p). Proof. intros p H; inversion H. Qed.

(* Examples of Sections 2 and 3. *)
Definition ex_t := TLam 0 (TApp (TLam 1 (TVar 1)) (TVar 0)).
Goal value ex_t /\ (forall u, ~ step ex_t u)
  /\ reduction ex_t (TLam 0 (TVar 0)) /\ reduction ex_t (TLam 1 (TVar 1)).
Proof.
  repeat split.
  - constructor.
  - intros u H; inversion H; subst; discriminate.
  - apply red_TLam_b, red_root; reflexivity.
  - apply red_eta; cbn; intuition discriminate.
Qed.
Goal forall k l0 l1 P u v, exists n,
  step (TSwitch k (TConsE l0 (TConsE l1 TNilE)) P (TPair u (TPair v TUnit)) (TESucc TEZero))
       (TSwitch k (TConsE l1 TNilE) (TLam n (TApp P (TESucc (TVar n)))) (TPair v TUnit) TEZero)
  /\ step (TSwitch k (TConsE l1 TNilE) (TLam n (TApp P (TESucc (TVar n)))) (TPair v TUnit) TEZero) v.
Proof. intros; eexists; split; apply st_root; reflexivity. Qed.
(* [[ 'Sigma A (\_. 'var star) ]] X == A x X star *)
Lemma ex_interp_cons : forall IT A X,
  conv (TInterp IT (TISig A (TLam (fresh [A]) (TIVar TUnit))) X) (product A (TApp X TUnit)).
Proof.
  intros IT A X.
  set (D := TLam (fresh [A]) (TIVar TUnit)).
  set (s := fresh [IT; A; D; X]).
  eapply cv_trans; [apply cv_step, st_root; reflexivity|]. fold s.
  eapply cv_trans with (u := TSigma s A (TApp X TUnit)).
  - apply cv_compatible, cp_TSigma; [apply cv_refl|].
    eapply cv_trans with (u := TInterp IT (TIVar TUnit) X).
    + apply cv_compatible, cp_TInterp; try apply cv_refl.
      apply cv_step, st_root; reflexivity.
    + apply cv_step, st_root; reflexivity.
  - apply cv_alpha. unfold product. apply constant_sigma_alpha.
    + cbn [free_vars]. rewrite app_nil_r. apply fresh_not_free; cbn; auto.
    + apply fresh_not_free; cbn; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 2: typing rules, in the document's form *)
Goal wf empty_ctx. Proof. exact wf_nil. Qed.
Goal forall Gamma x A k, wf Gamma -> typing Gamma A (TSort k) -> fresh_in Gamma x ->
  wf (extend Gamma x A). Proof. exact wf_cons. Qed.
Goal forall Gamma x A, wf Gamma -> lookup Gamma x = Some A -> typing Gamma (TVar x) A.
Proof. exact ty_var. Qed.
Goal forall Gamma x A B j k, fresh_in Gamma x -> typing Gamma A (TSort j) ->
  typing (extend Gamma x A) B (TSort k) -> typing Gamma (TPi x A B) (TSort (Nat.max j k)).
Proof. exact ty_pi. Qed.
Goal forall Gamma x A B j k, fresh_in Gamma x -> typing Gamma A (TSort j) ->
  typing (extend Gamma x A) B (TSort k) -> typing Gamma (TSigma x A B) (TSort (Nat.max j k)).
Proof. exact ty_sigma. Qed.
Goal forall Gamma x A B b k, fresh_in Gamma x -> typing Gamma (TPi x A B) (TSort k) ->
  typing (extend Gamma x A) b B -> typing Gamma (TLam x b) (TPi x A B).
Proof. exact ty_lam. Qed.
Goal forall Gamma x A B f a k, typing Gamma (TPi x A B) (TSort k) ->
  typing Gamma f (TPi x A B) -> typing Gamma a A -> typing Gamma (TApp f a) (subst a x B).
Proof. exact ty_app. Qed.
Goal forall Gamma x A B a b k, typing Gamma (TSigma x A B) (TSort k) ->
  typing Gamma a A -> typing Gamma b (subst a x B) -> typing Gamma (TPair a b) (TSigma x A B).
Proof. exact ty_pair. Qed.
Goal forall Gamma x A B p k, typing Gamma (TSigma x A B) (TSort k) ->
  typing Gamma p (TSigma x A B) -> typing Gamma (TFst p) A.
Proof. exact ty_fst. Qed.
Goal forall Gamma x A B p k, typing Gamma (TSigma x A B) (TSort k) ->
  typing Gamma p (TSigma x A B) -> typing Gamma (TSnd p) (subst (TFst p) x B).
Proof. exact ty_snd. Qed.
Goal forall Gamma t A B k, typing Gamma t A -> typing Gamma B (TSort k) -> conv A B ->
  typing Gamma t B. Proof. exact ty_conv. Qed.
Goal forall Gamma t u A, typing Gamma t A -> alpha_equiv t u -> typing Gamma u A.
Proof. exact ty_alpha. Qed.
Goal forall Gamma t j k, typing Gamma t (TSort j) -> j <= k -> typing Gamma t (TSort k).
Proof. exact ty_cumul. Qed.
Goal forall Gamma f x A B C D j k, typing Gamma f (TPi x A B) ->
  typing Gamma (TPi x A B) (TSort j) -> typing Gamma (TPi x C D) (TSort k) ->
  universe_le C A -> universe_le B D -> typing Gamma f (TPi x C D).
Proof. exact ty_cumul_fun. Qed.
Goal forall A, universe_le A A. Proof. exact ul_refl. Qed.
Goal forall j k, j <= k -> universe_le (TSort j) (TSort k). Proof. exact ul_sort. Qed.
Goal forall x A B C D, universe_le C A -> universe_le B D ->
  universe_le (TPi x A B) (TPi x C D). Proof. exact ul_pi. Qed.
(* Axioms. *)
Goal forall Gamma k, wf Gamma -> typing Gamma (TSort k) (TSort (S k)). Proof. exact ty_sort. Qed.
Goal forall Gamma k, wf Gamma -> typing Gamma TUnitT (TSort k). Proof. exact ty_unitT. Qed.
Goal forall Gamma, wf Gamma -> typing Gamma TUnit TUnitT. Proof. exact ty_unit. Qed.
Goal forall Gamma, wf Gamma -> typing Gamma TUId (TSort 0). Proof. exact ty_uid. Qed.
Goal forall Gamma s, wf Gamma -> typing Gamma (TTag s) TUId. Proof. exact ty_tag. Qed.
Goal forall Gamma, wf Gamma -> typing Gamma TEnumU (TSort 0). Proof. exact ty_enumu. Qed.
Goal forall Gamma, wf Gamma -> typing Gamma TNilE TEnumU. Proof. exact ty_nile. Qed.
(* Enumerations. *)
Goal forall Gamma l E, typing Gamma l TUId -> typing Gamma E TEnumU ->
  typing Gamma (TConsE l E) TEnumU. Proof. exact ty_conse. Qed.
Goal forall Gamma E, typing Gamma E TEnumU -> typing Gamma (TEnumT E) (TSort 0).
Proof. exact ty_enumt. Qed.
Goal forall Gamma l E, typing Gamma l TUId -> typing Gamma E TEnumU ->
  typing Gamma TEZero (TEnumT (TConsE l E)). Proof. exact ty_zero. Qed.
Goal forall Gamma l E n, typing Gamma l TUId -> typing Gamma E TEnumU ->
  typing Gamma n (TEnumT E) -> typing Gamma (TESucc n) (TEnumT (TConsE l E)).
Proof. exact ty_succ. Qed.
Goal forall Gamma k E P, typing Gamma E TEnumU ->
  typing Gamma P (arrow (TEnumT E) (TSort k)) -> typing Gamma (TEPi k E P) (TSort k).
Proof. exact ty_epi. Qed.
Goal forall Gamma k E P b c, typing Gamma E TEnumU ->
  typing Gamma P (arrow (TEnumT E) (TSort k)) -> typing Gamma b (TEPi k E P) ->
  typing Gamma c (TEnumT E) -> typing Gamma (TSwitch k E P b c) (TApp P c).
Proof. exact ty_switch. Qed.
(* Descriptions; the index type premise is the document's convention. *)
Goal forall Gamma IT, typing Gamma IT (TSort 0) -> typing Gamma (TIDesc IT) (TSort 1).
Proof. exact ty_idesc. Qed.
Goal forall Gamma IT i, typing Gamma IT (TSort 0) -> typing Gamma i IT ->
  typing Gamma (TIVar i) (TIDesc IT). Proof. exact ty_ivar. Qed.
Goal forall Gamma IT, typing Gamma IT (TSort 0) -> typing Gamma TI1 (TIDesc IT).
Proof. exact ty_i1. Qed.
Goal forall Gamma IT, typing Gamma IT (TSort 0) -> typing Gamma TIBot (TIDesc IT).
Proof. exact ty_ibot. Qed.
Goal forall Gamma IT D1 D2, typing Gamma IT (TSort 0) -> typing Gamma D1 (TIDesc IT) ->
  typing Gamma D2 (TIDesc IT) -> typing Gamma (TIProd D1 D2) (TIDesc IT).
Proof. exact ty_iprod. Qed.
Goal forall Gamma IT S T, typing Gamma IT (TSort 0) -> typing Gamma S (TSort 0) ->
  typing Gamma T (arrow S (TIDesc IT)) -> typing Gamma (TIPi S T) (TIDesc IT).
Proof. exact ty_ipi. Qed.
Goal forall Gamma IT S T, typing Gamma IT (TSort 0) -> typing Gamma S (TSort 0) ->
  typing Gamma T (arrow S (TIDesc IT)) -> typing Gamma (TISig S T) (TIDesc IT).
Proof. exact ty_isig. Qed.
Goal forall Gamma IT E T, typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
  typing Gamma T (arrow (TEnumT E) (TIDesc IT)) -> typing Gamma (TIChoice E T) (TIDesc IT).
Proof. exact ty_ichoice. Qed.
Goal forall Gamma IT D X, typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
  typing Gamma X (Family IT) -> typing Gamma (TInterp IT D X) (TSort 0).
Proof. exact ty_interp. Qed.
Goal forall Gamma IT D X x P, typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
  typing Gamma X (Family IT) -> typing Gamma x (TInterp IT D X) ->
  typing Gamma P (motive IT X) -> typing Gamma (TIAll IT D X x P) (TSort 0).
Proof. exact ty_iall. Qed.
Goal forall Gamma IT D X P h x, typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
  typing Gamma X (Family IT) -> typing Gamma P (motive IT X) ->
  typing Gamma h (recursive_method IT X P) -> typing Gamma x (TInterp IT D X) ->
  typing Gamma (THyps IT D X P h x) (TIAll IT D X x P).
Proof. exact ty_hyps. Qed.
Goal forall Gamma IT D, typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  typing Gamma (TMuI IT D) (Family IT). Proof. exact ty_mui. Qed.
Goal forall Gamma IT D i x, typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  typing Gamma i IT -> typing Gamma x (TInterp IT (TApp D i) (TMuI IT D)) ->
  typing Gamma (TIn x) (MuAt IT D i). Proof. exact ty_in_mui. Qed.
(* The step type of ind: Pi i:I. Pi y:[[D i]](mu D). iAll (D i) (mu D) y P -> P (i, in y). *)
Goal forall IT D P, exists i y h, mu_ind_method IT D P =
  TPi i IT (TPi y (TInterp IT (TApp D (TVar i)) (TMuI IT D))
    (TPi h (TIAll IT (TApp D (TVar i)) (TMuI IT D) (TVar y) P)
      (TApp P (TPair (TVar i) (TIn (TVar y)))))).
Proof. intros; do 3 eexists; reflexivity. Qed.
Goal forall Gamma IT D P s i x, typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  typing Gamma P (motive IT (TMuI IT D)) -> typing Gamma s (mu_ind_method IT D P) ->
  typing Gamma i IT -> typing Gamma x (MuAt IT D i) ->
  typing Gamma (TInd IT D P s i x) (TApp P (TPair i x)).
Proof. exact ty_ind. Qed.
(* Parameterized closure. *)
Goal forall Gamma IT F G, typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma (TClose IT F G) (Family IT).
Proof. exact ty_close. Qed.
Goal forall Gamma IT F G i x, typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma x (TInterp IT (TApp F i) (carrier IT G)) ->
  typing Gamma (TIn x) (CloseAt IT F G i).
Proof. exact ty_in_close. Qed.
(* b : Pi y:[[F i]]X_G. Q (in y) *)
Goal forall IT F G i Q, exists y, close_case_method IT F G i Q =
  TPi y (TInterp IT (TApp F i) (carrier IT G)) (TApp Q (TIn (TVar y))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall Gamma k IT F G i Q b x, typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma Q (arrow (CloseAt IT F G i) (TSort k)) ->
  typing Gamma b (close_case_method IT F G i Q) -> typing Gamma x (CloseAt IT F G i) ->
  typing Gamma (TCloseCase k IT F G i Q b x) (TApp Q x).
Proof. exact ty_close_case. Qed.
(* P : Pi H:Def. Pi j:I. C_{H,G}(j) -> Set_0 *)
Goal forall IT G, exists H j x, close_motive IT G =
  TPi H (Def IT) (TPi j IT (TPi x (CloseAt IT (TVar H) G (TVar j)) (TSort 0))).
Proof. intros; do 3 eexists; reflexivity. Qed.
(* s : Pi H. Pi j. Pi y:[[H j]]X_G. iAll (H j) X_G y P^G -> P H j (in y) *)
Goal forall IT G P, exists H j y h, close_ind_method IT G P =
  TPi H (Def IT) (TPi j IT
    (TPi y (TInterp IT (TApp (TVar H) (TVar j)) (carrier IT G))
      (TPi h (TIAll IT (TApp (TVar H) (TVar j)) (carrier IT G) (TVar y) (diagonal_motive G P))
        (TApp (TApp (TApp P (TVar H)) (TVar j)) (TIn (TVar y)))))).
Proof. intros; do 4 eexists; reflexivity. Qed.
Goal forall Gamma IT G P s F i x, typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
  typing Gamma P (close_motive IT G) -> typing Gamma s (close_ind_method IT G P) ->
  typing Gamma F (Def IT) -> typing Gamma i IT -> typing Gamma x (CloseAt IT F G i) ->
  typing Gamma (TCloseInd IT G P s F i x) (TApp (TApp (TApp P F) i) x).
Proof. exact ty_close_ind. Qed.

(* Examples of Section 2. *)
Goal typing (extend empty_ctx 0 (arrow TUnitT (TSort 0))) (TVar 0) (arrow TUnitT (TSort 1)).
Proof. exact eta_reduct_typing. Qed.
Goal typing (extend empty_ctx 0 (arrow (TSort 1) (TSort 0))) (TVar 0) (arrow (TSort 0) (TSort 0)).
Proof. exact domain_eta_reduct_typing. Qed.
Goal ~ conv (TSort 0) (TSort 1). Proof. exact sorts_remain_distinct. Qed.
Goal ~ universe_le (TSort 1) (TSort 0). Proof. exact universes_do_not_lower. Qed.
Definition ex_E := TConsE (TTag "nil") (TConsE (TTag "cons") TNilE).
Goal typing empty_ctx TEZero (TEnumT ex_E) /\ typing empty_ctx (TESucc TEZero) (TEnumT ex_E).
Proof.
  assert (Ht : forall s, typing empty_ctx (TTag s) TUId) by (intro; apply ty_tag, wf_nil).
  assert (Hn : typing empty_ctx TNilE TEnumU) by apply ty_nile, wf_nil.
  repeat split.
  - apply ty_zero; auto using ty_conse.
  - apply ty_succ; auto using ty_conse. apply ty_zero; auto.
Qed.
Goal forall k P, conv (TEPi k ex_E P)
  (product (TApp P TEZero) (product (TApp P (TESucc TEZero)) TUnitT)).
Proof.
  intros k P. unfold ex_E.
  eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  apply product_conversion; [apply cv_refl|].
  eapply cv_trans; [apply cv_step, st_root; reflexivity|].
  apply product_conversion.
  - eapply cv_trans; [apply cv_step, st_root; reflexivity|].
    unfold subst; cbn [substitute Nat.eqb]. rewrite Nat.eqb_refl.
    apply cv_compatible, cp_TApp; [|apply cv_refl].
    fold (subst TEZero (fresh [TTag "nil"; TConsE (TTag "cons") TNilE; P]) P).
    rewrite subst_fresh; [apply cv_refl|]. apply fresh_not_free; cbn; auto.
  - apply cv_step, st_root; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 4: observational equivalence *)
Goal observation_type = TEnumT (TConsE (TTag "true") (TConsE (TTag "false") TNilE)).
Proof. reflexivity. Qed.
Goal forall t, observation t <-> t = TEZero \/ t = TESucc TEZero. Proof. reflexivity. Qed.
Goal forall A t u, closed_observational_eq A t u <->
  typing empty_ctx t A /\ typing empty_ctx u A /\
  forall x c v, typing (extend empty_ctx x A) c observation_type -> observation v ->
    (eval (subst t x c) v <-> eval (subst u x c) v).
Proof. reflexivity. Qed.
Goal forall Gamma A t u, observational_eq Gamma A t u <->
  typing Gamma t A /\ typing Gamma u A /\
  forall env, closing Gamma env ->
    closed_observational_eq (instantiate env A) (instantiate env t) (instantiate env u).
Proof. reflexivity. Qed.
Goal closing empty_ctx []. Proof. exact closing_nil. Qed.
Goal forall Gamma env x A u, fresh_in Gamma x -> wf (extend Gamma x A) -> closing Gamma env ->
  typing empty_ctx u (instantiate env A) -> closing (extend Gamma x A) ((x, u) :: env).
Proof. exact closing_cons. Qed.
(* Laws. *)
Goal forall Gamma A t, typing Gamma t A -> observational_eq Gamma A t t.
Proof. exact observational_refl. Qed.
Goal forall Gamma A t u, observational_eq Gamma A t u -> observational_eq Gamma A u t.
Proof. exact observational_sym. Qed.
Goal forall Gamma A t u v, observational_eq Gamma A t u -> observational_eq Gamma A u v ->
  observational_eq Gamma A t v. Proof. exact observational_trans. Qed.
Goal forall Gamma A t u, typing Gamma t A -> typing Gamma u A -> conv t u ->
  observational_eq Gamma A t u. Proof. exact observational_conversion. Qed.
Goal forall A B f t u, typing empty_ctx f (arrow A B) -> closed_observational_eq A t u ->
  closed_observational_eq B (TApp f t) (TApp f u).
Proof. exact closed_observational_congruence. Qed.
Goal forall A B x c t u k, typing empty_ctx B (TSort k) -> typing (extend empty_ctx x A) c B ->
  closed_observational_eq A t u -> closed_observational_eq B (subst t x c) (subst u x c).
Proof. exact closed_observational_context. Qed.
Goal forall A B f g a b, closed_observational_eq (arrow A B) f g ->
  closed_observational_eq A a b -> closed_observational_eq B (TApp f a) (TApp g b).
Proof. exact closed_observational_application. Qed.
Goal forall Gamma A B t u, observational_eq Gamma A t u -> type_wf Gamma B -> conv A B ->
  observational_eq Gamma B t u. Proof. exact observational_type_conversion. Qed.
Goal forall A t u, closed_observational_eq A t u <->
  typing empty_ctx t A /\ typing empty_ctx u A /\
  forall f r, typing empty_ctx f (arrow A observation_type) -> observation r ->
    (eval (TApp f t) r <-> eval (TApp f u) r).
Proof. exact closed_observational_function_tests. Qed.
(* Example: in (unroll x) and x are not convertible. *)
Lemma reduces_var : forall x w, reduces (TVar x) w -> w = TVar x.
Proof.
  intros x w H. remember (TVar x) as t eqn:E. induction H; [reflexivity|].
  subst t. inversion H; subst; discriminate.
Qed.
Lemma reduces_in : forall t w, reduces (TIn t) w -> exists t', w = TIn t'.
Proof.
  intros t w H. remember (TIn t) as s eqn:E. revert t E.
  induction H; intros t0 E; subst; [eauto|].
  inversion H; subst; try discriminate. eapply IHreduces; reflexivity.
Qed.
Goal forall IT F G i x, ~ conv (TIn (unroll IT F G i (TVar x))) (TVar x).
Proof.
  intros IT F G i x H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [H1 [H2 Ha]]]].
  apply reduces_var in H2; subst w'. apply reduces_in in H1; destruct H1 as [t' ->].
  discriminate Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 5: core metatheory *)
Goal forall Gamma t A, typing Gamma t A -> wf Gamma. Proof. exact context_validity. Qed.
Goal forall Gamma t A, typing Gamma t A -> exists k, typing Gamma A (TSort k).
Proof. exact type_correctness. Qed.
Goal forall Gamma x t A B k, fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A. Proof. exact weakening. Qed.
Goal forall Gamma x A t B u, fresh_in Gamma x -> typing (extend Gamma x A) t B ->
  typing Gamma u A -> typing Gamma (subst u x t) (subst u x B). Proof. exact substitution. Qed.
Goal forall Gamma env t A, closing Gamma env -> typing Gamma t A ->
  typing empty_ctx (instantiate env t) (instantiate env A). Proof. exact closing_substitution. Qed.
Goal forall t u s x, conv t u -> conv (subst s x t) (subst s x u).
Proof. exact conversion_substitution. Qed.
Goal forall Gamma t u A, typing Gamma t A -> step t u -> typing Gamma u A.
Proof. exact preservation. Qed.
Goal forall Gamma t u A, typing Gamma t A -> eval t u -> typing Gamma u A.
Proof. exact preservation_eval. Qed.
Goal forall Gamma t u A, typing Gamma t A -> computation t u -> typing Gamma u A.
Proof. exact named_computation_preservation. Qed.
(* computation = root steps in every position, no eta; it sits between step and reduction. *)
Goal forall t u, step t u -> computation t u. Proof. exact step_computation. Qed.
Goal forall t u, computation t u -> reduction t u. Proof. exact computation_reduction. Qed.
Goal forall x b b', computation b b' -> computation (TLam x b) (TLam x b').
Proof. exact cmp_TLam_b. Qed.
Goal forall t A, typing empty_ctx t A -> value t \/ exists u, step t u. Proof. exact progress. Qed.
Goal forall Gamma t A, typing Gamma t A -> Acc (fun u v => reduction v u) t.
Proof. exact normalization. Qed.
Goal forall t A, typing empty_ctx t A -> exists v, eval t v /\ value v.
Proof. exact normalization_eval. Qed.
(* Confluence and joinability hold for raw terms. *)
Goal forall t u v, reduces t u -> reduces t v ->
  exists w w', reduces u w /\ reduces v w' /\ alpha_equiv w w'. Proof. exact raw_confluence. Qed.
Goal forall t u, conv t u -> exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof. exact raw_conversion_joinability. Qed.
Goal forall Gamma t A u v, typing Gamma t A -> reduces t u -> reduces t v ->
  exists w w', reduces u w /\ reduces v w' /\ alpha_equiv w w'. Proof. exact confluence. Qed.
Goal forall Gamma t u A, typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof. exact conversion_joinability. Qed.
Goal forall t, ~ typing empty_ctx t Bot. Proof. exact consistency. Qed.
Goal forall IT F G i v, typing empty_ctx v (CloseAt IT F G i) -> value v ->
  exists x, v = TIn x /\ typing empty_ctx x (TInterp IT (TApp F i) (carrier IT G)).
Proof. exact canonical_forms_close. Qed.
(* Refuted full preservation: T = Pi A:Set_0. A -> A, f = (\z.\B.z)(\x.x). *)
Definition ex_T := TPi 0 (TSort 0) (TPi 1 (TVar 0) (TVar 0)).
Definition ex_f := TApp (TLam 1 (TLam 2 (TVar 1))) (TLam 3 (TVar 3)).
Goal typing empty_ctx (TLam 0 (TApp ex_f (TVar 0))) ex_T
  /\ reduction (TLam 0 (TApp ex_f (TVar 0))) ex_f /\ ~ typing empty_ctx ex_f ex_T.
Proof. exact unrestricted_eta_counterexample. Qed.
Goal ~ (forall Gamma t u A, typing Gamma t A -> reduction t u -> typing Gamma u A).
Proof. exact full_preservation_refuted. Qed.
(* Derived core rules (abort and unroll are defined in Section 2). *)
Goal forall Gamma k A z, typing Gamma A (TSort k) -> typing Gamma z Bot ->
  typing Gamma (abort k A z) A. Proof. exact abort_typing. Qed.
Goal forall Gamma IT F G i, close_input Gamma IT F G i <->
  typing Gamma IT (TSort 0) /\ typing Gamma F (Def IT) /\ typing Gamma G (Def IT) /\ typing Gamma i IT.
Proof. reflexivity. Qed.
Goal forall Gamma IT F G i x, close_input Gamma IT F G i -> typing Gamma x (CloseAt IT F G i) ->
  typing Gamma (unroll IT F G i x) (TInterp IT (TApp F i) (carrier IT G)).
Proof. exact unroll_typing. Qed.
Goal forall IT F G i x, eval (unroll IT F G i (TIn x)) x. Proof. exact unroll_beta. Qed.
Goal forall Gamma IT F G i x, close_input Gamma IT F G i -> typing Gamma x (CloseAt IT F G i) ->
  observational_eq Gamma (CloseAt IT F G i) (TIn (unroll IT F G i x)) x.
Proof. exact close_roll_unroll. Qed.

(* ------------------------------------------------------------------ *)
(* Section 6: core lemmas cited in the table *)
Goal forall t u sigma tau, alpha_equiv t u ->
  (forall x, In x (free_vars t) -> alpha_equiv (sigma x) (tau x)) ->
  alpha_equiv (substitute sigma t) (substitute tau u). Proof. exact substitute_alpha. Qed.
Goal forall t sigma tau, alpha_equiv (substitute sigma (substitute tau t))
  (substitute (fun v => substitute sigma (tau v)) t). Proof. exact substitute_compose. Qed.
Goal forall t sigma a, In a (free_vars (substitute sigma t)) <->
  exists v, In v (free_vars t) /\ In a (free_vars (sigma v)). Proof. exact free_vars_substitute. Qed.
Goal forall b x y, ~ In y (remove Nat.eq_dec x (free_vars b)) ->
  alpha_equiv (TLam x b) (TLam y (subst (TVar y) x b)). Proof. exact alpha_rename_lam. Qed.
Goal forall A B x y, ~ In y (remove Nat.eq_dec x (free_vars B)) ->
  alpha_equiv (TPi x A B) (TPi y A (subst (TVar y) x B)). Proof. exact alpha_rename_pi. Qed.
Goal forall A B x y, ~ In y (remove Nat.eq_dec x (free_vars B)) ->
  alpha_equiv (TSigma x A B) (TSigma y A (subst (TVar y) x B)). Proof. exact alpha_rename_sigma. Qed.
Goal forall Gamma t A, typing Gamma t A ->
  forall x, In x (free_vars t) -> exists B, lookup Gamma x = Some B. Proof. exact typing_scoped. Qed.
Goal forall Gamma t A x, typing Gamma t A -> fresh_in Gamma x -> ~ In x (free_vars t).
Proof. exact typing_fresh_not_free. Qed.
Goal forall Gamma t A, typing Gamma t A -> forall Delta, wf Delta ->
  (forall x, lookup Gamma x = lookup Delta x) -> typing Delta t A. Proof. exact typing_ctx_equal. Qed.
Goal forall Gamma x y A B, x <> y ->
  ctx_equal (extend (extend Gamma x A) y B) (extend (extend Gamma y B) x A).
Proof. exact ctx_equal_exchange. Qed.
(* Conversion inversion. *)
Goal forall t u h k, conv t u -> term_head t = Some h -> term_head u = Some k -> h = k.
Proof. exact raw_head. Qed.
Goal forall x b, term_head (TLam x b) = None. Proof. reflexivity. Qed.
Goal forall a b, term_head (TPair a b) = None. Proof. reflexivity. Qed.
Goal forall a b, conv (TTag a) (TTag b) -> a = b. Proof. exact conv_tags. Qed.
Goal forall a E b F, conv (TConsE a E) (TConsE b F) -> conv a b /\ conv E F. Proof. exact conv_conse. Qed.
Goal forall x y A B C D, conv (TPi x A B) (TPi y C D) -> conv A C. Proof. exact pi_domain_conversion. Qed.
(* Canonical forms. *)
Goal forall Gamma IT F G i v, typing Gamma v (CloseAt IT F G i) -> value v -> exists x, v = TIn x.
Proof. exact close_value_shape. Qed.
Goal forall Gamma E v, typing Gamma v (TEnumT E) -> value v -> v = TEZero \/ exists n, v = TESucc n.
Proof. exact enum_value_shape. Qed.
Goal forall Gamma IT E D X v, typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
  typing Gamma D (arrow (TEnumT E) (TIDesc IT)) -> typing Gamma X (Family IT) ->
  typing Gamma v (TInterp IT (TIChoice E D) X) -> value v -> exists a b, v = TPair a b.
Proof. exact choice_value_shape. Qed.
Goal forall Gamma t A, typing Gamma t A -> Gamma = empty_ctx -> value t \/ exists u, step t u.
Proof. exact (progress_from_conversion conversion_joinability). Qed.
Goal forall Gamma t, typing Gamma t Bot -> value t -> False.
Proof. exact (bottom_no_value conversion_joinability). Qed.
(* Transport: the named results are the nameless ones. *)
Goal forall Gamma t u T, typing Gamma t T -> step t u -> typing Gamma u T.
Proof. exact named_preservation. Qed.
Goal forall Gamma t A, typing Gamma t A -> Acc (fun u v => reduction v u) t.
Proof. exact named_full_normalization. Qed.

(* ------------------------------------------------------------------ *)
(* Examples of Section 2: lookup maps, natural numbers, positive numbers *)
(* {'a |-> e_a, ...} := \x. switch^k {...} P (e_a, (..., star)) x *)
Lemma ex_lookup_map : forall Gamma k E P b x j,
  typing Gamma E TEnumU -> typing Gamma P (arrow (TEnumT E) (TSort k)) ->
  typing Gamma b (TEPi k E P) -> fresh_in Gamma x ->
  typing Gamma (TPi x (TEnumT E) (TApp P (TVar x))) (TSort j) ->
  typing Gamma (TLam x (TSwitch k E P b (TVar x))) (TPi x (TEnumT E) (TApp P (TVar x))).
Proof.
  intros Gamma k E P b x j HE HP Hb Hx HPi.
  assert (HT : typing Gamma (TEnumT E) (TSort 0)) by now apply ty_enumt.
  assert (Hwf : wf (extend Gamma x (TEnumT E)))
    by (eapply wf_cons; [eapply context_validity; exact HE|exact HT|exact Hx]).
  eapply ty_lam; [exact Hx|exact HPi|].
  apply ty_switch; try (eapply weakening; eassumption).
  apply ty_var; [exact Hwf|apply lookup_extend_same].
Qed.
(* Looking up the second label takes three root steps (variables stand for P, b_0, b_1). *)
Goal run 3 (TApp (TLam 0 (TSwitch 2 (TConsE (TTag "nil") (TConsE (TTag "cons") TNilE)) (TVar 9)
    (TPair (TVar 7) (TPair (TVar 8) TUnit)) (TVar 0))) (TESucc TEZero)) = TVar 8.
Proof. vm_compute. reflexivity. Qed.

(* NatD := \_. 'sigma {'zero,'suc} {'zero |-> '1, 'suc |-> 'var star}, and
   PosD := \_. 'sigma {'zero,'suc} {'zero |-> 'bot, 'suc |-> 'var star}:
   the same labels, with zero hidden by the empty payload. *)
Definition nat_rows : row := [("zero", TI1); ("suc", TIVar TUnit)].
Definition pos_rows : row := [("zero", TIBot); ("suc", TIVar TUnit)].
Definition natD := unit_signature nat_rows.
Definition posD := unit_signature pos_rows.
Goal exists i x m, natD =
  TLam i (TIChoice (TConsE (TTag "zero") (TConsE (TTag "suc") TNilE))
    (TLam x (TSwitch 1 (TConsE (TTag "zero") (TConsE (TTag "suc") TNilE))
       (TLam m (TIDesc TUnitT)) (TPair TI1 (TPair (TIVar TUnit) TUnit)) (TVar x)))).
Proof. do 3 eexists; reflexivity. Qed.
Goal exists i x m, posD =
  TLam i (TIChoice (TConsE (TTag "zero") (TConsE (TTag "suc") TNilE))
    (TLam x (TSwitch 1 (TConsE (TTag "zero") (TConsE (TTag "suc") TNilE))
       (TLam m (TIDesc TUnitT)) (TPair TIBot (TPair (TIVar TUnit) TUnit)) (TVar x)))).
Proof. do 3 eexists; reflexivity. Qed.
Lemma ex_nat_rows : forall Gamma, wf Gamma ->
  row_input Gamma TUnitT nat_rows /\ row_input Gamma TUnitT pos_rows.
Proof.
  intros Gamma Hwf.
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hv : typing Gamma (TIVar TUnit) (TIDesc TUnitT))
    by (apply ty_ivar; [exact HI|now apply ty_unit]).
  split; (split; [exact HI|split]).
  - repeat constructor; cbn; intuition discriminate.
  - apply Forall_cons; [cbn; now apply ty_i1|].
    apply Forall_cons; [cbn; exact Hv|apply Forall_nil].
  - repeat constructor; cbn; intuition discriminate.
  - apply Forall_cons; [cbn; now apply ty_ibot|].
    apply Forall_cons; [cbn; exact Hv|apply Forall_nil].
Qed.
Lemma ex_nat_def : forall Gamma, wf Gamma ->
  typing Gamma natD (Def TUnitT) /\ typing Gamma posD (Def TUnitT).
Proof.
  intros Gamma Hwf. destruct (ex_nat_rows _ Hwf) as [HN HP].
  split; apply (unit_signature_typing weakening); assumption.
Qed.
Ltac sect L := first [eapply (L weakening)|eapply L].
(* A position paired with that constructor's data is a payload of NatD. *)
Lemma ex_nat_inject : forall Gamma X k name D b,
  typing Gamma X (Family TUnitT) -> nth_error nat_rows k = Some (name, D) ->
  typing Gamma b (TInterp TUnitT D X) ->
  typing Gamma (TPair (enum_position k) b) (TInterp TUnitT (TApp natD TUnit) X).
Proof.
  intros Gamma X k name D b HX Hk Hb. pose proof (context_validity _ _ _ HX) as Hwf.
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hs : typing Gamma TUnit TUnitT) by now apply ty_unit.
  destruct (ex_nat_rows _ Hwf) as [HR _]. destruct (ex_nat_def _ Hwf) as [HD _].
  assert (HA : typing Gamma (TApp natD TUnit) (TIDesc TUnitT))
    by (sect def_application; eassumption).
  eapply ty_conv with (A := TInterp TUnitT (row_code TUnitT nat_rows) X).
  - sect row_injection_typing; eassumption.
  - apply ty_interp; assumption.
  - apply cv_compatible, cp_TInterp; try apply cv_refl.
    apply cv_sym, unit_signature_application.
Qed.
(* The two payloads of NatD: (0, star) and (1+0, n) with n : X star. *)
Lemma ex_nat_payloads : forall Gamma X,
  typing Gamma X (Family TUnitT) ->
  typing Gamma (TPair TEZero TUnit) (TInterp TUnitT (TApp natD TUnit) X) /\
  (forall n, typing Gamma n (TApp X TUnit) ->
     typing Gamma (TPair (TESucc TEZero) n) (TInterp TUnitT (TApp natD TUnit) X)).
Proof.
  intros Gamma X HX. pose proof (context_validity _ _ _ HX) as Hwf.
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hs : typing Gamma TUnit TUnitT) by now apply ty_unit.
  split.
  - apply (ex_nat_inject Gamma X 0 "zero" TI1); [exact HX|reflexivity|].
    sect interp_unit; assumption.
  - intros n Hn.
    apply (ex_nat_inject Gamma X 1 "suc" (TIVar TUnit)); [exact HX|reflexivity|].
    sect interp_variable; eassumption.
Qed.
(* iAll and hyps on the two payloads (variables stand for X, P, h, n). *)
Ltac by_run fuel :=
  match goal with |- eval ?t ?u =>
    replace u with (run fuel t) by (vm_compute; reflexivity); apply run_sound end.
Lemma ex_nat_hyps :
  eval (TIAll TUnitT (TApp natD TUnit) (TVar 3) (TPair TEZero TUnit) (TVar 5)) TUnitT
  /\ eval (THyps TUnitT (TApp natD TUnit) (TVar 3) (TVar 5) (TVar 4) (TPair TEZero TUnit)) TUnit
  /\ eval (TIAll TUnitT (TApp natD TUnit) (TVar 3) (TPair (TESucc TEZero) (TVar 6)) (TVar 5))
          (TApp (TVar 5) (TPair TUnit (TVar 6)))
  /\ eval (THyps TUnitT (TApp natD TUnit) (TVar 3) (TVar 5) (TVar 4)
             (TPair (TESucc TEZero) (TVar 6)))
          (TApp (TApp (TVar 4) TUnit) (TVar 6)).
Proof. repeat split; by_run 40. Qed.
(* Nat := mu NatD star, zero := in (0, star), suc n := in (1+0, n). *)
Lemma ex_nat_values : forall Gamma, wf Gamma ->
  typing Gamma (MuAt TUnitT natD TUnit) (TSort 0) /\
  typing Gamma (TIn (TPair TEZero TUnit)) (MuAt TUnitT natD TUnit) /\
  (forall n, typing Gamma n (MuAt TUnitT natD TUnit) ->
     typing Gamma (TIn (TPair (TESucc TEZero) n)) (MuAt TUnitT natD TUnit)).
Proof.
  intros Gamma Hwf.
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hs : typing Gamma TUnit TUnitT) by now apply ty_unit.
  destruct (ex_nat_def _ Hwf) as [HD _].
  assert (HX : typing Gamma (TMuI TUnitT natD) (Family TUnitT)) by now apply ty_mui.
  destruct (ex_nat_payloads _ _ HX) as [Hz Hsuc].
  split; [now apply mu_at_formation|]. split.
  - apply ty_in_mui; assumption.
  - intros n Hn. apply ty_in_mui; try assumption. now apply Hsuc.
Qed.
(* Induction on suc n calls the step with the payload and the hypotheses. *)
Goal forall P s n, exists j y,
  root_step (TInd TUnitT natD P s TUnit (TIn (TPair (TESucc TEZero) n))) =
  Some (TApp (TApp (TApp s TUnit) (TPair (TESucc TEZero) n))
    (THyps TUnitT (TApp natD TUnit) (TMuI TUnitT natD) P
      (TLam j (TLam y (TInd TUnitT natD P s (TVar j) (TVar y)))) (TPair (TESucc TEZero) n))).
Proof. intros; do 2 eexists; reflexivity. Qed.
(* 'bot has no closed payload. *)
Lemma ex_no_bot_payload : forall IT X z,
  ~ typing empty_ctx z (TInterp IT TIBot X).
Proof.
  intros IT X z Hz. apply (consistency z).
  eapply ty_conv; [exact Hz|apply ty_enumt, ty_nile, wf_nil|].
  apply cv_step, st_root; reflexivity.
Qed.
(* close NatD NatD star is the natural numbers again; close PosD NatD star
   keeps both labels, but only suc can be built, over an arbitrary natural
   number. Its values are the same terms as the successors of the former. *)
Lemma ex_pos_values : forall Gamma, wf Gamma ->
  let N := CloseAt TUnitT natD natD TUnit in
  typing Gamma (TIn (TPair TEZero TUnit)) N /\
  (forall n, typing Gamma n N -> typing Gamma (TIn (TPair (TESucc TEZero) n)) N) /\
  (forall n, typing Gamma n N ->
     typing Gamma (TIn (TPair (TESucc TEZero) n)) (CloseAt TUnitT posD natD TUnit)).
Proof.
  intros Gamma Hwf N.
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hs : typing Gamma TUnit TUnitT) by now apply ty_unit.
  destruct (ex_nat_def _ Hwf) as [HD HP]. destruct (ex_nat_rows _ Hwf) as [HR HRP].
  assert (HX : typing Gamma (carrier TUnitT natD) (Family TUnitT)) by now apply ty_close.
  assert (Hvar : forall n, typing Gamma n N ->
    typing Gamma n (TInterp TUnitT (TIVar TUnit) (carrier TUnitT natD)))
    by (intros n Hn; sect interp_variable; eassumption).
  assert (Hc : forall rs k name D b,
    typing Gamma (unit_signature rs) (Def TUnitT) -> row_input Gamma TUnitT rs ->
    nth_error rs k = Some (name, D) ->
    typing Gamma b (TInterp TUnitT D (carrier TUnitT natD)) ->
    typing Gamma (TIn (TPair (enum_position k) b))
      (CloseAt TUnitT (unit_signature rs) natD TUnit)).
  { intros rs k name D b HF Hrs Hk Hb.
    sect close_row_constructor;
      [repeat split; eassumption|exact Hrs|apply unit_signature_application
      |exact Hk|exact Hb]. }
  assert (Hunit : typing Gamma TUnit (TInterp TUnitT TI1 (carrier TUnitT natD)))
    by (sect interp_unit; assumption).
  split; [|split].
  - exact (Hc nat_rows 0 "zero" TI1 TUnit HD HR eq_refl Hunit).
  - intros n Hn. exact (Hc nat_rows 1 "suc" (TIVar TUnit) n HD HR eq_refl (Hvar n Hn)).
  - intros n Hn. exact (Hc pos_rows 1 "suc" (TIVar TUnit) n HP HRP eq_refl (Hvar n Hn)).
Qed.
(* Every closed term of close PosD NatD star evaluates to a suc. *)
Lemma ex_pos_only_suc : forall t,
  typing empty_ctx t (CloseAt TUnitT posD natD TUnit) ->
  exists n, eval t (TIn (TPair (TESucc TEZero) n)) /\
    typing empty_ctx n (CloseAt TUnitT natD natD TUnit).
Proof.
  intros t Ht.
  assert (HI : typing empty_ctx TUnitT (TSort 0)) by apply ty_unitT, wf_nil.
  assert (Hs : typing empty_ctx TUnit TUnitT) by apply ty_unit, wf_nil.
  destruct (ex_nat_def _ wf_nil) as [HD HP]. destruct (ex_nat_rows _ wf_nil) as [_ HRP].
  assert (HV : row_view empty_ctx TUnitT (TApp posD TUnit) pos_rows).
  { constructor; [exact HRP| |apply unit_signature_application].
    sect def_application; eassumption. }
  destruct (canonical_forms_named _ _ _ _ _ _ Ht HV) as [name [D [k [x [Hk [He Hx]]]]]].
  destruct k as [|[|k]]; cbn in Hk.
  - inversion Hk; subst. exfalso. exact (ex_no_bot_payload _ _ _ Hx).
  - inversion Hk; subst. exists x; split; [exact He|].
    eapply ty_conv; [exact Hx|now apply close_at_formation|].
    apply cv_step, st_root; reflexivity.
  - destruct k; discriminate.
Qed.

(* The example lemmas proved in this file use no axioms. *)
Print Assumptions ex_lookup_map.
Print Assumptions ex_nat_def.
Print Assumptions ex_nat_payloads.
Print Assumptions ex_nat_hyps.
Print Assumptions ex_nat_values.
Print Assumptions ex_pos_values.
Print Assumptions ex_no_bot_payload.
Print Assumptions ex_pos_only_suc.
