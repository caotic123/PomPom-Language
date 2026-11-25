(* Machine check of docs/type-rules/calculus.tex, Part II (elaboration).
   Every statement below is transcribed from that document and proved from
   the Rocq definition, constructor or theorem it cites. The "for all j"
   premises of the document are justified by the Forall2 lemmas, and the
   examples about List and NonEmpty are proved here for every element type.
   Build: make -C progress check-docs *)
From Stdlib Require Import List Arith String Lia.
Require Import OpenSignatures OpenSignaturesRowCoherence OpenSignaturesRowViews
  OpenSignaturesDescriptionCoherence.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Section 7.1: rows, signatures, dispatcher *)
Goal row_enum [] = TNilE. Proof. reflexivity. Qed.
Goal forall l D rs, row_enum ((l, D) :: rs) = TConsE (TTag l) (row_enum rs). Proof. reflexivity. Qed.
Goal tuple [] = TUnit. Proof. reflexivity. Qed.
Goal forall t ts, tuple (t :: ts) = TPair t (tuple ts). Proof. reflexivity. Qed.
Goal forall rs, row_tuple rs = tuple (map snd rs). Proof. reflexivity. Qed.
Goal forall IT rs, exists c m, row_branches IT rs =
  TLam c (TSwitch 1 (row_enum rs) (TLam m (TIDesc IT)) (row_tuple rs) (TVar c))
  /\ ~ In m (free_vars (TIDesc IT)).
Proof.
  intros; do 2 eexists; split; [reflexivity|].
  change (free_vars (TIDesc IT)) with (free_vars IT).
  apply above_fresh_not_free with (ts := IT :: map snd rs); [left; reflexivity|lia].
Qed.
Goal forall IT rs, row_code IT rs = TIChoice (row_enum rs) (row_branches IT rs). Proof. reflexivity. Qed.
Goal forall i IT rs, signature i IT rs = TLam i (row_code IT rs). Proof. reflexivity. Qed.
Goal forall Gamma IT rs, row_input Gamma IT rs <->
  typing Gamma IT (TSort 0) /\ NoDup (map fst rs) /\
  Forall (fun e => typing Gamma (snd e) (TIDesc IT)) rs. Proof. reflexivity. Qed.
Goal forall Gamma IT D rs, row_view Gamma IT D rs <->
  row_input Gamma IT rs /\ typing Gamma D (TIDesc IT) /\ conv D (row_code IT rs).
Proof. split; [intros []; auto|intros [? [? ?]]; constructor; auto]. Qed.
(* Names and positions: label_at is defined in OpenSignaturesCore.v and used for rows *)
Goal forall s E, label_at (TConsE (TTag s) E) s TEZero. Proof. exact at_here. Qed.
Goal forall E s n l, label_at E s n -> label_at (TConsE l E) s (TESucc n). Proof. exact at_there. Qed.
Goal forall E E' s n n', conv E E' -> conv n n' -> label_at E s n -> label_at E' s n'.
Proof. exact at_convert. Qed.
Goal forall IT rs X Y, exists c p, handler_motive IT rs X Y =
  TLam c (TPi p (TInterp IT (TApp (row_branches IT rs) (TVar c)) X) Y).
Proof. intros; do 2 eexists; reflexivity. Qed.
Goal forall k IT rs X Y hs, exists z, row_map k IT rs X Y hs =
  TLam z (TApp (TSwitch k (row_enum rs) (handler_motive IT rs X Y) (tuple hs) (TFst (TVar z)))
    (TSnd (TVar z))).
Proof. intros; eexists; reflexivity. Qed.
Goal enum_position 0 = TEZero. Proof. reflexivity. Qed.
Goal forall n, enum_position (S n) = TESucc (enum_position n). Proof. reflexivity. Qed.
Goal forall m, exists y, retag_handler m = TLam y (TPair (enum_position m) (TVar y)).
Proof. intros; eexists; reflexivity. Qed.
Goal forall k Y d, exists y, dead_handler k Y d = TLam y (abort k Y (TApp d (TVar y))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall ts, exists z, identity_for ts = TLam z (TVar z). Proof. intros; eexists; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.2: dead descriptions *)
Goal forall Gamma IT D X, description_input Gamma IT D X <->
  typing Gamma IT (TSort 0) /\ typing Gamma D (TIDesc IT) /\ typing Gamma X (Family IT).
Proof. reflexivity. Qed.
Goal forall Gamma IT D X, description_input Gamma IT D X -> conv D TIBot ->
  exists z, dead Gamma IT D X (TLam z (TVar z)).
Proof. intros; eexists; eapply dead_bot; eassumption. Qed.
Goal forall Gamma IT D X T, description_input Gamma IT D X -> conv D (TIChoice TNilE T) ->
  exists z, dead Gamma IT D X (TLam z (TFst (TVar z))).
Proof. intros; eexists; eapply dead_nil; eassumption. Qed.
Goal forall Gamma IT D X d, description_input Gamma IT D X ->
  typing Gamma d (arrow (TInterp IT D X) Bot) -> dead Gamma IT D X d.
Proof. exact dead_provided. Qed.
Goal forall Gamma IT D X D1 D2 d, description_input Gamma IT D X -> conv D (TIProd D1 D2) ->
  dead Gamma IT D1 X d -> exists z, dead Gamma IT D X (TLam z (TApp d (TFst (TVar z)))).
Proof. intros; eexists; eapply dead_left; eassumption. Qed.
Goal forall Gamma IT D X D1 D2 d, description_input Gamma IT D X -> conv D (TIProd D1 D2) ->
  dead Gamma IT D2 X d -> exists z, dead Gamma IT D X (TLam z (TApp d (TSnd (TVar z)))).
Proof. intros; eexists; eapply dead_right; eassumption. Qed.
Goal forall Gamma IT D X rs ds, description_input Gamma IT D X -> row_view Gamma IT D rs ->
  dead_rows Gamma IT rs X ds -> dead Gamma IT D X (row_map 0 IT rs X Bot ds).
Proof. exact dead_choice. Qed.
(* "forall j" premise of dead_choice *)
Lemma dead_rows_forall2 : forall Gamma IT rs X ds,
  dead_rows Gamma IT rs X ds <-> Forall2 (fun e d => dead Gamma IT (snd e) X d) rs ds.
Proof.
  split.
  - induction 1; constructor; auto.
  - induction 1 as [|[n D] d rs ds Hd Hrest IH]; constructor; auto.
Qed.

(* Description coercions *)
Goal forall Gamma IT D D' X, description_input Gamma IT D X -> description_input Gamma IT D' X ->
  conv D D' -> exists z, desc_sub Gamma IT D D' X (TLam z (TVar z)).
Proof. intros; eexists; eapply ds_conv; eassumption. Qed.
Goal forall Gamma IT D D' X d, dead Gamma IT D X d -> description_input Gamma IT D' X ->
  desc_sub Gamma IT D D' X (dead_handler 0 (TInterp IT D' X) d).
Proof. exact ds_dead. Qed.
Goal forall Gamma IT D D' X rs rt hs, description_input Gamma IT D X ->
  description_input Gamma IT D' X -> row_view Gamma IT D rs -> row_view Gamma IT D' rt ->
  row_handlers Gamma IT X (TInterp IT D' X) rt rs hs ->
  map fst rs = map fst rt ->
  desc_sub Gamma IT D D' X (row_map 0 IT rs X (TInterp IT D' X) hs).
Proof. exact ds_rows. Qed.
(* With the same names on both sides, a live label keeps its position. *)
Lemma ex_enum_position_inj : forall a b, enum_position a = enum_position b -> a = b.
Proof.
  induction a; destruct b; cbn; intros H; try discriminate; [reflexivity|].
  f_equal; apply IHa; now inversion H.
Qed.
Lemma ex_live_target : forall Gamma IT X Y rt rs hs,
  row_handlers Gamma IT X Y rt rs hs -> forall n name D m,
  nth_error rs n = Some (name, D) -> nth_error hs n = Some (retag_handler m) ->
  exists D', nth_error rt m = Some (name, D').
Proof.
  induction 1; intros k nm Dk m Hk Hh.
  - destruct k; discriminate.
  - destruct k as [|k]; cbn in Hk, Hh; [|eauto].
    inversion Hk; subst.
    assert (He : enum_position n = enum_position m)
      by (unfold retag_handler in Hh; cbv zeta in Hh; congruence).
    apply ex_enum_position_inj in He; subst. eauto.
  - destruct k as [|k]; cbn in Hk, Hh; [|eauto].
    unfold retag_handler, dead_handler, abort in Hh; cbv zeta in Hh. discriminate Hh.
Qed.
Lemma ex_live_keeps_position : forall Gamma IT X Y (rt rs : row) hs n name D m,
  map fst rs = map fst rt -> NoDup (map fst rt) ->
  row_handlers Gamma IT X Y rt rs hs ->
  nth_error rs n = Some (name, D) -> nth_error hs n = Some (retag_handler m) -> m = n.
Proof.
  intros Gamma IT X Y rt rs hs n name D m Hnames Hnd Hh Hn Hm.
  destruct (ex_live_target _ _ _ _ _ _ _ Hh _ _ _ _ Hn Hm) as [D' Hrt].
  assert (H1 : nth_error (map fst rt) n = Some name)
    by (rewrite <- Hnames, nth_error_map, Hn; reflexivity).
  assert (H2 : nth_error (map fst rt) m = Some name)
    by (rewrite nth_error_map, Hrt; reflexivity).
  apply (proj1 (NoDup_nth_error _) Hnd); [|congruence].
  apply nth_error_Some; congruence.
Qed.
(* The per-entry relation r_j |-> h_j of rh_live / rh_dead *)
Definition handler_ok Gamma IT X Y (target : row) (e : string * term) (h : term) :=
  (exists m D', nth_error target m = Some (fst e, D') /\
     conv (TInterp IT (snd e) X) (TInterp IT D' X) /\ h = retag_handler m)
  \/ (exists d, dead Gamma IT (snd e) X d /\ h = dead_handler 0 Y d).
Lemma row_handlers_forall2 : forall Gamma IT X Y target rs hs,
  row_handlers Gamma IT X Y target rs hs <-> Forall2 (handler_ok Gamma IT X Y target) rs hs.
Proof.
  split.
  - induction 1; constructor; auto.
    + left; do 2 eexists; repeat split; eassumption.
    + right; eexists; split; [eassumption|reflexivity].
  - induction 1 as [|[n D] h rs hs Hh Hrest IH]; [constructor|].
    destruct Hh as [[m [D' [Hn [Hc ->]]]]|[d [Hd ->]]].
    + eapply rh_live; eassumption.
    + apply rh_dead; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.3: type coercions *)
Goal forall c d, exists x, compose_coercion c d = TLam x (TApp d (TApp c (TVar x))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall y c d, exists f, pi_coercion y c d =
  TLam f (TLam y (TApp d (TApp (TVar f) (TApp c (TVar y))))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall x y c B, coerced_codomain x y c B = subst (TApp c (TVar y)) x B. Proof. reflexivity. Qed.
Goal forall IT F H G i q, exists x, close_coercion IT F H G i q =
  TLam x (TIn (TApp q (unroll IT F G i (TVar x)))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall Gamma A B, type_wf Gamma A -> type_wf Gamma B -> conv A B ->
  exists x, sub Gamma A B (TLam x (TVar x)).
Proof. intros; eexists; eapply su_conv; eassumption. Qed.
Goal forall Gamma A, type_wf Gamma A <-> exists k, typing Gamma A (TSort k). Proof. reflexivity. Qed.
Goal forall Gamma A B C c d, sub Gamma A B c -> sub Gamma B C d ->
  sub Gamma A C (compose_coercion c d). Proof. exact su_trans. Qed.
Goal forall Gamma A k, typing Gamma A (TSort k) ->
  exists z, sub Gamma Bot A (TLam z (abort k A (TVar z))).
Proof. intros; eexists; eapply su_bottom; eassumption. Qed.
Goal forall Gamma x y A B A' B' c d, fresh_in Gamma y ->
  type_wf Gamma (TPi x A B) -> type_wf Gamma (TPi y A' B') -> sub Gamma A' A c ->
  sub (extend Gamma y A') (subst (TApp c (TVar y)) x B) B' d ->
  sub Gamma (TPi x A B) (TPi y A' B') (pi_coercion y c d).
Proof. exact su_pi. Qed.
Goal forall Gamma IT F H G i q, close_input Gamma IT F G i -> close_input Gamma IT H G i ->
  desc_sub Gamma IT (TApp F i) (TApp H i) (carrier IT G) q ->
  sub Gamma (CloseAt IT F G i) (CloseAt IT H G i) (close_coercion IT F H G i q).
Proof. exact su_close. Qed.

(* ------------------------------------------------------------------ *)
(* Section 7.4: synthesis and checking *)
Goal forall Gamma x A, wf Gamma -> lookup Gamma x = Some A -> elab_synth Gamma (EVar x) A (TVar x).
Proof. exact es_var. Qed.
Goal forall Gamma e A t, type_wf Gamma A -> elab_check Gamma e A t -> elab_synth Gamma (EAnn e A) A t.
Proof. exact es_ann. Qed.
Goal forall Gamma x f a A B t u, type_wf Gamma (TPi x A B) -> elab_synth Gamma f (TPi x A B) t ->
  elab_check Gamma a A u -> elab_synth Gamma (EApp f a) (subst u x B) (TApp t u).
Proof. exact es_app. Qed.
Goal forall Gamma i IT rs, fresh_in Gamma i -> typing Gamma IT (TSort 0) ->
  row_input (extend Gamma i IT) IT rs ->
  elab_synth Gamma (ESignature i IT rs) (Def IT) (TLam i (row_code IT rs)).
Proof. exact es_signature. Qed.
Goal forall Gamma IT F G f g, typing Gamma IT (TSort 0) -> elab_check Gamma F (Def IT) f ->
  elab_check Gamma G (Def IT) g -> elab_synth Gamma (EClose IT F G) (Family IT) (TClose IT f g).
Proof. exact es_close. Qed.
Goal forall Gamma t A, typing Gamma t A -> elab_check Gamma (ECore t) A t. Proof. exact ec_core. Qed.
Goal forall Gamma x e A B t, fresh_in Gamma x -> type_wf Gamma (TPi x A B) ->
  elab_check (extend Gamma x A) e B t -> elab_check Gamma (ELam x e) (TPi x A B) (TLam x t).
Proof. exact ec_lam. Qed.
Goal forall Gamma x e e' A B t u, type_wf Gamma (TSigma x A B) -> elab_check Gamma e A t ->
  elab_check Gamma e' (subst t x B) u -> elab_check Gamma (EPair e e') (TSigma x A B) (TPair t u).
Proof. exact ec_pair. Qed.
Goal forall Gamma e A B t, elab_synth Gamma e A t -> type_wf Gamma B -> conv A B ->
  elab_check Gamma e B t. Proof. exact ec_conversion. Qed.
Goal forall Gamma e A B t, elab_check Gamma e A t -> type_wf Gamma B -> conv A B ->
  elab_check Gamma e B t. Proof. exact ec_target_conversion. Qed.
Goal forall Gamma e A B t c, elab_synth Gamma e A t -> sub Gamma A B c ->
  elab_check Gamma e B (TApp c t). Proof. exact ec_subsumption. Qed.
Goal forall Gamma name e IT F G i rs n D u, close_input Gamma IT F G i ->
  row_view Gamma IT (TApp F i) rs -> nth_error rs n = Some (name, D) ->
  elab_check Gamma e (TInterp IT D (carrier IT G)) u ->
  elab_check Gamma (EConstructor name e) (CloseAt IT F G i) (TIn (TPair (enum_position n) u)).
Proof. exact ec_constructor. Qed.
Goal forall k IT F G i Q rs hs x, exists z, case_term k IT F G i Q rs hs x =
  TCloseCase k IT F G i (TLam z Q) (row_map k IT rs (carrier IT G) Q hs) x.
Proof. intros; eexists; reflexivity. Qed.
Goal forall Gamma e Q bs IT F G i x rs k hs, close_input Gamma IT F G i ->
  elab_synth Gamma e (CloseAt IT F G i) x -> typing Gamma Q (TSort k) ->
  row_view Gamma IT (TApp F i) rs -> NoDup (map fst bs) ->
  Forall (fun entry => In (fst entry) (map fst rs)) bs ->
  elab_cases Gamma k IT (carrier IT G) Q bs rs hs ->
  elab_synth Gamma (ECase e Q bs) Q (case_term k IT F G i Q rs hs x).
Proof. exact es_case. Qed.
(* The per-entry relation r_j |> h_j of cases_live / cases_dead *)
Definition clause_ok Gamma k IT X Q (bs : list (string * (nat * expr)))
    (e : string * term) (h : term) :=
  (exists p e' t, In (fst e, (p, e')) bs /\ fresh_in Gamma p /\
     elab_check (extend Gamma p (TInterp IT (snd e) X)) e' Q t /\ h = TLam p t)
  \/ (exists d, ~ In (fst e) (map fst bs) /\ dead Gamma IT (snd e) X d /\ h = dead_handler k Q d).
Lemma elab_cases_forall2 : forall Gamma k IT X Q bs rs hs,
  elab_cases Gamma k IT X Q bs rs hs <-> Forall2 (clause_ok Gamma k IT X Q bs) rs hs.
Proof.
  split.
  - induction 1; constructor; auto.
    + left; do 3 eexists; repeat split; eassumption.
    + right; eexists; repeat split; eassumption.
  - induction 1 as [|[n D] h rs hs Hh Hrest IH]; [constructor|].
    destruct Hh as [[p [e' [t [Hin [Hf [Hc ->]]]]]]|[d [Hn [Hd ->]]]].
    + eapply cases_live; eassumption.
    + apply cases_dead; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Section 8: elaboration metatheory *)
Goal forall Gamma IT rs, row_input Gamma IT rs -> typing Gamma (row_code IT rs) (TIDesc IT).
Proof. exact row_code_typing. Qed.
Goal forall Gamma i IT rs, fresh_in Gamma i -> typing Gamma IT (TSort 0) ->
  row_input (extend Gamma i IT) IT rs -> typing Gamma (signature i IT rs) (Def IT).
Proof. exact signature_typing. Qed.
Goal forall rs n name D, nth_error rs n = Some (name, D) ->
  label_at (row_enum rs) name (enum_position n). Proof. exact row_position_identity. Qed.
Goal forall Gamma rs name a b, NoDup (map fst rs) -> typing Gamma a (TEnumT (row_enum rs)) ->
  typing Gamma b (TEnumT (row_enum rs)) -> label_at (row_enum rs) name a ->
  label_at (row_enum rs) name b -> conv a b. Proof. exact label_resolution_unique. Qed.
Goal forall IT F G i t rs, typing empty_ctx t (CloseAt IT F G i) ->
  row_view empty_ctx IT (TApp F i) rs ->
  exists name D n x, nth_error rs n = Some (name, D) /\
    eval t (TIn (TPair (enum_position n) x)) /\
    typing empty_ctx x (TInterp IT D (carrier IT G)).
Proof. exact canonical_forms_named. Qed.
Goal forall Gamma IT D X d, dead Gamma IT D X d -> typing Gamma d (arrow (TInterp IT D X) Bot).
Proof. exact dead_sound. Qed.
Goal forall IT F G i d, close_input empty_ctx IT F G i ->
  dead empty_ctx IT (TApp F i) (carrier IT G) d -> forall x, ~ typing empty_ctx x (CloseAt IT F G i).
Proof. exact dead_close_uninhabited. Qed.
Goal forall Gamma IT D D' X q, desc_sub Gamma IT D D' X q ->
  typing Gamma q (arrow (TInterp IT D X) (TInterp IT D' X)).
Proof. exact description_subtyping_sound. Qed.
Goal forall Gamma A B c, sub Gamma A B c -> typing Gamma c (arrow A B). Proof. exact subtyping_sound. Qed.
Goal forall Gamma e A t, elab_synth Gamma e A t -> typing Gamma t A. Proof. exact synthesis_sound. Qed.
Goal forall Gamma e A t, elab_check Gamma e A t -> typing Gamma t A. Proof. exact checking_sound. Qed.
Goal forall e A t, elab_check empty_ctx e A t -> value t \/ exists u, step t u.
Proof. exact elaborated_progress. Qed.
Goal forall e A t, elab_check empty_ctx e A t ->
  exists v, eval t v /\ value v /\ typing empty_ctx v A. Proof. exact elaborated_evaluation. Qed.
Goal forall Gamma A B c d, sub Gamma A B c -> sub Gamma A B d ->
  observational_eq Gamma (arrow A B) c d. Proof. exact coercion_coherence. Qed.
Goal forall Gamma e A t u, elab_check Gamma e A t -> elab_check Gamma e A u ->
  observational_eq Gamma A t u. Proof. exact checking_coherence. Qed.
Goal forall Gamma IT X Y target source hs, row_input Gamma IT source -> row_input Gamma IT target ->
  typing Gamma X (Family IT) -> typing Gamma Y (TSort 0) ->
  conv Y (TInterp IT (row_code IT target) X) ->
  row_handlers Gamma IT X Y target source hs ->
  Forall2 (fun entry h => typing Gamma h (arrow (TInterp IT (snd entry) X) Y)) source hs.
Proof. exact row_handlers_sound. Qed.
Goal forall Gamma k IT X Q bs rs hs, row_input Gamma IT rs -> typing Gamma X (Family IT) ->
  typing Gamma Q (TSort k) -> elab_cases Gamma k IT X Q bs rs hs ->
  typing Gamma (tuple hs) (TEPi k (row_enum rs) (handler_motive IT rs X Q)).
Proof. exact case_handlers_sound. Qed.

(* ------------------------------------------------------------------ *)
(* Section 9: row lemmas cited in the table *)
Goal forall k IT rs X Y hs n name D h x, nth_error rs n = Some (name, D) ->
  nth_error hs n = Some h ->
  conv (TApp (row_map k IT rs X Y hs) (TPair (enum_position n) x)) (TApp h x).
Proof. exact row_map_selected. Qed.
Goal forall m x, conv (TApp (retag_handler m) x) (TPair (enum_position m) x).
Proof. exact retag_handler_beta. Qed.
Goal forall IT rs X t, row_input empty_ctx IT rs -> typing empty_ctx X (Family IT) ->
  typing empty_ctx t (TInterp IT (row_code IT rs) X) ->
  exists name D n x, nth_error rs n = Some (name, D) /\ conv t (TPair (enum_position n) x) /\
    typing empty_ctx x (TInterp IT D X). Proof. exact row_payload_canonical. Qed.
Goal forall Gamma IT D rs rt, row_view Gamma IT D rs -> row_view Gamma IT D rt ->
  forall n name C, nth_error rs n = Some (name, C) ->
  exists C', nth_error rt n = Some (name, C') /\ conv C C'.
Proof. exact row_view_position_transport. Qed.
Goal forall IT X Y target source hs, row_handlers empty_ctx IT X Y target source hs ->
  forall n name D x, nth_error source n = Some (name, D) -> typing empty_ctx x (TInterp IT D X) ->
  exists m D', nth_error target m = Some (name, D') /\ nth_error hs n = Some (retag_handler m).
Proof. exact row_handlers_live_at. Qed.
Goal forall (rs : row) name n m D E, NoDup (map fst rs) -> nth_error rs n = Some (name, D) ->
  nth_error rs m = Some (name, E) -> n = m. Proof. exact row_position_unique. Qed.
Goal forall IT D D' X q r t, desc_sub empty_ctx IT D D' X q -> desc_sub empty_ctx IT D D' X r ->
  typing empty_ctx t (TInterp IT D X) -> conv (TApp q t) (TApp r t).
Proof. exact description_coercions_closed_pointwise_coherence. Qed.
Goal forall IT D D' X q t, desc_sub empty_ctx IT D D' X q -> conv D D' ->
  typing empty_ctx t (TInterp IT D X) -> conv (TApp q t) t.
Proof. exact description_conversion_identity. Qed.
Goal forall E D E' D', conv (TIChoice E D) (TIChoice E' D') -> conv E E' /\ conv D D'.
Proof. exact conv_choice. Qed.

(* ------------------------------------------------------------------ *)
(* Running example: NonEmpty keeps both labels of List and hides nil *)
Goal forall A, cons_code A = TISig A (TLam (fresh [A]) (TIVar TUnit)). Proof. reflexivity. Qed.
Goal forall A, list_rows A = [("nil", TI1); ("cons", cons_code A)]. Proof. reflexivity. Qed.
Goal forall A, nonempty_rows A = [("nil", TIBot); ("cons", cons_code A)]. Proof. reflexivity. Qed.
Goal forall A, row_enum (nonempty_rows A) = row_enum (list_rows A). Proof. reflexivity. Qed.
Goal forall A, exists i, list_def A = signature i TUnitT (list_rows A). Proof. intros; eexists; reflexivity. Qed.
Goal forall A, exists i, nonempty_def A = signature i TUnitT (nonempty_rows A).
Proof. intros; eexists; reflexivity. Qed.
Goal forall A, list_type A = CloseAt TUnitT (list_def A) (list_def A) TUnit. Proof. reflexivity. Qed.
Goal forall A, nonempty_type A = CloseAt TUnitT (nonempty_def A) (list_def A) TUnit. Proof. reflexivity. Qed.
Goal forall A, endless_type A = CloseAt TUnitT (nonempty_def A) (nonempty_def A) TUnit. Proof. reflexivity. Qed.
Goal nil_value = TIn (TPair TEZero TUnit). Proof. reflexivity. Qed.
Goal forall a x, cons_value a x = TIn (TPair (enum_position 1) (TPair a x)). Proof. reflexivity. Qed.
(* A nonempty list is the same term as the list it denotes. *)
Goal forall a x, nonempty_value a x = cons_value a x. Proof. reflexivity. Qed.
Lemma ex_interp_cons : forall IT A X,
  conv (TInterp IT (cons_code A) X) (product A (TApp X TUnit)).
Proof.
  intros IT A X. unfold cons_code.
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
(* [[K_A]] X_L == A x List A *)
Goal forall A, conv (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A)))
  (product A (list_type A)).
Proof. intros; apply ex_interp_cons. Qed.
Goal forall Gamma A, typing Gamma A (TSort 0) -> typing Gamma nil_value (list_type A).
Proof. exact nil_typing. Qed.
Goal forall Gamma A a x, typing Gamma A (TSort 0) -> typing Gamma a A ->
  typing Gamma x (list_type A) -> typing Gamma (cons_value a x) (list_type A).
Proof. exact cons_typing. Qed.
Goal forall Gamma A a x, typing Gamma A (TSort 0) -> typing Gamma a A ->
  typing Gamma x (list_type A) -> typing Gamma (nonempty_value a x) (nonempty_type A).
Proof. exact nonempty_cons_typing. Qed.
(* cons sits at position 1 in both rows. *)
Goal forall A, nth_error (list_rows A) 1 = Some ("cons", cons_code A)
  /\ nth_error (nonempty_rows A) 1 = Some ("cons", cons_code A).
Proof. split; reflexivity. Qed.
Goal forall A, label_at (row_enum (list_rows A)) "cons" (enum_position 1)
  /\ label_at (row_enum (nonempty_rows A)) "cons" (enum_position 1).
Proof. intros; split; apply at_there, at_here. Qed.

Lemma ex_unit_small : forall Gamma, wf Gamma -> typing Gamma TUnitT (TSort 0).
Proof. intros; now apply ty_unitT. Qed.
Lemma ex_list_close_input : forall Gamma A, typing Gamma A (TSort 0) ->
  close_input Gamma TUnitT (list_def A) (list_def A) TUnit /\
  close_input Gamma TUnitT (nonempty_def A) (list_def A) TUnit.
Proof.
  intros Gamma A HA. pose proof (context_validity _ _ _ HA) as Hwf.
  destruct (list_definitions_well_typed _ _ HA) as [HL [HN _]].
  assert (HI : typing Gamma TUnitT (TSort 0)) by now apply ty_unitT.
  assert (Hs : typing Gamma TUnit TUnitT) by now apply ty_unit.
  repeat split; assumption.
Qed.
Lemma ex_def_at_unit : forall Gamma D, typing Gamma D (Def TUnitT) ->
  typing Gamma (TApp D TUnit) (TIDesc TUnitT).
Proof.
  intros Gamma D HD. pose proof (context_validity _ _ _ HD) as Hwf.
  first [exact (def_application weakening _ _ _ _ (ty_unitT 0 Hwf) HD (ty_unit Hwf))
        |exact (def_application _ _ _ _ (ty_unitT 0 Hwf) HD (ty_unit Hwf))].
Qed.
Lemma ex_list_view : forall Gamma A, typing Gamma A (TSort 0) ->
  row_view Gamma TUnitT (TApp (list_def A) TUnit) (list_rows A).
Proof.
  intros Gamma A HA. destruct (ex_list_close_input _ _ HA) as [[_ [HL _]] _].
  constructor; [exact (list_rows_typing weakening _ _ HA)|now apply ex_def_at_unit|].
  apply unit_signature_application.
Qed.
Lemma ex_nonempty_view : forall Gamma A, typing Gamma A (TSort 0) ->
  row_view Gamma TUnitT (TApp (nonempty_def A) TUnit) (nonempty_rows A).
Proof.
  intros Gamma A HA. destruct (ex_list_close_input _ _ HA) as [_ [_ [HN _]]].
  constructor; [exact (nonempty_rows_typing weakening _ _ HA)|now apply ex_def_at_unit|].
  apply unit_signature_application.
Qed.
Lemma ex_list_type_formation : forall Gamma A, typing Gamma A (TSort 0) ->
  typing Gamma (list_type A) (TSort 0) /\ typing Gamma (nonempty_type A) (TSort 0).
Proof.
  intros Gamma A HA.
  destruct (ex_list_close_input _ _ HA) as [[HI [HL [_ Hs]]] [_ [HN _]]].
  split; eapply close_at_formation; eassumption.
Qed.

(* Hidden constructors. 'bot has no closed payload, so nil cannot be built
   at NonEmpty A ... *)
Lemma ex_bot_no_payload : forall IT X z, ~ typing empty_ctx z (TInterp IT TIBot X).
Proof.
  intros IT X z Hz. apply (consistency z).
  eapply ty_conv; [exact Hz|apply ty_enumt, ty_nile, wf_nil|].
  apply cv_step, st_root; reflexivity.
Qed.
Lemma ex_hidden_nil_unconstructible : forall A e t,
  ~ elab_check empty_ctx e (TInterp TUnitT TIBot (carrier TUnitT (list_def A))) t.
Proof. intros A e t H. exact (ex_bot_no_payload _ _ _ (checking_sound _ _ _ _ H)). Qed.
(* ... and every closed term of it evaluates to a cons, at List's position. *)
Lemma ex_nonempty_only_cons : forall A t, typing empty_ctx A (TSort 0) ->
  typing empty_ctx t (nonempty_type A) ->
  exists x, eval t (TIn (TPair (enum_position 1) x)) /\
    typing empty_ctx x (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))).
Proof.
  intros A t HA Ht.
  destruct (canonical_forms_named _ _ _ _ _ _ Ht (ex_nonempty_view _ _ HA))
    as [name [D [n [x [Hn [He Hx]]]]]].
  destruct n as [|[|n]]; cbn in Hn.
  - inversion Hn; subst. exfalso. exact (ex_bot_no_payload _ _ _ Hx).
  - inversion Hn; subst. exists x; split; assumption.
  - destruct n; discriminate.
Qed.

(* Row embedding: the same labels on both sides; nil is dead, cons is live
   and keeps position 1. *)
Lemma ex_embed_nonempty_list : forall Gamma A X,
  typing Gamma A (TSort 0) -> typing Gamma X (Family TUnitT) ->
  exists z, desc_sub Gamma TUnitT (row_code TUnitT (nonempty_rows A))
    (row_code TUnitT (list_rows A)) X
    (row_map 0 TUnitT (nonempty_rows A) X
       (TInterp TUnitT (row_code TUnitT (list_rows A)) X)
       [dead_handler 0 (TInterp TUnitT (row_code TUnitT (list_rows A)) X) (TLam z (TVar z));
        retag_handler 1]).
Proof.
  intros Gamma A X HA HX. eexists.
  pose proof (ex_unit_small _ (context_validity _ _ _ HA)) as HI.
  pose proof (nonempty_rows_typing weakening _ _ HA) as HN.
  pose proof (list_rows_typing weakening _ _ HA) as HL.
  pose proof (row_code_typing _ _ _ HN) as HDN.
  pose proof (row_code_typing _ _ _ HL) as HDL.
  apply ds_rows with (rt := list_rows A).
  - repeat split; assumption.
  - repeat split; assumption.
  - constructor; [assumption|assumption|apply cv_refl].
  - constructor; [assumption|assumption|apply cv_refl].
  - apply rh_dead.
    + apply dead_bot; [|apply cv_refl]. repeat split; try assumption. now apply ty_ibot.
    + eapply rh_live with (n := 1); [reflexivity|apply cv_refl|constructor].
  - reflexivity.
Qed.
(* Rows with different labels are not related: the rule needs equal names. *)
Goal forall A, map fst (nonempty_rows A) = map fst (list_rows A). Proof. reflexivity. Qed.
Goal forall A, map fst [("cons", cons_code A)] <> map fst (list_rows A).
Proof. intros A H; discriminate H. Qed.

(* Coercion examples *)
Goal forall A, hidden_nil A = identity_for [TUnitT; TIBot; carrier TUnitT (list_def A)].
Proof. reflexivity. Qed.
Goal forall A, exists x, to_list A = TLam x (TIn (TApp
  (row_map 0 TUnitT (nonempty_rows A) (carrier TUnitT (list_def A))
     (payload TUnitT (list_def A) (list_def A) TUnit)
     [dead_handler 0 (payload TUnitT (list_def A) (list_def A) TUnit) (hidden_nil A);
      retag_handler 1])
  (unroll TUnitT (nonempty_def A) (list_def A) TUnit (TVar x)))).
Proof. intros; eexists; reflexivity. Qed.
Goal forall Gamma A, typing Gamma A (TSort 0) ->
  sub Gamma (nonempty_type A) (list_type A) (to_list A). Proof. exact nonempty_widening. Qed.
(* The coercion returns the value it was given (variables stand for A, a, x). *)
Goal eval (TApp (to_list (TVar 2)) (nonempty_value (TVar 7) (TVar 8)))
          (nonempty_value (TVar 7) (TVar 8)).
Proof.
  replace (nonempty_value (TVar 7) (TVar 8))
    with (run 80 (TApp (to_list (TVar 2)) (nonempty_value (TVar 7) (TVar 8)))) at 2
    by (vm_compute; reflexivity).
  apply run_sound.
Qed.
(* No coercion List A <= NonEmpty A in the context A : Set_0. *)
Lemma ex_no_list_to_nonempty_coercion :
  ~ exists c, sub (extend empty_ctx 0 (TSort 0)) (list_type (TVar 0)) (nonempty_type (TVar 0)) c.
Proof.
  intros [c H]. apply no_uniform_list_downcast. exists (TLam 0 c).
  pose proof (subtyping_sound _ _ _ _ H) as Hc.
  destruct (type_correctness _ _ _ Hc) as [k Hk].
  eapply ty_lam; [reflexivity| |exact Hc].
  eapply ty_pi; [reflexivity|apply ty_sort, wf_nil|exact Hk].
Qed.
Lemma ex_function_coercion : forall Gamma A B x y j k l,
  typing Gamma A (TSort 0) -> typing Gamma B (TSort l) -> ~ In x (free_vars B) ->
  fresh_in Gamma y -> typing Gamma (TPi x (list_type A) B) (TSort j) ->
  typing Gamma (TPi y (nonempty_type A) B) (TSort k) ->
  typing Gamma (nonempty_type A) (TSort 0) ->
  exists z, sub Gamma (TPi x (list_type A) B) (TPi y (nonempty_type A) B)
    (pi_coercion y (to_list A) (TLam z (TVar z))).
Proof.
  intros Gamma A B x y j k l HA HB Hx Hy HP HP' HN. eexists.
  eapply su_pi; [exact Hy|eexists; exact HP|eexists; exact HP'|now apply nonempty_widening|].
  unfold coerced_codomain. rewrite subst_fresh by exact Hx.
  assert (HB' : type_wf (extend Gamma y (nonempty_type A)) B)
    by (exists l; eapply weakening; eassumption).
  exact (su_conv HB' HB' (cv_refl B)).
Qed.

(* Elaboration examples, for every element type A *)
(* The pair (core a, core x) checks against the payload type of cons. *)
Lemma ex_cons_payload : forall Gamma A a x,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma x (list_type A) ->
  elab_check Gamma (EPair (ECore a) (ECore x))
    (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) (TPair a x).
Proof.
  intros Gamma A a x HA Ha Hx.
  destruct (ex_list_close_input _ _ HA) as [[HI [HL _]] _].
  destruct (ex_list_type_formation _ _ HA) as [HLt _].
  assert (HP : typing Gamma (product A (list_type A)) (TSort 0))
    by exact (product_formation weakening _ _ _ 0 0 HA HLt).
  assert (HK : typing Gamma
      (TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))) (TSort 0)).
  { apply ty_interp; [exact HI|exact (cons_code_typing weakening _ _ HA)|now apply ty_close]. }
  eapply ec_target_conversion with (A := product A (list_type A));
    [|exists 0; exact HK|apply cv_sym, ex_interp_cons].
  unfold product. apply ec_pair; [exists 0; exact HP|now apply ec_core|].
  apply ec_core. rewrite subst_fresh; [exact Hx|].
  apply fresh_not_free; right; left; reflexivity.
Qed.
(* cons((core a, core x)) elaborates to the same term at NonEmpty A and List A. *)
Lemma ex_cons_at_nonempty : forall Gamma A a x,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma x (list_type A) ->
  elab_check Gamma (EConstructor "cons" (EPair (ECore a) (ECore x)))
    (nonempty_type A) (cons_value a x).
Proof.
  intros Gamma A a x HA Ha Hx. destruct (ex_list_close_input _ _ HA) as [_ Hci].
  eapply ec_constructor with (rs := nonempty_rows A) (n := 1) (D := cons_code A);
    [exact Hci|now apply ex_nonempty_view|reflexivity|now apply ex_cons_payload].
Qed.
Lemma ex_cons_at_list : forall Gamma A a x,
  typing Gamma A (TSort 0) -> typing Gamma a A -> typing Gamma x (list_type A) ->
  elab_check Gamma (EConstructor "cons" (EPair (ECore a) (ECore x)))
    (list_type A) (cons_value a x).
Proof.
  intros Gamma A a x HA Ha Hx. destruct (ex_list_close_input _ _ HA) as [Hci _].
  eapply ec_constructor with (rs := list_rows A) (n := 1) (D := cons_code A);
    [exact Hci|now apply ex_list_view|reflexivity|now apply ex_cons_payload].
Qed.
Goal singleton_source TUnit =
  EAnn (EConstructor "cons" (EPair (ECore TUnit) (ECore nil_value))) (nonempty_type TUnitT).
Proof. reflexivity. Qed.
Goal elab_check empty_ctx (singleton_source TUnit) (nonempty_type TUnitT)
  (nonempty_value TUnit nil_value). Proof. exact singleton_source_elaborates. Qed.

(* head := \x. case_A x of { cons(p) => core (fst p) }: the nil clause is
   omitted because its payload is dead. *)
Goal forall A, exists x p, head_source A =
  EAnn (ELam x (ECase (EVar x) A [("cons", (p, ECore (TFst (TVar p))))]))
    (arrow (nonempty_type A) A)
  /\ head_term A = TLam x (case_term 0 TUnitT (nonempty_def A) (list_def A) TUnit A
       (nonempty_rows A) [dead_handler 0 A (hidden_nil A); TLam p (TFst (TVar p))] (TVar x)).
Proof. intros; do 2 eexists; split; reflexivity. Qed.
Lemma ex_head_elaborates : forall Gamma A,
  typing Gamma A (TSort 0) ->
  let x := fresh [nonempty_type A; A] in
  fresh_in Gamma x -> fresh_in Gamma (S x) ->
  elab_synth Gamma (head_source A) (arrow (nonempty_type A) A) (head_term A).
Proof.
  intros Gamma A HA x Hx Hp.
  set (N := nonempty_type A) in *. set (p := S x) in *.
  destruct (ex_list_type_formation _ _ HA) as [_ HN]. fold N in HN.
  assert (Harrow : type_wf Gamma (arrow N A))
    by (exists 0; exact (arrow_formation weakening _ _ _ 0 0 HN HA)).
  set (Gx := extend Gamma x N).
  assert (Hwf : wf Gx)
    by (eapply wf_cons; [eapply context_validity; exact HA|exact HN|exact Hx]).
  assert (HAx : typing Gx A (TSort 0)) by (eapply weakening; eassumption).
  destruct (ex_list_close_input _ _ HAx) as [_ Hci].
  unfold head_source, head_term, hidden_nil. fold N. fold x. fold p.
  apply es_ann; [exact Harrow|].
  apply ec_lam; [exact Hx|exact Harrow|]. fold Gx.
  eapply ec_conversion with (A := A); [|exists 0; exact HAx|apply cv_refl].
  eapply es_case with (rs := nonempty_rows A).
  - exact Hci.
  - apply es_var; [exact Hwf|apply lookup_extend_same].
  - exact HAx.
  - now apply ex_nonempty_view.
  - repeat constructor; cbn; tauto.
  - apply Forall_cons; [cbn; auto|apply Forall_nil].
  - destruct Hci as [HIx [_ [HLx _]]].
    assert (HXx : typing Gx (carrier TUnitT (list_def A)) (Family TUnitT)) by now apply ty_close.
    apply cases_dead.
    + cbn; intuition discriminate.
    + apply dead_bot; [|apply cv_refl]. repeat split; try assumption. now apply ty_ibot.
    + set (K := TInterp TUnitT (cons_code A) (carrier TUnitT (list_def A))).
      assert (HK : typing Gx K (TSort 0)).
      { apply ty_interp; [exact HIx|exact (cons_code_typing weakening _ _ HAx)|exact HXx]. }
      assert (Hpx : fresh_in Gx p).
      { unfold fresh_in, Gx. rewrite lookup_extend_other by (subst p; lia). exact Hp. }
      eapply cases_live with (p := p) (e := ECore (TFst (TVar p)));
        [left; reflexivity|exact Hpx| |constructor].
      apply ec_core. fold K.
      set (Gp := extend Gx p K).
      assert (Hwfp : wf Gp) by (eapply wf_cons; eassumption).
      assert (HAp : typing Gp A (TSort 0)) by (eapply weakening; eassumption).
      destruct (ex_list_type_formation _ _ HAp) as [HL _].
      assert (HS : typing Gp (product A (list_type A)) (TSort 0))
        by exact (product_formation weakening _ _ _ 0 0 HAp HL).
      eapply ty_fst with (B := list_type A); [exact HS|].
      eapply ty_conv; [apply ty_var; [exact Hwfp|apply lookup_extend_same]|exact HS|].
      apply ex_interp_cons.
Qed.
Corollary ex_head_elaborates_closed : forall A, typing empty_ctx A (TSort 0) ->
  elab_synth empty_ctx (head_source A) (arrow (nonempty_type A) A) (head_term A).
Proof. intros A HA; apply ex_head_elaborates; [exact HA|reflexivity|reflexivity]. Qed.
(* head and toList compute: at A = 1, and with variables standing for A and a. *)
Goal run 80 (TApp (head_term TUnitT) (singleton TUnit)) = TUnit. Proof. exact singleton_head. Qed.
Goal run 80 (TApp (head_term (TVar 2)) (singleton (TVar 7))) = TVar 7.
Proof. exact head_preserves_open_payload. Qed.
Goal run 80 (TApp (to_list TUnitT) (singleton TUnit)) = cons_value TUnit nil_value.
Proof. exact singleton_retag. Qed.
(* A context that can be closed has no dead witness for '1, so the nil
   clause of a case on List A cannot be omitted. *)
Lemma ex_no_dead_unit : forall Gamma env IT X d,
  closing Gamma env -> description_input Gamma IT TI1 X -> ~ dead Gamma IT TI1 X d.
Proof.
  intros Gamma env IT X d Hc [HIT [HD HX]] Hd.
  pose proof (dead_sound _ _ _ _ _ Hd) as Hty.
  pose proof (context_validity _ _ _ HIT) as Hwf.
  assert (HT : typing Gamma (TInterp IT TI1 X) (TSort 0)) by (apply ty_interp; assumption).
  assert (Hu : typing Gamma TUnit (TInterp IT TI1 X)).
  { eapply ty_conv; [now apply ty_unit|exact HT|].
    apply cv_sym, cv_step, st_root; reflexivity. }
  assert (HB : typing Gamma Bot (TSort 0)) by now apply ty_enumt, ty_nile.
  assert (Happ : typing Gamma (TApp d TUnit) Bot).
  { eapply arrow_app with (A := TInterp IT TI1 X);
      [exact weakening|exact HT|exact HB|exact Hty|exact Hu]. }
  pose proof (closing_substitution _ _ _ _ Hc Happ) as Hclosed.
  rewrite (instantiate_closed env Bot) in Hclosed by reflexivity.
  exact (consistency _ Hclosed).
Qed.
(* The context x : List 1 of such a case can be closed, by x := nil. *)
Goal closing (extend empty_ctx 0 (list_type TUnitT)) [(0, nil_value)].
Proof.
  assert (H1 : typing empty_ctx TUnitT (TSort 0)) by apply ty_unitT, wf_nil.
  destruct (ex_list_type_formation _ _ H1) as [HL _].
  apply closing_cons; [reflexivity| |apply closing_nil|exact (nil_typing _ _ H1)].
  eapply wf_cons; [apply wf_nil|exact HL|reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Section 10: list theorems *)
Goal forall Gamma A, typing Gamma A (TSort 0) ->
  typing Gamma (head_term A) (arrow (nonempty_type A) A) /\
  typing Gamma (tail_term A) (arrow (nonempty_type A) (list_type A)).
Proof. exact nonempty_observers_typing. Qed.
Goal ~ exists c, typing empty_ctx c
  (TPi 0 (TSort 0) (arrow (list_type (TVar 0)) (nonempty_type (TVar 0)))).
Proof. exact no_uniform_list_downcast. Qed.
Goal forall A, typing empty_ctx A (TSort 0) -> forall x, ~ typing empty_ctx x (endless_type A).
Proof. exact self_restricted_list_empty. Qed.
Goal forall Gamma A a x, typing Gamma A (TSort 0) -> typing Gamma a A ->
  typing Gamma x (tree_type A) -> typing Gamma (cons_value a x) (tree_type A).
Proof. exact reused_tree_cons_typing. Qed.

(* The example lemmas proved in this file use no axioms. *)
Print Assumptions ex_live_keeps_position.
Print Assumptions ex_embed_nonempty_list.
Print Assumptions ex_no_list_to_nonempty_coercion.
Print Assumptions ex_function_coercion.
Print Assumptions ex_nonempty_only_cons.
Print Assumptions ex_hidden_nil_unconstructible.
Print Assumptions ex_cons_at_nonempty.
Print Assumptions ex_cons_at_list.
Print Assumptions ex_head_elaborates.
Print Assumptions ex_no_dead_unit.
