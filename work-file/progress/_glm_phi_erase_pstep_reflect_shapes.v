(* GLM worker — atomic shape inversions for phi_erase, feeding the mutual
   pstep / pbranches reflection of the erased-sorts parent factor.
   Every lemma inverts one constructor of the erased image:

     phi_erase t = C ...   ==>   t = C ... with phi_erase components.

   The only collapsing clause of phi_erase is TMuS (_ := TMuS TUnit), so
   TMuS is inverted without constraining the preimage body while forcing
   the image body to be TUnit.  Branch lists are inverted through the
   erasing map, cell by cell. *)

Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* -- binary-node shapes ---------------------------------------------------- *)

Lemma erase_shape_pi_glm : forall t A B,
    phi_erase t = TPi A B ->
    exists x y, t = TPi x y /\ phi_erase x = A /\ phi_erase y = B.
Proof.
  intros t A B H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_app_glm : forall t f a,
    phi_erase t = TApp f a ->
    exists x y, t = TApp x y /\ phi_erase x = f /\ phi_erase y = a.
Proof.
  intros t f a H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_sigma_glm : forall t A B,
    phi_erase t = TSigma A B ->
    exists x y, t = TSigma x y /\ phi_erase x = A /\ phi_erase y = B.
Proof.
  intros t A B H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_pair_glm : forall t a b,
    phi_erase t = TPair a b ->
    exists x y, t = TPair x y /\ phi_erase x = a /\ phi_erase y = b.
Proof.
  intros t a b H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_conse_glm : forall t tg E,
    phi_erase t = TConsE tg E ->
    exists x y, t = TConsE x y /\ phi_erase x = tg /\ phi_erase y = E.
Proof.
  intros t tg E H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_epi_glm : forall t E P,
    phi_erase t = TEPi E P ->
    exists x y, t = TEPi x y /\ phi_erase x = E /\ phi_erase y = P.
Proof.
  intros t E P H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_iprod_glm : forall t A B,
    phi_erase t = TIProd A B ->
    exists x y, t = TIProd x y /\ phi_erase x = A /\ phi_erase y = B.
Proof.
  intros t A B H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_ipi_glm : forall t S T,
    phi_erase t = TIPi S T ->
    exists x y, t = TIPi x y /\ phi_erase x = S /\ phi_erase y = T.
Proof.
  intros t S T H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_isig_glm : forall t S T,
    phi_erase t = TISig S T ->
    exists x y, t = TISig x y /\ phi_erase x = S /\ phi_erase y = T.
Proof.
  intros t S T H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_ichoice_glm : forall t E T,
    phi_erase t = TIChoice E T ->
    exists x y, t = TIChoice x y /\ phi_erase x = E /\ phi_erase y = T.
Proof.
  intros t E T H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_interp_glm : forall t D X,
    phi_erase t = TInterp D X ->
    exists x y, t = TInterp x y /\ phi_erase x = D /\ phi_erase y = X.
Proof.
  intros t D X H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2. eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

(* -- unary-node shapes ----------------------------------------------------- *)

Lemma erase_shape_lam_glm : forall t b,
    phi_erase t = TLam b ->
    exists x, t = TLam x /\ phi_erase x = b.
Proof.
  intros t b H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_fst_glm : forall t p,
    phi_erase t = TFst p ->
    exists x, t = TFst x /\ phi_erase x = p.
Proof.
  intros t p H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_snd_glm : forall t p,
    phi_erase t = TSnd p ->
    exists x, t = TSnd x /\ phi_erase x = p.
Proof.
  intros t p H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_enumt_glm : forall t E,
    phi_erase t = TEnumT E ->
    exists x, t = TEnumT x /\ phi_erase x = E.
Proof.
  intros t E H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_esucc_glm : forall t n,
    phi_erase t = TESucc n ->
    exists x, t = TESucc x /\ phi_erase x = n.
Proof.
  intros t n H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_idesc_glm : forall t IT,
    phi_erase t = TIDesc IT ->
    exists x, t = TIDesc x /\ phi_erase x = IT.
Proof.
  intros t IT H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_ivar_glm : forall t i,
    phi_erase t = TIVar i ->
    exists x, t = TIVar x /\ phi_erase x = i.
Proof.
  intros t i H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_mui_glm : forall t R,
    phi_erase t = TMuI R ->
    exists x, t = TMuI x /\ phi_erase x = R.
Proof.
  intros t R H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_tin_glm : forall t x,
    phi_erase t = TIn x ->
    exists y, t = TIn y /\ phi_erase y = x.
Proof.
  intros t x H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_list_glm : forall t A,
    phi_erase t = TList A ->
    exists x, t = TList x /\ phi_erase x = A.
Proof.
  intros t A H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_lnil_glm : forall t A,
    phi_erase t = TLNil A ->
    exists x, t = TLNil x /\ phi_erase x = A.
Proof.
  intros t A H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_tag_glm : forall t s,
    phi_erase t = TTag s -> t = TTag s.
Proof.
  intros t s H. destruct t; cbn [phi_erase] in H; try discriminate.
  now injection H.
Qed.

(* -- nullary-node shapes --------------------------------------------------- *)

Lemma erase_shape_unitt_glm : forall t, phi_erase t = TUnitT -> t = TUnitT.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_unit_glm : forall t, phi_erase t = TUnit -> t = TUnit.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_uid_glm : forall t, phi_erase t = TUId -> t = TUId.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_enumu_glm : forall t, phi_erase t = TEnumU -> t = TEnumU.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_nile_glm : forall t, phi_erase t = TNilE -> t = TNilE.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_ezero_glm : forall t, phi_erase t = TEZero -> t = TEZero.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

Lemma erase_shape_i1_glm : forall t, phi_erase t = TI1 -> t = TI1.
Proof. intros t H. destruct t; cbn [phi_erase] in H; try discriminate. reflexivity. Qed.

(* -- larger-node shapes ---------------------------------------------------- *)

Lemma erase_shape_switch_glm : forall t E P p e,
    phi_erase t = TSwitch E P p e ->
    exists y1 y2 y3 y4,
      t = TSwitch y1 y2 y3 y4 /\ phi_erase y1 = E /\ phi_erase y2 = P /\
      phi_erase y3 = p /\ phi_erase y4 = e.
Proof.
  intros t E P p e H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3 H4.
  eexists; eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_ind_glm : forall t R P stp i x,
    phi_erase t = TInd R P stp i x ->
    exists y1 y2 y3 y4 y5,
      t = TInd y1 y2 y3 y4 y5 /\ phi_erase y1 = R /\ phi_erase y2 = P /\
      phi_erase y3 = stp /\ phi_erase y4 = i /\ phi_erase y5 = x.
Proof.
  intros t R P stp i x H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3 H4 H5.
  eexists; eexists; eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_iall_glm : forall t D X xs P,
    phi_erase t = TIAll D X xs P ->
    exists y1 y2 y3 y4,
      t = TIAll y1 y2 y3 y4 /\ phi_erase y1 = D /\ phi_erase y2 = X /\
      phi_erase y3 = xs /\ phi_erase y4 = P.
Proof.
  intros t D X xs P H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3 H4.
  eexists; eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_hyps_glm : forall t D X P h xs,
    phi_erase t = THyps D X P h xs ->
    exists y1 y2 y3 y4 y5,
      t = THyps y1 y2 y3 y4 y5 /\ phi_erase y1 = D /\ phi_erase y2 = X /\
      phi_erase y3 = P /\ phi_erase y4 = h /\ phi_erase y5 = xs.
Proof.
  intros t D X P h xs H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3 H4 H5.
  eexists; eexists; eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_lcons_glm : forall t A a l,
    phi_erase t = TLCons A a l ->
    exists y1 y2 y3,
      t = TLCons y1 y2 y3 /\ phi_erase y1 = A /\ phi_erase y2 = a /\
      phi_erase y3 = l.
Proof.
  intros t A a l H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3.
  eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

Lemma erase_shape_case_glm : forall t M Q bs,
    phi_erase t = TCase M Q bs ->
    exists x y l,
      t = TCase x y l /\ phi_erase x = M /\ phi_erase y = Q /\
      map (fun '(c,b) => (phi_erase c, phi_erase b)) l = bs.
Proof.
  intros t M Q bs H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1 H2 H3.
  eexists; eexists; eexists.
  repeat split; solve [reflexivity | eassumption].
Qed.

(* -- the collapsing node: TMuS erases its body to TUnit -------------------- *)

Lemma erase_shape_mus_glm : forall t S,
    phi_erase t = TMuS S -> exists b, t = TMuS b /\ S = TUnit.
Proof.
  intros t S H. destruct t; cbn [phi_erase] in H; try discriminate.
  injection H as H1. eexists.
  split; [reflexivity | symmetry; exact H1].
Qed.

(* -- inversions of the erasing map on branch lists -------------------------- *)

Lemma erase_map_nil_inv_glm : forall bs0,
    map (fun '(c,b) => (phi_erase c, phi_erase b)) bs0 = [] -> bs0 = [].
Proof.
  intros bs0 H. destruct bs0 as [|[c b] rest]; cbn [map phi_erase] in H;
    try discriminate. reflexivity.
Qed.

Lemma erase_map_cons_inv_glm : forall bs0 c b rest,
    map (fun '(c,b) => (phi_erase c, phi_erase b)) bs0 = (c,b) :: rest ->
    exists c0 b0 rest0,
      bs0 = (c0,b0) :: rest0 /\ phi_erase c0 = c /\ phi_erase b0 = b /\
      map (fun '(c,b) => (phi_erase c, phi_erase b)) rest0 = rest.
Proof.
  intros bs0 c b rest H.
  destruct bs0 as [|[c0 b0] rest0]; cbn [map phi_erase] in H; try discriminate.
  injection H as H1 H2 H3.
  exists c0, b0, rest0.
  repeat split; solve [reflexivity | eassumption].
Qed.

(* -- a small pstep shape inversion (needed by the TMuS case) ---------------- *)

Lemma pstep_tunit_inv_glm : forall u, pstep TUnit u -> u = TUnit.
Proof. intros u H. now inversion H. Qed.

Print Assumptions erase_shape_mus_glm.
Print Assumptions erase_map_cons_inv_glm.
Print Assumptions pstep_tunit_inv_glm.
