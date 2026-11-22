(* Typed annotated normal forms erase to raw normal forms.

   Proved simultaneously with two freshness facts, by strong induction on
   term size:
   - GF: in a typed normal term, a variable absent from the erasure, from
     the type, and from the types of newer context entries is absent from
     every annotation;
   - NF: an elimination form additionally has a principal type free of
     that variable.
   The eta case of the main statement uses NF: a raw eta redex in the
   erasure whose annotated function still mentions the bound variable
   cannot occur in a typed normal term. *)
From Stdlib Require Import List Arith Bool Lia Wf_nat.
Require Export annotated.ACfHelpers.
Import ListNotations.

Definition LN t := forall Delta T, typing Delta t T -> anormal t -> raw_normal (erase t).
Definition GF t := forall Delta T x, typing Delta t T -> anormal t ->
  raw_fresh x (erase t) -> raw_fresh x T -> ctx_fresh Delta x -> occurs x t = false.
Definition NF t := forall Delta T x, typing Delta t T -> anormal t ->
  raw_fresh x (erase t) -> ctx_fresh Delta x -> elim_form t ->
  occurs x t = false /\ exists P, raw_fresh x P /\ RC.type_comparison P T.
Definition PN t := LN t /\ GF t /\ NF t.
Definition below t := forall y, tsize y < tsize t -> PN y.

Lemma LN_use : forall f Delta T s, PN f -> typing Delta f T -> anormal f ->
  RCore.reduction (erase f) s -> False.
Proof. intros f Delta T s [HL _] HT HN HR; exact (HL _ _ HT HN _ HR). Qed.
Lemma LN_normal : forall f Delta T, PN f -> typing Delta f T -> anormal f ->
  raw_normal (erase f).
Proof. intros f Delta T [HL _] HT HN; exact (HL _ _ HT HN). Qed.
Lemma GF_use : forall f Delta T x, PN f -> typing Delta f T -> anormal f ->
  raw_fresh x (erase f) -> raw_fresh x T -> ctx_fresh Delta x -> occurs x f = false.
Proof. intros f Delta T x [_ [HG _]]; eauto. Qed.
Lemma NF_use : forall f Delta T x, PN f -> typing Delta f T -> anormal f ->
  raw_fresh x (erase f) -> ctx_fresh Delta x -> elim_form f ->
  occurs x f = false /\ exists P, raw_fresh x P /\ RC.type_comparison P T.
Proof. intros f Delta T x [_ [_ HN]]; eauto. Qed.

Lemma GF_from_NF : forall t, elim_form t -> NF t -> GF t.
Proof.
  intros t He HN Delta T x HT Hn HE _ Hctx.
  exact (proj1 (HN Delta T x HT Hn HE Hctx He)).
Qed.
Lemma NF_trivial : forall t, (elim_form t -> False) -> NF t.
Proof. intros t He Delta T x _ _ _ _ H; contradiction (He H). Qed.

(* ---- raw normal forms of compound types ---- *)
Ltac rn_close :=
  let s := fresh "s" in let Hs := fresh "Hs" in
  intros s Hs; inversion Hs; subst;
  try (cbn [RCore.root_step] in *; discriminate);
  match goal with
  | N : raw_normal ?a, H : RCore.reduction ?a _ |- _ => exact (N _ H)
  end.
Lemma rn_TPi : forall A B, raw_normal A -> raw_normal B -> raw_normal (Raw.TPi A B).
Proof. intros; rn_close. Qed.
Lemma rn_TSigma : forall A B, raw_normal A -> raw_normal B -> raw_normal (Raw.TSigma A B).
Proof. intros; rn_close. Qed.
Lemma rn_TIDesc : forall A, raw_normal A -> raw_normal (Raw.TIDesc A).
Proof. intros; rn_close. Qed.
Lemma rn_TEnumT : forall A, raw_normal A -> raw_normal (Raw.TEnumT A).
Proof. intros; rn_close. Qed.
Lemma rn_TConsE : forall A B, raw_normal A -> raw_normal B -> raw_normal (Raw.TConsE A B).
Proof. intros; rn_close. Qed.
Lemma rn_TMuI : forall A B, raw_normal A -> raw_normal B -> raw_normal (Raw.TMuI A B).
Proof. intros; rn_close. Qed.
Lemma rn_TClose : forall A B C, raw_normal A -> raw_normal B -> raw_normal C ->
  raw_normal (Raw.TClose A B C).
Proof. intros; rn_close. Qed.
Lemma rn_app_mui : forall A B a, raw_normal (Raw.TMuI A B) -> raw_normal a ->
  raw_normal (Raw.TApp (Raw.TMuI A B) a).
Proof. intros; rn_close. Qed.
Lemma rn_app_close : forall A B C a, raw_normal (Raw.TClose A B C) -> raw_normal a ->
  raw_normal (Raw.TApp (Raw.TClose A B C) a).
Proof. intros; rn_close. Qed.

(* ---- inversion of raw freshness ---- *)
Ltac lift_eqs_to_fresh :=
  repeat match goal with
  | E : erase ?f = Raw.lift 1 ?c ?r0 |- _ =>
      let H := fresh "Hfr" in assert (H : raw_fresh c (erase f)) by (exists r0; exact E); clear E
  | E : ?a = Raw.lift 1 ?c ?r0 |- _ =>
      let H := fresh "Hfr" in assert (H : raw_fresh c a) by (exists r0; exact E); clear E
  end.
Ltac rfresh_inv H :=
  let r := fresh "r" in let E := fresh "E" in destruct H as [r E];
  destruct r; cbn [Raw.lift] in E; try discriminate;
  try (match type of E with context [if ?b then _ else _] => destruct b; discriminate end);
  try (injection E; clear E; intros); lift_eqs_to_fresh.
Ltac fresh_inv H := cbn [erase] in H; rfresh_inv H.

Lemma rf_TVar_inv : forall x n, raw_fresh x (Raw.TVar n) -> n <> x.
Proof.
  intros x n [r E]; destruct r; cbn [Raw.lift] in E; try discriminate.
  destruct (Nat.ltb_spec n0 x); inversion E; subst; lia.
Qed.

(* ---- shared tactics ---- *)
Ltac split_hyp H :=
  match type of H with
  | exists _, _ => let x := fresh "g" in let H2 := fresh "Hg" in
      destruct H as [x H2]; split_hyp H2
  | _ /\ _ => let H1 := fresh "Hg" in let H2 := fresh "Hg" in
      destruct H as [H1 H2]; split_hyp H1; split_hyp H2
  | _ => idtac
  end.

Ltac gen H :=
  let G := fresh "G" in
  match type of H with
  | typing _ (TVar _) _ => pose proof (var_generation _ _ _ H I) as G
  | typing _ (TSort _) _ => pose proof (sort_generation _ _ _ H I) as G
  | typing _ (TPi _ _) _ => pose proof (pi_generation _ _ _ H I) as G
  | typing _ (TLam _ _ _) _ => pose proof (lambda_generation _ _ _ H _ _ _ eq_refl) as G
  | typing _ (TApp _ _ _ _) _ => pose proof (application_generation _ _ _ H _ _ _ _ eq_refl) as G
  | typing _ (TSigma _ _) _ => pose proof (sigma_generation _ _ _ H I) as G
  | typing _ (TPair _ _ _ _) _ => pose proof (pair_generation _ _ _ H _ _ _ _ eq_refl) as G
  | typing _ (TFst _ _ _) _ => pose proof (fst_generation _ _ _ H I) as G
  | typing _ (TSnd _ _ _) _ => pose proof (snd_generation _ _ _ H I) as G
  | typing _ (TConsE _ _) _ => pose proof (conse_generation _ _ _ H I) as G
  | typing _ (TEnumT _) _ => pose proof (enumt_generation _ _ _ H I) as G
  | typing _ (TEZero _ _) _ => pose proof (zero_generation _ _ _ H I) as G
  | typing _ (TESucc _ _ _) _ => pose proof (succ_generation _ _ _ H I) as G
  | typing _ (TEPi _ _ _) _ => pose proof (epi_generation _ _ _ H I) as G
  | typing _ (TSwitch _ _ _ _ _) _ => pose proof (switch_generation _ _ _ H I) as G
  | typing _ (TIDesc _) _ => pose proof (idesc_generation _ _ _ H I) as G
  | typing _ (TIVar _ _) _ => pose proof (ivar_generation _ _ _ H I) as G
  | typing _ (TI1 _) _ => pose proof (i1_generation _ _ _ H I) as G
  | typing _ (TIBot _) _ => pose proof (ibot_generation _ _ _ H I) as G
  | typing _ (TIProd _ _ _) _ => pose proof (iprod_generation _ _ _ H I) as G
  | typing _ (TIPi _ _ _) _ => pose proof (ipi_generation _ _ _ H I) as G
  | typing _ (TISig _ _ _) _ => pose proof (isig_generation _ _ _ H I) as G
  | typing _ (TIChoice _ _ _) _ => pose proof (ichoice_generation _ _ _ H I) as G
  | typing _ (TInterp _ _ _) _ => pose proof (interp_generation _ _ _ H I) as G
  | typing _ (TMuI _ _) _ => pose proof (mui_generation _ _ _ H I) as G
  | typing _ (TInMu _ _ _ _) _ => pose proof (in_mui_generation _ _ _ H I) as G
  | typing _ (TInClose _ _ _ _ _) _ => pose proof (in_close_generation _ _ _ H I) as G
  | typing _ (TIAll _ _ _ _ _) _ => pose proof (iall_generation _ _ _ H I) as G
  | typing _ (THyps _ _ _ _ _ _) _ => pose proof (hyps_generation _ _ _ H I) as G
  | typing _ (TInd _ _ _ _ _ _) _ => pose proof (ind_generation _ _ _ H I) as G
  | typing _ (TClose _ _ _) _ => pose proof (close_generation _ _ _ H I) as G
  | typing _ (TCloseCase _ _ _ _ _ _ _ _) _ => pose proof (close_case_generation _ _ _ H I) as G
  | typing _ (TCloseInd _ _ _ _ _ _ _) _ => pose proof (close_ind_generation _ _ _ H I) as G
  | typing _ ?t _ => pose proof (constant_generation _ _ _ H _ eq_refl) as G
  end;
  split_hyp G;
  repeat match goal with
  | E : ?C _ = ?C _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ = ?C _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ = ?C _ _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ _ = ?C _ _ _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ _ _ = ?C _ _ _ _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ _ _ _ = ?C _ _ _ _ _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ |- _ => injection E; clear E; intros; subst
  | E : ?C _ _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ _ |- _ => injection E; clear E; intros; subst
  end.

Ltac size_below Hb f := exact (Hb f ltac:(cbn [tsize]; lia)).

Ltac ln_tac Hb :=
  let Delta := fresh "Delta" in let T := fresh "T" in let HT := fresh "HT" in
  let HN := fresh "HN" in let s := fresh "s" in let Hs := fresh "Hs" in
  intros Delta T HT HN s Hs; gen HT; cbn [erase] in Hs; inversion Hs; subst;
  first
    [ match goal with Hr : RCore.root_step _ = Some _ |- _ =>
        exact (typed_normal_no_root _ _ _ _ HT HN Hr) end
    | match goal with
      | HR : RCore.reduction (erase ?f) _, HTf : typing ?D ?f ?Tf |- _ =>
          exact (LN_use f D Tf _ (Hb f ltac:(cbn [tsize]; lia)) HTf ltac:(subnormal) HR)
      end ].

Ltac gf_goal Hb :=
  match goal with
  | |- occurs ?c ?f = false =>
      first
        [ assumption
        | reflexivity
        | match goal with HTf : typing ?D f ?Tf |- _ =>
            apply (GF_use f D Tf c (Hb f ltac:(cbn [tsize]; lia)) HTf);
            [ subnormal | assumption | rfresh
            | solve [assumption | apply ctx_fresh_extend; assumption] ]
          end ]
  end.
Ltac close_occurs Hb :=
  cbn [occurs]; repeat (apply Bool.orb_false_iff; split);
  first [reflexivity | gf_goal Hb].

Ltac nf_simple Hb :=
  let Delta := fresh "Delta" in let T := fresh "T" in let x := fresh "x" in
  let HT := fresh "HT" in let HN := fresh "HN" in let HE := fresh "HE" in
  let Hctx := fresh "Hctx" in
  intros Delta T x HT HN HE Hctx _; gen HT; fresh_inv HE; split;
  [ close_occurs Hb
  | match goal with Hc : RC.type_comparison ?P T |- _ =>
      exists P; split; [rfresh|exact Hc] end ].

Ltac gf_simple Hb :=
  let Delta := fresh "Delta" in let T := fresh "T" in let x := fresh "x" in
  let HT := fresh "HT" in let HN := fresh "HN" in let HE := fresh "HE" in
  let HTf := fresh "HTf" in let Hctx := fresh "Hctx" in
  intros Delta T x HT HN HE HTf Hctx; gen HT; fresh_inv HE; close_occurs Hb.

Ltac leaf_normal Hb :=
  match goal with
  | |- raw_normal (erase ?f) =>
      match goal with HTf : typing ?D f ?Tf |- _ =>
        exact (LN_normal f D Tf (Hb f ltac:(cbn [tsize]; lia)) HTf ltac:(subnormal))
      end
  end.
Ltac compound_normal Hb :=
  repeat first
    [ apply rn_app_mui | apply rn_app_close | apply rn_TPi | apply rn_TSigma
    | apply rn_TIDesc | apply rn_TEnumT | apply rn_TConsE | apply rn_TMuI
    | apply rn_TClose | leaf_normal Hb ].

(* Annotations fixed by a rigid principal type. *)
Lemma type_fresh_rigid : forall P T x h, RC.type_comparison P T ->
  RG.term_head P = Some h -> h <> RG.h_pi -> h <> RG.h_sort ->
  raw_normal P -> raw_fresh x T -> raw_fresh x P.
Proof.
  intros P T x h HC HP Hpi Hs HN HT.
  eapply raw_normal_conv_fresh; [exact HN|eapply cmp_rigid_conv; eassumption|exact HT].
Qed.

Ltac gf_rigid Hb :=
  let Delta := fresh "Delta" in let T := fresh "T" in let x := fresh "x" in
  let HT := fresh "HT" in let HN := fresh "HN" in let HE := fresh "HE" in
  let HTf := fresh "HTf" in let Hctx := fresh "Hctx" in
  intros Delta T x HT HN HE HTf Hctx; gen HT; fresh_inv HE;
  match goal with Hc : RC.type_comparison ?P T |- _ =>
    let HPn := fresh "HPn" in let HPf := fresh "HPf" in
    assert (HPn : raw_normal P) by (compound_normal Hb);
    assert (HPf : raw_fresh x P) by
      (eapply type_fresh_rigid; [exact Hc|reflexivity|discriminate|discriminate|exact HPn|exact HTf]);
    repeat (rfresh_inv HPf)
  end;
  repeat match goal with
  | H : raw_fresh _ (Raw.TConsE _ _) |- _ => rfresh_inv H
  | H : raw_fresh _ (Raw.TMuI _ _) |- _ => rfresh_inv H
  | H : raw_fresh _ (Raw.TClose _ _ _) |- _ => rfresh_inv H
  end;
  close_occurs Hb.

(* ---- per-constructor cases ---- *)
Ltac case_simple Hb := split; [ln_tac Hb|split; [gf_simple Hb|apply NF_trivial; cbn; tauto]].
Ltac case_elim Hb :=
  match goal with |- PN ?t =>
    let HNF := fresh "HNF" in assert (HNF : NF t) by nf_simple Hb;
    split; [ln_tac Hb|split; [apply GF_from_NF; [exact I|exact HNF]|exact HNF]]
  end.
Ltac case_rigid Hb := split; [ln_tac Hb|split; [gf_rigid Hb|apply NF_trivial; cbn; tauto]].

Lemma pn_TSort : forall k, below (TSort k) -> PN (TSort k).
Proof. intros k Hb; case_simple Hb. Qed.
Lemma pn_TPi : forall A B, below (TPi A B) -> PN (TPi A B).
Proof. intros A B Hb; case_simple Hb. Qed.
Lemma pn_TSigma : forall A B, below (TSigma A B) -> PN (TSigma A B).
Proof. intros A B Hb; case_simple Hb. Qed.
Lemma pn_TUnitT : below TUnitT -> PN TUnitT.
Proof. intros Hb; case_simple Hb. Qed.
Lemma pn_TUnit : below TUnit -> PN TUnit.
Proof. intros Hb; case_simple Hb. Qed.
Lemma pn_TUId : below TUId -> PN TUId.
Proof. intros Hb; case_simple Hb. Qed.
Lemma pn_TTag : forall s, below (TTag s) -> PN (TTag s).
Proof. intros s Hb; case_simple Hb. Qed.
Lemma pn_TEnumU : below TEnumU -> PN TEnumU.
Proof. intros Hb; case_simple Hb. Qed.
Lemma pn_TNilE : below TNilE -> PN TNilE.
Proof. intros Hb; case_simple Hb. Qed.
Lemma pn_TConsE : forall a b, below (TConsE a b) -> PN (TConsE a b).
Proof. intros a b Hb; case_simple Hb. Qed.
Lemma pn_TEnumT : forall E, below (TEnumT E) -> PN (TEnumT E).
Proof. intros E Hb; case_simple Hb. Qed.
Lemma pn_TIDesc : forall IT, below (TIDesc IT) -> PN (TIDesc IT).
Proof. intros IT Hb; case_simple Hb. Qed.

Lemma pn_TEPi : forall k E P, below (TEPi k E P) -> PN (TEPi k E P).
Proof. intros k E P Hb; case_elim Hb. Qed.
Lemma pn_TSwitch : forall k E P p e, below (TSwitch k E P p e) -> PN (TSwitch k E P p e).
Proof. intros k E P p e Hb; case_elim Hb. Qed.
Lemma pn_TInterp : forall IT D X, below (TInterp IT D X) -> PN (TInterp IT D X).
Proof. intros IT D X Hb; case_elim Hb. Qed.
Lemma pn_TMuI : forall IT D, below (TMuI IT D) -> PN (TMuI IT D).
Proof. intros IT D Hb; case_elim Hb. Qed.
Lemma pn_TInd : forall IT D P st i x, below (TInd IT D P st i x) -> PN (TInd IT D P st i x).
Proof. intros IT D P st i x Hb; case_elim Hb. Qed.
Lemma pn_TIAll : forall IT D X xs P, below (TIAll IT D X xs P) -> PN (TIAll IT D X xs P).
Proof. intros IT D X xs P Hb; case_elim Hb. Qed.
Lemma pn_THyps : forall IT D X P h xs, below (THyps IT D X P h xs) -> PN (THyps IT D X P h xs).
Proof. intros IT D X P h xs Hb; case_elim Hb. Qed.
Lemma pn_TClose : forall IT F G, below (TClose IT F G) -> PN (TClose IT F G).
Proof. intros IT F G Hb; case_elim Hb. Qed.
Lemma pn_TCloseCase : forall k IT F G i Q b x,
  below (TCloseCase k IT F G i Q b x) -> PN (TCloseCase k IT F G i Q b x).
Proof. intros k IT F G i Q b x Hb; case_elim Hb. Qed.
Lemma pn_TCloseInd : forall IT G P st F i x,
  below (TCloseInd IT G P st F i x) -> PN (TCloseInd IT G P st F i x).
Proof. intros IT G P st F i x Hb; case_elim Hb. Qed.

Lemma pn_TEZero : forall tag E, below (TEZero tag E) -> PN (TEZero tag E).
Proof. intros tag E Hb; case_rigid Hb. Qed.
Lemma pn_TESucc : forall tag E n, below (TESucc tag E n) -> PN (TESucc tag E n).
Proof. intros tag E n Hb; case_rigid Hb. Qed.
Lemma pn_TIVar : forall IT i, below (TIVar IT i) -> PN (TIVar IT i).
Proof. intros IT i Hb; case_rigid Hb. Qed.
Lemma pn_TI1 : forall IT, below (TI1 IT) -> PN (TI1 IT).
Proof. intros IT Hb; case_rigid Hb. Qed.
Lemma pn_TIBot : forall IT, below (TIBot IT) -> PN (TIBot IT).
Proof. intros IT Hb; case_rigid Hb. Qed.
Lemma pn_TIProd : forall IT A B, below (TIProd IT A B) -> PN (TIProd IT A B).
Proof. intros IT A B Hb; case_rigid Hb. Qed.
Lemma pn_TIPi : forall IT A D, below (TIPi IT A D) -> PN (TIPi IT A D).
Proof. intros IT A D Hb; case_rigid Hb. Qed.
Lemma pn_TISig : forall IT A D, below (TISig IT A D) -> PN (TISig IT A D).
Proof. intros IT A D Hb; case_rigid Hb. Qed.
Lemma pn_TIChoice : forall IT E D, below (TIChoice IT E D) -> PN (TIChoice IT E D).
Proof. intros IT E D Hb; case_rigid Hb. Qed.
Lemma pn_TInMu : forall IT D i xs, below (TInMu IT D i xs) -> PN (TInMu IT D i xs).
Proof. intros IT D i xs Hb; case_rigid Hb. Qed.
Lemma pn_TInClose : forall IT F G i xs, below (TInClose IT F G i xs) -> PN (TInClose IT F G i xs).
Proof. intros IT F G i xs Hb; case_rigid Hb. Qed.

Lemma raw_fresh_sigma_inv : forall x A B, raw_fresh x (Raw.TSigma A B) ->
  raw_fresh x A /\ raw_fresh (S x) B.
Proof.
  intros x A B [r0 H]; destruct r0; cbn [Raw.lift] in H; try discriminate.
  - destruct (n <? x); discriminate.
  - inversion H; subst; split; eexists; reflexivity.
Qed.

Lemma pn_TVar : forall n, below (TVar n) -> PN (TVar n).
Proof.
  intros n Hb.
  assert (HNF : NF (TVar n)).
  { intros Delta T x HT HN HE Hctx _; gen HT.
    pose proof (rf_TVar_inv _ _ HE) as Hn; split.
    - cbn [occurs]; now apply Nat.eqb_neq.
    - match goal with Hc : RC.type_comparison ?P T, Hl : nth_error Delta ?m = Some _ |- _ =>
        exists P; split; [|exact Hc];
        destruct (Nat.lt_ge_cases m x) as [Hlt|Hge];
        [eapply Hctx; eassumption|apply raw_fresh_old_lift; exact Hge] end. }
  split; [ln_tac Hb|split; [apply GF_from_NF; [exact I|exact HNF]|exact HNF]].
Qed.

Lemma pn_TApp : forall C D g a, below (TApp C D g a) -> PN (TApp C D g a).
Proof.
  intros C D g a Hb.
  assert (HNF : NF (TApp C D g a)).
  { intros Delta T x HT HN HE Hctx _; gen HT; fresh_inv HE.
    assert (Hgn : anormal g) by subnormal.
    match goal with Hg : typing Delta g (Raw.TPi _ _) |- _ =>
      destruct (pi_typed_shape _ _ _ _ _ Hg (RCore.cv_refl _)) as [[A' [B' [b ->]]]|Hel];
      [exfalso; eapply HN; apply step_root, root_beta|];
      destruct (NF_use g _ _ x (Hb g ltac:(cbn [tsize]; lia)) Hg Hgn
        ltac:(assumption) Hctx Hel) as [Hgx [Pg [HPg HcPg]]] end.
    assert (HPi : raw_normal (Raw.TPi (erase C) (erase D))) by compound_normal Hb.
    destruct (raw_fresh_pi_inv _ _ _ (comparison_fresh_right x _ _ HcPg HPi HPg))
      as [HCf HDf].
    split.
    - close_occurs Hb.
    - match goal with Hc : RC.type_comparison ?P T |- _ =>
        exists P; split; [rfresh|exact Hc] end. }
  split; [ln_tac Hb|split; [apply GF_from_NF; [exact I|exact HNF]|exact HNF]].
Qed.

Lemma pn_TFst : forall A B p, below (TFst A B p) -> PN (TFst A B p).
Proof.
  intros A B p Hb.
  assert (HNF : NF (TFst A B p)).
  { intros Delta T x HT HN HE Hctx _; gen HT; fresh_inv HE.
    match goal with Hp : typing Delta ?p (Raw.TSigma _ _) |- _ =>
      let Hpn := fresh "Hpn" in
      assert (Hpn : anormal p) by subnormal;
      destruct (sigma_typed_shape _ _ _ _ _ Hp (RCore.cv_refl _)) as [[A' [B' [a' [b' ->]]]]|Hel];
      [exfalso; eapply HN; apply step_root, root_fst|];
      destruct (NF_use p _ _ x (Hb p ltac:(cbn [tsize]; lia)) Hp Hpn
        ltac:(assumption) Hctx Hel) as [Hpx [Pp [HPp HcPp]]] end.
    match type of HcPp with RC.type_comparison _ ?S =>
      let HSg := fresh "HSg" in
      assert (HSg : raw_normal S) by compound_normal Hb;
      destruct (raw_fresh_sigma_inv _ _ _ (comparison_fresh_right x _ _ HcPp HSg HPp))
        as [HAf HBf] end.
    split.
    - close_occurs Hb.
    - match goal with Hc : RC.type_comparison ?P T |- _ =>
        exists P; split; [rfresh|exact Hc] end. }
  split; [ln_tac Hb|split; [apply GF_from_NF; [exact I|exact HNF]|exact HNF]].
Qed.

Lemma pn_TSnd : forall A B p, below (TSnd A B p) -> PN (TSnd A B p).
Proof.
  intros A B p Hb.
  assert (HNF : NF (TSnd A B p)).
  { intros Delta T x HT HN HE Hctx _; gen HT; fresh_inv HE.
    match goal with Hp : typing Delta ?p (Raw.TSigma _ _) |- _ =>
      let Hpn := fresh "Hpn" in
      assert (Hpn : anormal p) by subnormal;
      destruct (sigma_typed_shape _ _ _ _ _ Hp (RCore.cv_refl _)) as [[A' [B' [a' [b' ->]]]]|Hel];
      [exfalso; eapply HN; apply step_root, root_snd|];
      destruct (NF_use p _ _ x (Hb p ltac:(cbn [tsize]; lia)) Hp Hpn
        ltac:(assumption) Hctx Hel) as [Hpx [Pp [HPp HcPp]]] end.
    match type of HcPp with RC.type_comparison _ ?S =>
      let HSg := fresh "HSg" in
      assert (HSg : raw_normal S) by compound_normal Hb;
      destruct (raw_fresh_sigma_inv _ _ _ (comparison_fresh_right x _ _ HcPp HSg HPp))
        as [HAf HBf] end.
    split.
    - close_occurs Hb.
    - match goal with Hc : RC.type_comparison ?P T |- _ =>
        exists P; split; [rfresh|exact Hc] end. }
  split; [ln_tac Hb|split; [apply GF_from_NF; [exact I|exact HNF]|exact HNF]].
Qed.

Lemma pn_TPair : forall A B a b, below (TPair A B a b) -> PN (TPair A B a b).
Proof.
  intros A B a b Hb; split; [ln_tac Hb|split; [|apply NF_trivial; cbn; tauto]].
  intros Delta T x HT HN HE HTf Hctx; gen HT; fresh_inv HE.
  match goal with Hc : RC.type_comparison (Raw.TSigma _ _) T |- _ =>
    pose proof (comparison_sigma_source _ _ _ Hc) as Hconv end.
  assert (HSg : raw_normal (Raw.TSigma (erase A) (erase B))) by compound_normal Hb.
  destruct (raw_fresh_sigma_inv _ _ _ (raw_normal_conv_fresh x _ _ HSg Hconv HTf))
    as [HAf HBf].
  close_occurs Hb.
Qed.

Lemma pn_TLam : forall A B b, below (TLam A B b) -> PN (TLam A B b).
Proof.
  intros A B b Hb; split; [|split; [|apply NF_trivial; cbn; tauto]].
  - intros Delta T HT HN s Hs; gen HT; cbn [erase] in Hs; inversion Hs; subst.
    all: first
      [ match goal with Hr : RCore.root_step _ = Some _ |- _ =>
          exact (typed_normal_no_root _ _ _ _ HT HN Hr) end
      | match goal with HR : RCore.reduction (erase ?f) _, HTf : typing ?D ?f ?Tf |- _ =>
          exact (LN_use f D Tf _ (Hb f ltac:(cbn [tsize]; lia)) HTf ltac:(subnormal) HR) end
      | idtac ].
    (* a raw eta redex in the erasure *)
    match goal with
    | H : _ = erase b |- _ => symmetry in H
    | H : erase b = _ |- _ => idtac
    end.
    match goal with H : erase b = _ |- _ => rename H into Heq end.
    assert (Hbn : anormal b) by subnormal.
    destruct b; cbn [erase] in Heq; try discriminate.
    injection Heq as Hf Ha.
    destruct b4; cbn [erase] in Ha; try discriminate.
    injection Ha as Hn0; subst.
    match goal with Hbody : typing _ (TApp _ _ _ (TVar 0)) _ |- _ => gen Hbody end.
    assert (Hfn : anormal b3) by subnormal.
    match goal with Hf' : typing _ b3 (Raw.TPi _ _) |- _ =>
      destruct (pi_typed_shape _ _ _ _ _ Hf' (RCore.cv_refl _)) as [[A' [B' [c ->]]]|Hel];
      [eapply HN; apply step_context, cp_TLam_b, step_root, root_beta|];
      destruct (NF_use b3 _ _ 0 (Hb b3 ltac:(cbn [tsize]; lia)) Hf' Hfn
        (ex_intro _ s Hf) (ctx_fresh_zero _) Hel) as [Hocc _] end.
    apply occurs_false_iff_lift in Hocc; destruct Hocc as [f0 ->].
    eapply HN; apply step_eta, eta_contract_root.
  - intros Delta T x HT HN HE HTf Hctx; gen HT; fresh_inv HE.
    match goal with Hc : RC.type_comparison (Raw.TPi _ _) T |- _ =>
      assert (HPi : raw_normal (Raw.TPi (erase A) (erase B))) by compound_normal Hb;
      destruct (raw_fresh_pi_inv _ _ _ (comparison_fresh_left x _ _ Hc HPi HTf)) as [HAf HBf]
    end.
    close_occurs Hb.
Qed.

Theorem pn_all : forall t, PN t.
Proof.
  intro t; induction t as [t IH] using (well_founded_induction
    (well_founded_ltof _ tsize)).
  destruct t.
  all: first
    [ apply pn_TVar | apply pn_TSort | apply pn_TPi | apply pn_TLam | apply pn_TApp
    | apply pn_TSigma | apply pn_TPair | apply pn_TFst | apply pn_TSnd
    | apply pn_TUnitT | apply pn_TUnit | apply pn_TUId | apply pn_TTag
    | apply pn_TEnumU | apply pn_TNilE | apply pn_TConsE | apply pn_TEnumT
    | apply pn_TEZero | apply pn_TESucc | apply pn_TEPi | apply pn_TSwitch
    | apply pn_TIDesc | apply pn_TIVar | apply pn_TI1 | apply pn_TIBot
    | apply pn_TIProd | apply pn_TIPi | apply pn_TISig | apply pn_TIChoice
    | apply pn_TInterp | apply pn_TMuI | apply pn_TInMu | apply pn_TInClose
    | apply pn_TInd | apply pn_TIAll | apply pn_THyps | apply pn_TClose
    | apply pn_TCloseCase | apply pn_TCloseInd ];
    exact IH.
Qed.

(* Typed annotated normal forms erase to raw normal forms. *)
Theorem typed_normal_erasure : forall Delta t T, typing Delta t T -> anormal t ->
  raw_normal (erase t).
Proof. intros Delta t T; exact (proj1 (pn_all t) Delta T). Qed.

Print Assumptions typed_normal_erasure.
