(* ========================================================================== *)
(*  Progress.v — a proof of TypeRules.v's progress conjecture, RELATIVE to a  *)
(*  small, explicitly named interface of confluence-grade facts about the     *)
(*  untyped conversion (the §10 obligations this file does NOT discharge).    *)
(*                                                                            *)
(*  Theorem progress_proved at the end has the exact statement of the         *)
(*  progress conjecture; Print Assumptions lists what it stands on:           *)
(*    conv_whd, conv_enumt_inj, conv_pos, spine_covered, muapp_sort           *)
(*    (this file's interface), and canonical_forms_sig (TypeRules §8).        *)
(*  Everything else — canonical forms, typing inversion, the first-match     *)
(*  selection argument — is proved.                                           *)
(* ========================================================================== *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules.

(* ------------------------------------------------------------------ *)
(*  Term size, the induction measure                                   *)
(* ------------------------------------------------------------------ *)

Definition bsizeF (f : term -> nat) :=
  fix bsz (l : list (term * term)) : nat :=
    match l with
    | [] => 0
    | (c, b) :: l' => f c + f b + bsz l'
    end.

Fixpoint tsize (t : term) : nat :=
  match t with
  | TVar _ | TSort _ | TUnitT | TUnit | TUId | TTag _ | TEnumU | TNilE
  | TEZero | TI1 => 1
  | TLam b => S (tsize b)
  | TESucc n => S (tsize n)
  | TEnumT E => S (tsize E)
  | TIDesc IT => S (tsize IT)
  | TIVar i => S (tsize i)
  | TMuI R => S (tsize R)
  | TMuS Sf => S (tsize Sf)
  | TIn x => S (tsize x)
  | TFst p | TSnd p => S (tsize p)
  | TList A | TLNil A => S (tsize A)
  | TPi a b | TApp a b | TSigma a b | TPair a b | TConsE a b | TEPi a b
  | TIProd a b | TIPi a b | TISig a b | TIChoice a b | TInterp a b =>
      S (tsize a + tsize b)
  | TLCons a b c => S (tsize a + tsize b + tsize c)
  | TSwitch a b c d => S (tsize a + tsize b + tsize c + tsize d)
  | TIAll a b c d => S (tsize a + tsize b + tsize c + tsize d)
  | THyps a b c d e => S (tsize a + tsize b + tsize c + tsize d + tsize e)
  | TInd a b c d e => S (tsize a + tsize b + tsize c + tsize d + tsize e)
  | TCase M Q bs => S (tsize M + tsize Q + bsizeF tsize bs)
  end.

Notation bsize := (bsizeF tsize).

Lemma tsize_pos : forall t, 1 <= tsize t.
Proof. destruct t; cbn; lia. Qed.

Lemma bsize_in : forall bs c b, In (c, b) bs -> tsize c + tsize b <= bsize bs.
Proof.
  induction bs as [|[c0 b0] bs IH]; cbn; intros c b Hin.
  - destruct Hin.
  - destruct Hin as [Hin | Hin].
    + inversion Hin; subst; lia.
    + specialize (IH _ _ Hin); lia.
Qed.

Lemma tsize_case_bs : forall M Q bs c b,
    In (c, b) bs -> tsize c < tsize (TCase M Q bs).
Proof.
  intros M Q bs c b Hin.
  pose proof (bsize_in bs c b Hin) as H.
  pose proof (tsize_pos b) as Hb.
  change (tsize (TCase M Q bs)) with (S (tsize M + tsize Q + bsize bs)).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  Small helpers                                                      *)
(* ------------------------------------------------------------------ *)

Lemma eval_trans : forall a b c, eval a b -> eval b c -> eval a c.
Proof.
  intros a b c H; revert c; induction H; intros; eauto.
  eapply ev_step; eauto.
Qed.

Lemma conv_of_eval : forall t u, eval t u -> conv t u.
Proof.
  intros t u H; induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply cv_step; exact H | exact IHeval].
Qed.

Lemma check_of_synth : forall G t A, synth G t A -> check G t A.
Proof. intros; eapply ch_conv; [eassumption | apply cv_refl]. Qed.

(* canonical positions are step-normal (also proved in the smoke suite;
   needed here for the eval-invariance of a canonical scrutinee tag) *)
Lemma pos_step_normal : forall c n, enum_pos c n -> forall c', ~ step c c'.
Proof.
  intros c n H. induction H; intros c' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHenum_pos; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(*  Weak-head classification                                           *)
(* ------------------------------------------------------------------ *)

Inductive htag : Type :=
| HSort | HPi | HSigma | HUnitT | HUId | HEnumU | HEnumT | HIDesc | HList
| HMuIApp | HMuSApp | HNilE | HConsE.

(* Top-level shapes.  All classified shapes are completely step-normal:
   none has a head rule, and none has an argument congruence (TApp with a
   μ head included — st_app1 needs the function to step and μ formers do
   not).  λ is deliberately UNclassified: eta makes it head-promiscuous. *)
Inductive hshape : term -> htag -> Prop :=
| hs_sort   : forall k, hshape (TSort k) HSort
| hs_pi     : forall A B, hshape (TPi A B) HPi
| hs_sigma  : forall A B, hshape (TSigma A B) HSigma
| hs_unitT  : hshape TUnitT HUnitT
| hs_uid    : hshape TUId HUId
| hs_enumu  : hshape TEnumU HEnumU
| hs_enumt  : forall E, hshape (TEnumT E) HEnumT
| hs_idesc  : forall IT, hshape (TIDesc IT) HIDesc
| hs_list   : forall A, hshape (TList A) HList
| hs_muiapp : forall R i, hshape (TApp (TMuI R) i) HMuIApp
| hs_musapp : forall Sf i, hshape (TApp (TMuS Sf) i) HMuSApp
| hs_nile   : hshape TNilE HNilE
| hs_conse  : forall tg E, hshape (TConsE tg E) HConsE.

Definition whd (T : term) (h : htag) : Prop :=
  exists T', eval T T' /\ hshape T' h.

Lemma whd_shape : forall T h, hshape T h -> whd T h.
Proof. intros; exists T; split; [apply ev_refl | assumption]. Qed.

(* ------------------------------------------------------------------ *)
(*  THE ASSUMPTION INTERFACE — confluence-grade facts about conv       *)
(*  (the §10 conversion metatheory), stated as narrowly as the proof   *)
(*  needs.  Each is a consequence of confluence-modulo-eta/phi of the  *)
(*  raw reduction; none is proved here.                                *)
(* ------------------------------------------------------------------ *)

(* conversion cannot cross weak-head classes (λ is unclassified, so eta
   never witnesses a crossing; cv_phi stays inside HMuSApp) *)
Conjecture conv_whd : forall t u h1 h2,
    conv t u -> whd t h1 -> whd u h2 -> h1 = h2.

(* EnumT is injective up to conversion *)
Conjecture conv_enumt_inj : forall E1 E2,
    conv (TEnumT E1) (TEnumT E2) -> conv E1 E2.

(* conversion-related canonical positions are the same position *)
Conjecture conv_pos : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.

(* a spine member of a covered list is convertible to a clause label
   (spine_mem and covers both walk reducts of L; confluence aligns them) *)
Conjecture spine_covered : forall L a Psi,
    spine_mem a L -> covers Psi L -> exists d, In d Psi /\ conv a d.

(* a stuck μ-application value classifies only as a sort: its type is
   Set₀ up to conversion (Π-injectivity + substitution-compatibility) *)
Conjecture muapp_sort : forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.

(* ------------------------------------------------------------------ *)
(*  Canonical-form data per class                                      *)
(* ------------------------------------------------------------------ *)

Definition canon (t : term) (h : htag) (U : term) : Prop :=
  match h with
  | HPi => (exists b, t = TLam b) \/ (exists R, t = TMuI R) \/
           (exists Sf, t = TMuS Sf)
  | HSigma => exists a b, t = TPair a b
  | HUnitT => t = TUnit
  | HEnumU => t = TNilE \/ exists tg E, t = TConsE tg E
  | HEnumT =>
      exists tg E0, conv (TEnumT (TConsE tg E0)) U /\
      (t = TEZero \/
       exists n', t = TESucc n' /\ exists E1, check [] n' (TEnumT E1))
  | HIDesc =>
      (exists i, t = TIVar i) \/ t = TI1 \/
      (exists A B, t = TIProd A B) \/ (exists Sd T, t = TIPi Sd T) \/
      (exists Sd T, t = TISig Sd T) \/ (exists E T, t = TIChoice E T)
  | HMuIApp => exists xs, t = TIn xs
  | HMuSApp => exists c xs E0, t = TIn (TPair c xs) /\ check [] c (TEnumT E0)
  | _ => True
  end.

(* a μˢ-typed canonical also serves at μᴵ class (Sig-forget widening) *)
Lemma canon_mus_to_mui : forall t U U',
    canon t HMuSApp U -> canon t HMuIApp U'.
Proof.
  intros t U U' Hc. destruct Hc as [c [xs [E0 [-> _]]]].
  exists (TPair c xs); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Subtyping transport.  A pure-conversion chain keeps the SAME U (so  *)
(*  the U-dependent HEnumT payload survives); the proper subtyping      *)
(*  rules can only land in the four classes below, whose canonical      *)
(*  payloads do not mention U.                                          *)
(* ------------------------------------------------------------------ *)

Lemma sub_transport : forall G A B, sub G A B ->
    forall U h, conv B U -> whd U h ->
    conv A U \/
    ((h = HSort \/ h = HPi \/ h = HMuSApp) /\
     exists U', conv A U' /\ whd U' h) \/
    (h = HMuIApp /\
     exists U', conv A U' /\ (whd U' HMuIApp \/ whd U' HMuSApp)).
Proof.
  intros G A B Hsub. induction Hsub; intros U h HcU Hwhd.
  - (* su_conv *) left. eapply cv_trans; eassumption.
  - (* su_trans *)
    destruct (IHHsub2 U h HcU Hwhd) as
      [HXU | [[Hh [U' [HcU' Hw']]] | [Heq [U' [HcU' Hw']]]]].
    + exact (IHHsub1 U h HXU Hwhd).
    + destruct (IHHsub1 U' h HcU' Hw') as
        [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
      * right; left. split; [exact Hh | exists U'; split; assumption].
      * right; left. split; [exact Hh | exists U''; split; assumption].
      * subst h. destruct Hh as [Hh | [Hh | Hh]]; discriminate Hh.
    + subst h. destruct Hw' as [Hw' | Hw'].
      * destruct (IHHsub1 U' HMuIApp HcU' Hw') as
          [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
        -- right; right. split; [reflexivity |].
           exists U'. split; [exact HAU' | left; exact Hw'].
        -- destruct Hh2 as [Hh2 | [Hh2 | Hh2]]; discriminate Hh2.
        -- right; right. split; [reflexivity |].
           exists U''. split; [exact HcU'' | exact Hw''].
      * destruct (IHHsub1 U' HMuSApp HcU' Hw') as
          [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
        -- right; right. split; [reflexivity |].
           exists U'. split; [exact HAU' | right; exact Hw'].
        -- right; right. split; [reflexivity |].
           exists U''. split; [exact HcU'' | right; exact Hw''].
        -- discriminate Heq2.
  - (* su_sort *)
    assert (HSort = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [left; reflexivity |].
    exists (TSort j). split; [apply cv_refl | apply whd_shape; constructor].
  - (* su_pi *)
    assert (HPi = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [right; left; reflexivity |].
    eexists. split; [apply cv_refl | apply whd_shape; constructor].
  - (* su_forget *)
    assert (HMuIApp = h) as <-.
    { eapply conv_whd;
        [exact HcU | apply whd_shape; unfold Carrier; constructor | exact Hwhd]. }
    right; right. split; [reflexivity |].
    eexists. split; [apply cv_refl | right; apply whd_shape; constructor].
  - (* su_sig *)
    assert (HMuSApp = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [right; right; reflexivity |].
    eexists. split; [apply cv_refl | apply whd_shape; constructor].
Qed.

(* ------------------------------------------------------------------ *)
(*  Canonical forms                                                    *)
(* ------------------------------------------------------------------ *)

(* fix the target class from a literal-headed leaf type *)
Ltac cls C hh Hcc Hww :=
  let E := fresh "Eclass" in
  assert (E : C = hh) by
    (eapply conv_whd; [exact Hcc | apply whd_shape; constructor | exact Hww]);
  subst hh; cbn.

Lemma canon_syn : forall t A, synth [] t A -> value t ->
    forall U h, conv A U -> whd U h -> canon t h U.
Proof.
  intros t A Hsyn Hval U h Hc Hw.
  inversion Hsyn; subst; try (solve [inversion Hval]).
  - (* sy_sort *) cls HSort h Hc Hw. exact I.
  - (* sy_pi *) cls HSort h Hc Hw. exact I.
  - (* sy_sigma *) cls HSort h Hc Hw. exact I.
  - (* sy_app : a stuck mu application *)
    assert (h = HSort) as ->.
    { eapply muapp_sort; [apply check_of_synth; exact Hsyn | exact Hval
                         | exact Hc | exact Hw]. }
    exact I.
  - (* sy_unitT *) cls HSort h Hc Hw. exact I.
  - (* sy_unit *) cls HUnitT h Hc Hw. reflexivity.
  - (* sy_uid *) cls HSort h Hc Hw. exact I.
  - (* sy_enumu *) cls HSort h Hc Hw. exact I.
  - (* sy_tag *) cls HUId h Hc Hw. exact I.
  - (* sy_nile *) cls HEnumU h Hc Hw. left; reflexivity.
  - (* sy_conse *) cls HEnumU h Hc Hw. right; eexists; eexists; reflexivity.
  - (* sy_enumt *) cls HSort h Hc Hw. exact I.
  - (* sy_idesc *) cls HSort h Hc Hw. exact I.
  - (* sy_mui *) cls HPi h Hc Hw. right; left; eexists; reflexivity.
  - (* sy_mus *) cls HPi h Hc Hw. right; right; eexists; reflexivity.
  - (* sy_list *) cls HSort h Hc Hw. exact I.
  - (* sy_lnil *) cls HList h Hc Hw. exact I.
  - (* sy_lcons *) cls HList h Hc Hw. exact I.
Qed.

Lemma canon_main : forall G t T, check G t T -> G = [] -> value t ->
    forall U h, conv T U -> whd U h -> canon t h U.
Proof.
  intros G t T Hck. induction Hck; intros HG Hval U h Hc Hw; subst.
  - (* ch_conv *)
    match goal with
    | Hs : synth [] ?t0 ?A0, Hcv : conv ?A0 ?B0 |- _ =>
        eapply canon_syn;
        [exact Hs | exact Hval
        | eapply cv_trans; [exact Hcv | exact Hc] | exact Hw]
    end.
  - (* ch_sub *)
    match goal with
    | Hs : synth [] ?t0 ?A0, Hsub : sub [] ?A0 ?B0 |- _ =>
        destruct (sub_transport [] A0 B0 Hsub U h Hc Hw) as
          [HcAU | [[Hh [U' [HcU' Hw']]] | [Heq [U' [HcU' Hw']]]]];
        [ eapply canon_syn; [exact Hs | exact Hval | exact HcAU | exact Hw]
        | destruct Hh as [-> | [-> | ->]];
          (assert (K : canon _ _ U') by
             (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
           exact K)
        | subst h; destruct Hw' as [Hw' | Hw'];
          [ assert (K : canon _ HMuIApp U') by
              (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
            exact K
          | assert (K : canon _ HMuSApp U') by
              (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
            exact (canon_mus_to_mui _ U' U K) ] ]
    end.
  - (* ch_expand *)
    match goal with
    | Hcv : conv ?A0 ?B0 |- _ =>
        apply IHHck;
        [reflexivity | exact Hval
        | eapply cv_trans; [eapply cv_sym; exact Hcv | exact Hc] | exact Hw]
    end.
  - (* ch_lam *) cls HPi h Hc Hw. left; eexists; reflexivity.
  - (* ch_pair *) cls HSigma h Hc Hw. eexists; eexists; reflexivity.
  - (* ch_app : a stuck μ application *)
    assert (h = HSort) as ->.
    { eapply muapp_sort;
        [eapply ch_app; eassumption | exact Hval | exact Hc | exact Hw]. }
    exact I.
  - (* ch_fst *) inversion Hval.
  - (* ch_snd *) inversion Hval.
  - (* ch_ezero *) cls HEnumT h Hc Hw.
    do 2 eexists. split; [exact Hc | left; reflexivity].
  - (* ch_esucc *) cls HEnumT h Hc Hw.
    do 2 eexists. split; [exact Hc |].
    right. eexists. split; [reflexivity |].
    match goal with Hn : check [] ?n0 (TEnumT ?E0) |- _ =>
      exists E0; exact Hn end.
  - (* ch_ivar *) cls HIDesc h Hc Hw. left; eexists; reflexivity.
  - (* ch_i1 *) cls HIDesc h Hc Hw. right; left; reflexivity.
  - (* ch_iprod *) cls HIDesc h Hc Hw.
    right; right; left; eexists; eexists; reflexivity.
  - (* ch_ipi *) cls HIDesc h Hc Hw.
    right; right; right; left; eexists; eexists; reflexivity.
  - (* ch_isig *) cls HIDesc h Hc Hw.
    right; right; right; right; left; eexists; eexists; reflexivity.
  - (* ch_ichoice *) cls HIDesc h Hc Hw.
    right; right; right; right; right; eexists; eexists; reflexivity.
  - (* ch_in_mui *) cls HMuIApp h Hc Hw. eexists; reflexivity.
  - (* ch_in_sig *) cls HMuSApp h Hc Hw.
    match goal with Hc0 : check [] ?c0 (Label ?E0) |- _ =>
      eexists; eexists; exists E0; split; [reflexivity | exact Hc0] end.
Qed.

(* ------------------------------------------------------------------ *)
(*  Typing inversion for eliminator shapes (empty context)             *)
(* ------------------------------------------------------------------ *)

Lemma inv_var : forall G t T, check G t T -> G = [] ->
    forall n, t = TVar n -> False.
Proof.
  intros G t T Hck. induction Hck; intros HG n0 Heq; subst; try discriminate.
  - match goal with Hs : synth [] (TVar _) _ |- _ =>
      inversion Hs; subst;
      match goal with Hne : nth_error [] ?m = Some _ |- _ =>
        destruct m; discriminate Hne end
    end.
  - match goal with Hs : synth [] (TVar _) _ |- _ =>
      inversion Hs; subst;
      match goal with Hne : nth_error [] ?m = Some _ |- _ =>
        destruct m; discriminate Hne end
    end.
  - exact (IHHck eq_refl n0 eq_refl).
Qed.

Ltac syn_app_emit :=
  match goal with Hs : synth [] (TApp _ _) _ |- _ =>
    inversion Hs; subst;
    match goal with
      Hsf : synth [] ?f0 ?C, Hev : eval ?C (TPi ?A1 ?B1) |- _ =>
        exists C; split;
        [apply check_of_synth; exact Hsf
        | exists (TPi A1 B1); split; [exact Hev | constructor]]
    end
  end.

Lemma inv_app : forall G t T, check G t T -> G = [] ->
    forall f a, t = TApp f a ->
    exists T', check [] f T' /\ whd T' HPi.
Proof.
  intros G t T Hck. induction Hck; intros HG f0 a0 Heq; subst; try discriminate.
  - syn_app_emit.
  - syn_app_emit.
  - exact (IHHck eq_refl f0 a0 eq_refl).
  - (* ch_app *)
    match goal with Heq2 : TApp _ _ = TApp _ _ |- _ =>
      inversion Heq2; subst end.
    match goal with Hf : check [] ?f1 (TPi ?A1 ?B1) |- _ =>
      exists (TPi A1 B1); split;
      [exact Hf | apply whd_shape; constructor]
    end.
Qed.

Ltac syn_proj_emit :=
  match goal with Hs : synth [] (_ _) _ |- _ =>
    inversion Hs; subst;
    match goal with
      Hsp : synth [] ?p0 ?C, Hev : eval ?C (TSigma ?A1 ?B1) |- _ =>
        exists C; split;
        [apply check_of_synth; exact Hsp
        | exists (TSigma A1 B1); split; [exact Hev | constructor]]
    end
  end.

Lemma inv_fst : forall G t T, check G t T -> G = [] ->
    forall p, t = TFst p ->
    exists T', check [] p T' /\ whd T' HSigma.
Proof.
  intros G t T Hck. induction Hck; intros HG p0 Heq; subst; try discriminate.
  - syn_proj_emit.
  - syn_proj_emit.
  - exact (IHHck eq_refl p0 eq_refl).
  - match goal with Heq2 : TFst _ = TFst _ |- _ => inversion Heq2; subst end.
    match goal with Hp : check [] ?p1 (TSigma ?A1 ?B1) |- _ =>
      exists (TSigma A1 B1); split;
      [exact Hp | apply whd_shape; constructor]
    end.
Qed.

Lemma inv_snd : forall G t T, check G t T -> G = [] ->
    forall p, t = TSnd p ->
    exists T', check [] p T' /\ whd T' HSigma.
Proof.
  intros G t T Hck. induction Hck; intros HG p0 Heq; subst; try discriminate.
  - syn_proj_emit.
  - syn_proj_emit.
  - exact (IHHck eq_refl p0 eq_refl).
  - match goal with Heq2 : TSnd _ = TSnd _ |- _ => inversion Heq2; subst end.
    match goal with Hp : check [] ?p1 (TSigma ?A1 ?B1) |- _ =>
      exists (TSigma A1 B1); split;
      [exact Hp | apply whd_shape; constructor]
    end.
Qed.

Ltac syn_prem_emit :=
  match goal with Hs : synth [] _ _ |- _ =>
    inversion Hs; subst; repeat split; try eassumption;
    try (eexists; eassumption)
  end.

Lemma inv_epi : forall G t T, check G t T -> G = [] ->
    forall E P, t = TEPi E P -> check [] E TEnumU.
Proof.
  intros G t T Hck. induction Hck; intros HG E0 P0 Heq; subst; try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 eq_refl).
Qed.

Lemma inv_switch : forall G t T, check G t T -> G = [] ->
    forall E P p e, t = TSwitch E P p e ->
    check [] E TEnumU /\ check [] p (TEPi E P) /\ check [] e (TEnumT E).
Proof.
  intros G t T Hck. induction Hck; intros HG E0 P0 p0 e0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 p0 e0 eq_refl).
Qed.

Lemma inv_interp : forall G t T, check G t T -> G = [] ->
    forall D X, t = TInterp D X -> exists IT, check [] D (TIDesc IT).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 Heq; subst; try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 eq_refl).
Qed.

Lemma inv_iall : forall G t T, check G t T -> G = [] ->
    forall D X xs P, t = TIAll D X xs P ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 xs0 P0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 xs0 P0 eq_refl).
Qed.

Lemma inv_hyps : forall G t T, check G t T -> G = [] ->
    forall D X P h xs, t = THyps D X P h xs ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 P0 h0 xs0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 P0 h0 xs0 eq_refl).
Qed.

Lemma inv_ind : forall G t T, check G t T -> G = [] ->
    forall R P stp i x, t = TInd R P stp i x ->
    check [] x (TApp (TMuI R) i).
Proof.
  intros G t T Hck. induction Hck; intros HG R0 P0 stp0 i0 x0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl R0 P0 stp0 i0 x0 eq_refl).
Qed.

Lemma inv_case : forall G t T, check G t T -> G = [] ->
    forall M Q bs, t = TCase M Q bs ->
    exists Sf i IT E Phi,
      check [] M (TApp (TMuS Sf) i) /\
      check [] IT (TSort 0) /\ check [] E TEnumU /\
      check [] Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) /\
      check [] i IT /\
      eval (labels (TApp Sf i)) Phi /\
      covers (map fst bs) Phi /\
      check_branches [] Sf i E Q bs.
Proof.
  intros G t T Hck. induction Hck; intros HG M0 Q0 bs0 Heq; subst;
    try discriminate.
  - match goal with Hs : synth [] (TCase _ _ _) _ |- _ =>
      inversion Hs; subst;
      do 5 eexists; repeat split; eassumption
    end.
  - match goal with Hs : synth [] (TCase _ _ _) _ |- _ =>
      inversion Hs; subst;
      do 5 eexists; repeat split; eassumption
    end.
  - exact (IHHck eq_refl M0 Q0 bs0 eq_refl).
Qed.

Lemma cb_labels : forall G Sf i E Q bs,
    check_branches G Sf i E Q bs ->
    Forall (fun cb => check G (fst cb) (TEnumT E)) bs.
Proof.
  intros G Sf i E Q bs Hcb. induction Hcb; constructor; cbn; auto.
Qed.

(* ------------------------------------------------------------------ *)
(*  Auxiliaries for the case redex                                     *)
(* ------------------------------------------------------------------ *)

(* evaluation cannot change a canonical scrutinee tag *)
Lemma eval_in_tag : forall n c xs V, enum_pos c n ->
    eval (TIn (TPair c xs)) V -> exists xs', V = TIn (TPair c xs').
Proof.
  intros n c xs V Hp Hev. remember (TIn (TPair c xs)) as t0 eqn:Ht.
  revert c xs Hp Ht.
  induction Hev as [t | t u v Hst Hev IH]; intros c xs Hp Ht; subst.
  - eexists; reflexivity.
  - inversion Hst; subst.
    match goal with Hpp : step (TPair _ _) _ |- _ =>
      inversion Hpp; subst end.
    + match goal with Hc : step c ?c' |- _ =>
        exfalso; exact (pos_step_normal c n Hp c' Hc) end.
    + eapply IH; [exact Hp | reflexivity].
Qed.

Lemma spine_mem_pre : forall L Phi a,
    eval L Phi -> spine_mem a Phi -> spine_mem a L.
Proof.
  intros L Phi a Hev Hm. inversion Hm; subst.
  - eapply sm_here; [eapply eval_trans; eassumption | assumption].
  - eapply sm_there; [eapply eval_trans; eassumption | assumption].
Qed.

Lemma covers_pre : forall L Phi Psi,
    eval L Phi -> covers Psi Phi -> covers Psi L.
Proof.
  intros L Phi Psi Hev Hc. inversion Hc; subst.
  - eapply cov_nil. eapply eval_trans; eassumption.
  - eapply cov_cons; [eapply eval_trans; eassumption | assumption | assumption].
Qed.

Lemma forall2_in_l :
  forall (A B : Type) (R : A -> B -> Prop) (l : list A) (ns : list B) x,
    Forall2 R l ns -> In x l -> exists y, In y ns /\ R x y.
Proof.
  intros A B R l ns x HF. induction HF; intros Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + exists y. split; [left; reflexivity | assumption].
    + destruct (IHHF Hin) as [y0 [Hy0 HR]].
      exists y0. split; [right; assumption | assumption].
Qed.

Lemma forall_ex_forall2 : forall (bs : list (term * term)),
    Forall (fun cb => exists m, enum_pos (fst cb) m) bs ->
    exists ns, Forall2 (fun cb m => enum_pos (fst cb) m) bs ns.
Proof.
  induction bs as [|cb bs IH]; intros HF.
  - exists []. constructor.
  - inversion HF as [|? ? Hhd Htl]; subst.
    destruct Hhd as [m Hm]. destruct (IH Htl) as [ns Hns].
    exists (m :: ns). constructor; assumption.
Qed.

(* either some clause label steps (in place), or all are canonical *)
Lemma labels_walk : forall bs : list (term * term),
    Forall (fun cb => (exists m, enum_pos (fst cb) m) \/
                      (exists c', step (fst cb) c')) bs ->
    (exists bs1 c b bs2 c', bs = bs1 ++ (c, b) :: bs2 /\ step c c') \/
    Forall (fun cb => exists m, enum_pos (fst cb) m) bs.
Proof.
  induction bs as [|[c b] bs IH]; intros HF.
  - right; constructor.
  - inversion HF as [|? ? Hhd Htl]; subst. cbn in Hhd.
    destruct Hhd as [Hp | [c' Hst]].
    + destruct (IH Htl) as [[bs1 [c0 [b0 [bs2 [c0' [Heq Hst0]]]]]] | Hall].
      * left. exists ((c, b) :: bs1), c0, b0, bs2, c0'.
        cbn. rewrite Heq. auto.
      * right. constructor; [exact Hp | exact Hall].
    + left. exists [], c, b, bs, c'. cbn. auto.
Qed.

(* the first clause whose label sits at position n, with the first-match
   prefix condition st_case requires *)
Lemma find_first : forall (l : list (term * term)) (ns : list nat) n,
    Forall2 (fun cb m => enum_pos (fst cb) m) l ns ->
    In n ns ->
    exists k c b,
      nth_error l k = Some (c, b) /\ enum_pos c n /\
      (forall j cj bj, j < k -> nth_error l j = Some (cj, bj) ->
          exists nj, enum_pos cj nj /\ nj <> n).
Proof.
  intros l ns n HF. revert n.
  induction HF as [|[c b] m l' ns' Hp HF IH]; intros n Hin.
  - destruct Hin.
  - cbn in Hp. destruct (Nat.eq_dec m n) as [-> | Hne].
    + exists 0, c, b. cbn. repeat split; auto.
      intros j cj bj Hlt _. lia.
    + destruct Hin as [-> | Hin]; [congruence |].
      destruct (IH n Hin) as [k [c0 [b0 [Hnth [Hp0 Hpre]]]]].
      exists (S k), c0, b0. cbn. repeat split; auto.
      intros j cj bj Hlt Hnthj. destruct j as [|j'].
      * cbn in Hnthj. inversion Hnthj; subst. exists m. split; auto.
      * cbn in Hnthj. eapply (Hpre j' cj bj); [lia | exact Hnthj].
Qed.

(* ------------------------------------------------------------------ *)
(*  Progress                                                           *)
(* ------------------------------------------------------------------ *)

Lemma progress_n : forall N,
    (forall t A, tsize t <= N -> check [] t A ->
       value t \/ exists t', step t t') /\
    (forall c T, tsize c <= N -> check [] c T -> whd T HEnumT ->
       (exists m, enum_pos c m) \/ exists c', step c c').
Proof.
  induction N as [|N IH].
  { split.
    - intros t A Hsz _. pose proof (tsize_pos t). lia.
    - intros c T Hsz _ _. pose proof (tsize_pos c). lia. }
  destruct IH as [IHmain IHpos].
  assert (Hmain : forall t A, tsize t <= S N -> check [] t A ->
                    value t \/ exists t', step t t').
  { intros t A Hsz Hck.
    destruct t as [ n | k | A0 B0 | b | f a | A0 B0 | a b | p | p
                  | | | | s | | | tg E | E | | n' | E P
                  | E P p e | IT | i | | A0 B0 | Sd T | Sd T | E T
                  | D X | R | Sf | x | R P stp i x | D X xs P
                  | D X P h0 xs | A0 | A0 | A0 a l | M Q bs ];
      try (solve [left; constructor]).
    - (* TVar *)
      exfalso. exact (inv_var [] (TVar n) A Hck eq_refl n eq_refl).
    - (* TApp *)
      destruct (inv_app [] (TApp f a) A Hck eq_refl f a eq_refl)
        as [T' [Hf HwPi]].
      assert (Hszf : tsize f <= N) by (cbn in Hsz; lia).
      destruct (IHmain f T' Hszf Hf) as [Hv | [f' Hstep]];
        [| right; eexists; apply st_app1; exact Hstep].
      pose proof (canon_main [] f T' Hf eq_refl Hv T' HPi (cv_refl T') HwPi)
        as K. cbn in K.
      destruct K as [[b0 ->] | [[R0 ->] | [Sf0 ->]]].
      + right. eexists. apply st_beta.
      + left. constructor.
      + left. constructor.
    - (* TFst *)
      destruct (inv_fst [] (TFst p) A Hck eq_refl p eq_refl)
        as [T' [Hp HwS]].
      assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
      destruct (IHmain p T' Hszp Hp) as [Hv | [p' Hstep]];
        [| right; eexists; apply st_fst1; exact Hstep].
      pose proof (canon_main [] p T' Hp eq_refl Hv T' HSigma (cv_refl T') HwS)
        as K. cbn in K.
      destruct K as [a0 [b0 ->]].
      right. eexists. apply st_fst.
    - (* TSnd *)
      destruct (inv_snd [] (TSnd p) A Hck eq_refl p eq_refl)
        as [T' [Hp HwS]].
      assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
      destruct (IHmain p T' Hszp Hp) as [Hv | [p' Hstep]];
        [| right; eexists; apply st_snd1; exact Hstep].
      pose proof (canon_main [] p T' Hp eq_refl Hv T' HSigma (cv_refl T') HwS)
        as K. cbn in K.
      destruct K as [a0 [b0 ->]].
      right. eexists. apply st_snd.
    - (* TEPi *)
      pose proof (inv_epi [] (TEPi E P) A Hck eq_refl E P eq_refl) as HEnum.
      assert (HszE : tsize E <= N) by (cbn in Hsz; lia).
      destruct (IHmain E TEnumU HszE HEnum) as [Hv | [E' Hstep]];
        [| right; eexists; apply st_epi1; exact Hstep].
      pose proof (canon_main [] E TEnumU HEnum eq_refl Hv TEnumU HEnumU
                    (cv_refl TEnumU) (whd_shape TEnumU HEnumU hs_enumu))
        as K. cbn in K.
      destruct K as [-> | [tg0 [E0 ->]]].
      + right. eexists. apply st_epi_nil.
      + right. eexists. apply st_epi_cons.
    - (* TSwitch *)
      destruct (inv_switch [] (TSwitch E P p e) A Hck eq_refl E P p e eq_refl)
        as (HEnum & Hp & He).
      assert (HszE : tsize E <= N) by (cbn in Hsz; lia).
      destruct (IHmain E TEnumU HszE HEnum) as [HvE | [E' Hstep]];
        [| right; eexists; apply st_switch1; exact Hstep].
      pose proof (canon_main [] E TEnumU HEnum eq_refl HvE TEnumU HEnumU
                    (cv_refl TEnumU) (whd_shape TEnumU HEnumU hs_enumu))
        as KE. cbn in KE.
      destruct KE as [-> | [tg0 [E0 ->]]].
      + (* nil enum: the scrutinee cannot be a value *)
        assert (Hsze : tsize e <= N) by (cbn in Hsz; lia).
        destruct (IHmain e (TEnumT TNilE) Hsze He) as [Hve | [e' Hstep]];
          [| right; eexists; apply st_switch4; exact Hstep].
        exfalso.
        pose proof (canon_main [] e (TEnumT TNilE) He eq_refl Hve
                      (TEnumT TNilE) HEnumT (cv_refl _)
                      (whd_shape _ _ (hs_enumt TNilE))) as Ke.
        cbn in Ke. destruct Ke as (tg1 & E1 & Hcvt & _).
        apply conv_enumt_inj in Hcvt.
        assert (Hd : HConsE = HNilE).
        { eapply conv_whd;
            [exact Hcvt | apply whd_shape; constructor
            | apply whd_shape; constructor]. }
        discriminate Hd.
      + (* cons enum *)
        assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
        assert (HwS : whd (TEPi (TConsE tg0 E0) P) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_epi_cons | apply ev_refl].
          - constructor. }
        destruct (IHmain p (TEPi (TConsE tg0 E0) P) Hszp Hp)
          as [Hvp | [p' Hstep]];
          [| right; eexists; apply st_switch3; exact Hstep].
        pose proof (canon_main [] p _ Hp eq_refl Hvp _ HSigma (cv_refl _) HwS)
          as Kp. cbn in Kp.
        destruct Kp as [p0 [ps ->]].
        assert (Hsze : tsize e <= N) by (cbn in Hsz; lia).
        destruct (IHmain e (TEnumT (TConsE tg0 E0)) Hsze He)
          as [Hve | [e' Hstep]];
          [| right; eexists; apply st_switch4; exact Hstep].
        pose proof (canon_main [] e _ He eq_refl Hve _ HEnumT (cv_refl _)
                      (whd_shape _ _ (hs_enumt (TConsE tg0 E0)))) as Ke.
        cbn in Ke. destruct Ke as (tg1 & E1 & _ & [-> | [n0 [-> _]]]).
        * right. eexists. apply st_switch_zero.
        * right. eexists. apply st_switch_succ.
    - (* TInterp *)
      destruct (inv_interp [] (TInterp D X) A Hck eq_refl D X eq_refl)
        as [IT0 HD].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_interp1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_interp_var.
      + subst D. right. eexists. apply st_interp_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        right. eexists. apply st_interp_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D.
        right. eexists. apply st_interp_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        right. eexists. apply st_interp_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        right. eexists. apply st_interp_choice.
    - (* TInd *)
      pose proof (inv_ind [] (TInd R P stp i x) A Hck eq_refl
                    R P stp i x eq_refl) as Hx.
      assert (Hszx : tsize x <= N) by (cbn in Hsz; lia).
      destruct (IHmain x _ Hszx Hx) as [Hvx | [x' Hstep]];
        [| right; eexists; apply st_ind5; exact Hstep].
      pose proof (canon_main [] x _ Hx eq_refl Hvx _ HMuIApp (cv_refl _)
                    (whd_shape _ _ (hs_muiapp R i))) as K. cbn in K.
      destruct K as [xs0 ->].
      right. eexists. apply st_ind.
    - (* TIAll *)
      destruct (inv_iall [] (TIAll D X xs P) A Hck eq_refl D X xs P eq_refl)
        as [[IT0 HD] Hxs].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_iall1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      assert (Hszxs : tsize xs <= N) by (cbn in Hsz; lia).
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_iall_var.
      + subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp TI1 X) HUnitT).
        { eexists. split.
          - eapply ev_step; [apply st_interp_one | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HUnitT (cv_refl _)
                      Hw1) as Kx. cbn in Kx. subst xs.
        right. eexists. apply st_iall_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TIProd A1 B1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_prod | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D. right. eexists. apply st_iall_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TISig S1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_sig | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TIChoice E1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_choice | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_choice.
    - (* THyps *)
      destruct (inv_hyps [] (THyps D X P h0 xs) A Hck eq_refl
                  D X P h0 xs eq_refl)
        as [[IT0 HD] Hxs].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_hyps1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      assert (Hszxs : tsize xs <= N) by (cbn in Hsz; lia).
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_hyps_var.
      + subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp TI1 X) HUnitT).
        { eexists. split.
          - eapply ev_step; [apply st_interp_one | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HUnitT (cv_refl _)
                      Hw1) as Kx. cbn in Kx. subst xs.
        right. eexists. apply st_hyps_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TIProd A1 B1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_prod | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D. right. eexists. apply st_hyps_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TISig S1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_sig | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TIChoice E1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_choice | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_choice.
    - (* TCase *)
      destruct (inv_case [] (TCase M Q bs) A Hck eq_refl M Q bs eq_refl)
        as (Sf & i & IT & E & Phi & HM & HIT & HE & HSf & Hi & Hlab & Hcov & Hcb).
      assert (HszM : tsize M <= N) by (cbn in Hsz; lia).
      destruct (IHmain M _ HszM HM) as [HvM | [M' HstM]];
        [| right; eexists; apply st_case1; exact HstM].
      pose proof (canon_main [] M _ HM eq_refl HvM _ HMuSApp (cv_refl _)
                    (whd_shape _ _ (hs_musapp Sf i))) as K.
      cbn in K. destruct K as (c & xs & E0 & -> & Hc0).
      assert (Hszc : tsize c <= N) by (cbn in Hsz; lia).
      destruct (IHpos c _ Hszc Hc0 (whd_shape _ _ (hs_enumt E0)))
        as [[n Hn] | [c' Hstc]];
        [| right; eexists; apply st_case1; apply st_in1; apply st_pair1;
           exact Hstc].
      pose proof (cb_labels [] Sf i E Q bs Hcb) as HFlab.
      assert (HFps : Forall (fun cb => (exists m, enum_pos (fst cb) m) \/
                                       (exists c'0, step (fst cb) c'0)) bs).
      { rewrite Forall_forall in HFlab. apply Forall_forall.
        intros [cj bj] Hin.
        assert (Hszj : tsize cj <= N).
        { pose proof (tsize_case_bs (TIn (TPair c xs)) Q bs cj bj Hin). lia. }
        specialize (HFlab _ Hin). cbn in HFlab.
        exact (IHpos cj _ Hszj HFlab (whd_shape _ _ (hs_enumt E))). }
      destruct (labels_walk bs HFps)
        as [[bs1 [c0 [b0 [bs2 [c0' [-> Hst0]]]]]] | Hall];
        [right; eexists; eapply st_case_lbl; exact Hst0 |].
      destruct (forall_ex_forall2 bs Hall) as [ns Hns].
      destruct (@canonical_forms_sig (TIn (TPair c xs)) Sf i IT E
                  HIT HE HSf Hi HM)
        as (c1 & xs1 & Phi1 & HevM & HevL & Hmem1 & _).
      destruct (eval_in_tag n c xs _ Hn HevM) as [xs' Heq1].
      inversion Heq1; subst.
      assert (HmemL : spine_mem c (labels (TApp Sf i))).
      { eapply spine_mem_pre; [exact HevL | exact Hmem1]. }
      assert (HcovL : covers (map fst bs) (labels (TApp Sf i))).
      { eapply covers_pre; [exact Hlab | exact Hcov]. }
      destruct (spine_covered _ _ _ HmemL HcovL) as [d [Hind Hcvd]].
      apply in_map_iff in Hind. destruct Hind as [[d0 bd] [Hfst Hinbs]].
      cbn in Hfst. subst d0.
      destruct (forall2_in_l _ _ _ _ _ _ Hns Hinbs) as [m [Hinm Hpm]].
      cbn in Hpm.
      assert (Hmn : n = m) by
        (eapply conv_pos; [exact Hcvd | exact Hn | exact Hpm]).
      subst m.
      destruct (find_first bs ns n Hns Hinm) as (k & ck & bk & Hnth & Hpk & Hpre).
      right. eexists.
      eapply st_case with (k := k) (n := n);
        [exact Hnth | exact Hpk | exact Hn | exact Hpre]. }
  split; [exact Hmain |].
  intros c T Hsz Hck HwT.
  destruct (Hmain c T Hsz Hck) as [Hv | Hs]; [| right; exact Hs].
  destruct HwT as [T' [HevT HshT]].
  pose proof (canon_main [] c T Hck eq_refl Hv T HEnumT (cv_refl T)
                (ex_intro _ T' (conj HevT HshT))) as K.
  cbn in K. destruct K as (tg1 & E1 & _ & [-> | [n' [-> [E2 Hn']]]]).
  - left. exists 0. constructor.
  - assert (Hszn : tsize n' <= N) by (cbn in Hsz; lia).
    destruct (IHpos n' _ Hszn Hn' (whd_shape _ _ (hs_enumt E2)))
      as [[m Hm] | [n'' Hstn]].
    + left. exists (S m). constructor. exact Hm.
    + right. eexists. apply st_esucc1. exact Hstn.
Qed.

Theorem progress_proved : forall t A,
    check [] t A -> value t \/ exists t', step t t'.
Proof.
  intros t A Hck.
  destruct (progress_n (tsize t)) as [Hmain _].
  exact (Hmain t A (le_n (tsize t)) Hck).
Qed.

Print Assumptions progress_proved.
