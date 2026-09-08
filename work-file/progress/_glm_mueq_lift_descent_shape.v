(* GLM worker 1 — mueq lift-descent bundle, part 1: shape lemmas.            *)
(*                                                                           *)
(* Inversion of the image of [lift 1 k] at every term constructor: if        *)
(* [lift 1 k f] has constructor head C, then [f] has the same head C and     *)
(* every component of [lift 1 k f] is itself a lift image.  Note that NO     *)
(* lift injectivity is needed anywhere: the descent proof never recovers a   *)
(* term from an arbitrary [g], it only splits [lift 1 k f] by destructing    *)
(* [f] and reassembles the descent witness [g0] componentwise.               *)
(*                                                                           *)
(* Offsets: components in binder position (the B of TPi/TSigma, a TLam body, *)
(* TCase branch bodies) are lifted at [S k]; everything else at [k].         *)

Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* The branch-map used by lift on TCase, packaged so that it can be named.   *)
Definition lift_branches (k : nat) (bs : list (term * term)) : list (term * term) :=
  map (fun '(c, b) => (lift 1 k c, lift 1 (S k) b)) bs.

Lemma lift_case_branches_glm : forall k M Q bs,
    lift 1 k (TCase M Q bs) = TCase (lift 1 k M) (lift 1 k Q) (lift_branches k bs).
Proof. reflexivity. Qed.

(* Uniform small proof tactic: destruct f, reduce the lift, kill the TVar     *)
(* disjuncts (whose lifted shape is an if-then-else on the index test).      *)
Ltac glm_shape :=
  match goal with
  | H : lift 1 _ ?f = _ |- _ =>
      destruct f; cbn [lift] in H;
      repeat match goal with
             | H0 : context [Nat.ltb ?n ?k] |- _ => destruct (Nat.ltb n k)
             end;
      cbn [lift] in H; try discriminate
  end.

(* ---- nullary heads ------------------------------------------------------- *)

Lemma lift_shape_unitt_glm : forall k f, lift 1 k f = TUnitT -> f = TUnitT.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_unit_glm : forall k f, lift 1 k f = TUnit -> f = TUnit.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_uid_glm : forall k f, lift 1 k f = TUId -> f = TUId.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_enumu_glm : forall k f, lift 1 k f = TEnumU -> f = TEnumU.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_nile_glm : forall k f, lift 1 k f = TNilE -> f = TNilE.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_ezero_glm : forall k f, lift 1 k f = TEZero -> f = TEZero.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_i1_glm : forall k f, lift 1 k f = TI1 -> f = TI1.
Proof. intros k f H. glm_shape. reflexivity. Qed.

Lemma lift_shape_sort_glm : forall k f s,
    lift 1 k f = TSort s -> exists s', f = TSort s' /\ s = s'.
Proof.
  intros k f s H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_tag_glm : forall k f s,
    lift 1 k f = TTag s -> exists s', f = TTag s' /\ s = s'.
Proof.
  intros k f s H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

(* ---- variable ------------------------------------------------------------ *)

Lemma lift_shape_var_glm : forall k f n,
    lift 1 k f = TVar n -> exists m, f = TVar m.
Proof. intros k f n H. glm_shape. all: eexists; reflexivity. Qed.

(* ---- unary, component at k ----------------------------------------------- *)

Lemma lift_shape_fst_glm : forall k f p,
    lift 1 k f = TFst p -> exists p0, f = TFst p0 /\ p = lift 1 k p0.
Proof.
  intros k f p H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_snd_glm : forall k f p,
    lift 1 k f = TSnd p -> exists p0, f = TSnd p0 /\ p = lift 1 k p0.
Proof.
  intros k f p H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_enumt_glm : forall k f E,
    lift 1 k f = TEnumT E -> exists E0, f = TEnumT E0 /\ E = lift 1 k E0.
Proof.
  intros k f E H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_esucc_glm : forall k f n,
    lift 1 k f = TESucc n -> exists n0, f = TESucc n0 /\ n = lift 1 k n0.
Proof.
  intros k f n H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_idesc_glm : forall k f IT,
    lift 1 k f = TIDesc IT -> exists IT0, f = TIDesc IT0 /\ IT = lift 1 k IT0.
Proof.
  intros k f IT H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_ivar_glm : forall k f i,
    lift 1 k f = TIVar i -> exists i0, f = TIVar i0 /\ i = lift 1 k i0.
Proof.
  intros k f i H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_mui_glm : forall k f R,
    lift 1 k f = TMuI R -> exists R0, f = TMuI R0 /\ R = lift 1 k R0.
Proof.
  intros k f R H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_mus_glm : forall k f Sf,
    lift 1 k f = TMuS Sf -> exists Sf0, f = TMuS Sf0 /\ Sf = lift 1 k Sf0.
Proof.
  intros k f Sf H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_in_glm : forall k f x,
    lift 1 k f = TIn x -> exists x0, f = TIn x0 /\ x = lift 1 k x0.
Proof.
  intros k f x H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_list_glm : forall k f A,
    lift 1 k f = TList A -> exists A0, f = TList A0 /\ A = lift 1 k A0.
Proof.
  intros k f A H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

Lemma lift_shape_lnil_glm : forall k f A,
    lift 1 k f = TLNil A -> exists A0, f = TLNil A0 /\ A = lift 1 k A0.
Proof.
  intros k f A H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

(* ---- unary, component at S k (binder) ------------------------------------ *)

Lemma lift_shape_lam_glm : forall k f b,
    lift 1 k f = TLam b -> exists b0, f = TLam b0 /\ b = lift 1 (S k) b0.
Proof.
  intros k f b H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.

(* ---- binary, both at k ---------------------------------------------------- *)

Lemma lift_shape_app_glm : forall k f g a,
    lift 1 k f = TApp g a ->
    exists g0 a0, f = TApp g0 a0 /\ g = lift 1 k g0 /\ a = lift 1 k a0.
Proof.
  intros k f g a H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_pair_glm : forall k f a b,
    lift 1 k f = TPair a b ->
    exists a0 b0, f = TPair a0 b0 /\ a = lift 1 k a0 /\ b = lift 1 k b0.
Proof.
  intros k f a b H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_conse_glm : forall k f tg E,
    lift 1 k f = TConsE tg E ->
    exists tg0 E0, f = TConsE tg0 E0 /\ tg = lift 1 k tg0 /\ E = lift 1 k E0.
Proof.
  intros k f tg E H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_epi_glm : forall k f E P,
    lift 1 k f = TEPi E P ->
    exists E0 P0, f = TEPi E0 P0 /\ E = lift 1 k E0 /\ P = lift 1 k P0.
Proof.
  intros k f E P H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_iprod_glm : forall k f A B,
    lift 1 k f = TIProd A B ->
    exists A0 B0, f = TIProd A0 B0 /\ A = lift 1 k A0 /\ B = lift 1 k B0.
Proof.
  intros k f A B H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_ipi_glm : forall k f Sd T,
    lift 1 k f = TIPi Sd T ->
    exists Sd0 T0, f = TIPi Sd0 T0 /\ Sd = lift 1 k Sd0 /\ T = lift 1 k T0.
Proof.
  intros k f Sd T H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_isig_glm : forall k f Sd T,
    lift 1 k f = TISig Sd T ->
    exists Sd0 T0, f = TISig Sd0 T0 /\ Sd = lift 1 k Sd0 /\ T = lift 1 k T0.
Proof.
  intros k f Sd T H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_ichoice_glm : forall k f E T,
    lift 1 k f = TIChoice E T ->
    exists E0 T0, f = TIChoice E0 T0 /\ E = lift 1 k E0 /\ T = lift 1 k T0.
Proof.
  intros k f E T H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_interp_glm : forall k f D X,
    lift 1 k f = TInterp D X ->
    exists D0 X0, f = TInterp D0 X0 /\ D = lift 1 k D0 /\ X = lift 1 k X0.
Proof.
  intros k f D X H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

(* ---- binary, second at S k (binder) --------------------------------------- *)

Lemma lift_shape_pi_glm : forall k f A B,
    lift 1 k f = TPi A B ->
    exists A0 B0, f = TPi A0 B0 /\ A = lift 1 k A0 /\ B = lift 1 (S k) B0.
Proof.
  intros k f A B H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

Lemma lift_shape_sigma_glm : forall k f A B,
    lift 1 k f = TSigma A B ->
    exists A0 B0, f = TSigma A0 B0 /\ A = lift 1 k A0 /\ B = lift 1 (S k) B0.
Proof.
  intros k f A B H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.

(* ---- ternary, all at k ----------------------------------------------------- *)

Lemma lift_shape_lcons_glm : forall k f A a l,
    lift 1 k f = TLCons A a l ->
    exists A0 a0 l0,
      f = TLCons A0 a0 l0 /\ A = lift 1 k A0 /\ a = lift 1 k a0 /\ l = lift 1 k l0.
Proof.
  intros k f A a l H. glm_shape. eexists; eexists; eexists.
  repeat split; try reflexivity; congruence.
Qed.

(* ---- quaternary, all at k -------------------------------------------------- *)

Lemma lift_shape_switch_glm : forall k f E P p e,
    lift 1 k f = TSwitch E P p e ->
    exists E0 P0 p0 e0,
      f = TSwitch E0 P0 p0 e0 /\
      E = lift 1 k E0 /\ P = lift 1 k P0 /\ p = lift 1 k p0 /\ e = lift 1 k e0.
Proof.
  intros k f E P p e H. glm_shape. eexists; eexists; eexists; eexists.
  repeat split; try reflexivity; congruence.
Qed.

Lemma lift_shape_iall_glm : forall k f D X xs P,
    lift 1 k f = TIAll D X xs P ->
    exists D0 X0 xs0 P0,
      f = TIAll D0 X0 xs0 P0 /\
      D = lift 1 k D0 /\ X = lift 1 k X0 /\ xs = lift 1 k xs0 /\ P = lift 1 k P0.
Proof.
  intros k f D X xs P H. glm_shape. eexists; eexists; eexists; eexists.
  repeat split; try reflexivity; congruence.
Qed.

(* ---- quinary, all at k ------------------------------------------------------ *)

Lemma lift_shape_ind_glm : forall k f R P s i x,
    lift 1 k f = TInd R P s i x ->
    exists R0 P0 s0 i0 x0,
      f = TInd R0 P0 s0 i0 x0 /\
      R = lift 1 k R0 /\ P = lift 1 k P0 /\ s = lift 1 k s0 /\
      i = lift 1 k i0 /\ x = lift 1 k x0.
Proof.
  intros k f R P s i x H. glm_shape.
  eexists; eexists; eexists; eexists; eexists.
  repeat split; try reflexivity; congruence.
Qed.

Lemma lift_shape_hyps_glm : forall k f D X P h xs,
    lift 1 k f = THyps D X P h xs ->
    exists D0 X0 P0 h0 xs0,
      f = THyps D0 X0 P0 h0 xs0 /\
      D = lift 1 k D0 /\ X = lift 1 k X0 /\ P = lift 1 k P0 /\
      h = lift 1 k h0 /\ xs = lift 1 k xs0.
Proof.
  intros k f D X P h xs H. glm_shape.
  eexists; eexists; eexists; eexists; eexists.
  repeat split; try reflexivity; congruence.
Qed.

(* ---- TCase: scrutinee and motive at k, branch bodies at S k ----------------- *)

Lemma lift_shape_case_glm : forall k f M Q bs,
    lift 1 k f = TCase M Q bs ->
    exists M0 Q0 bs0,
      f = TCase M0 Q0 bs0 /\
      M = lift 1 k M0 /\ Q = lift 1 k Q0 /\ bs = lift_branches k bs0.
Proof.
  intros k f M Q bs H. glm_shape.
  eexists; eexists; eexists.
  unfold lift_branches.
  repeat split; try reflexivity; congruence.
Qed.
