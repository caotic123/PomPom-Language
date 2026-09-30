(* GLM worker 1 — mueq lift-descent bundle, part 2: the descent itself.      *)
(*                                                                           *)
(* Goal (root eta simulation needs):                                        *)
(*                                                                           *)
(*   mueq_lift1_descent_glm :                                                *)
(*     forall f g, mueq (lift 1 0 f) g ->                                    *)
(*       exists g0, g = lift 1 0 g0 /\ mueq f g0.                            *)
(*                                                                           *)
(* Strategy: mutual structural induction on the mueq/mubeq derivation.  Each *)
(* branch inverts the image of [lift 1 k] at the branch's head constructor   *)
(* (part 1 shape lemmas — no lift injectivity is needed anywhere: the        *)
(* descent never recovers a term from an arbitrary g, it only splits         *)
(* [lift 1 k f] by destructing f and reassembles the witness g0), applies    *)
(* the induction hypotheses to the component equations, and rebuilds.        *)
(*                                                                           *)
(* The exceptional me_muapp branch embeds an arbitrary conv; the exact       *)
(* closure there is isolated as the ONLY conversion-level premise:           *)
(*                                                                           *)
(*   conv_muapp_lift1_descent_glm.                                          *)
(*                                                                           *)
(* Minimal adjustment to the originally requested form: the premise is       *)
(* quantified over the lift offset k (the k = 0 instance is exactly the      *)
(* requested statement).  The structural induction runs under binders —      *)
(* branch bodies live at [lift 1 (S k)] — so me_muapp can be met at any      *)
(* offset; the premise must be available there too.                          *)
(*                                                                           *)
(* No Axiom / Conjecture / Admitted / Abort: the conversion descent remains  *)
(* a theorem binder (an ordinary hypothesis of the conditional theorems),    *)
(* never an axiom; every proved theorem below is closed under its binders.   *)

Require Import Progress.
Require Import _luna_mueq _luna_mueq_equiv.
Require Import _glm_mueq_lift_descent_shape.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. The isolated conversion-level premise (theorem binder, not an axiom)   *)
(* ========================================================================== *)

Definition conv_muapp_lift1_descent_glm : Prop :=
  forall k S i S' i',
    conv (lift 1 k (TApp (TMuS S) i)) (TApp (TMuS S') i') ->
    exists S0 i0,
      TApp (TMuS S') i' = lift 1 k (TApp (TMuS S0) i0) /\
      conv (TApp (TMuS S) i) (TApp (TMuS S0) i0).

(* The requested k = 0 instance, spelled out for reference. *)
Definition conv_muapp_lift0_descent_glm : Prop :=
  forall S i S' i',
    conv (lift 1 0 (TApp (TMuS S) i)) (TApp (TMuS S') i') ->
    exists S0 i0,
      TApp (TMuS S') i' = lift 1 0 (TApp (TMuS S0) i0) /\
      conv (TApp (TMuS S) i) (TApp (TMuS S0) i0).

Lemma conv_muapp_lift0_of_k_glm :
    conv_muapp_lift1_descent_glm -> conv_muapp_lift0_descent_glm.
Proof.
  intros HP S i S' i' H.
  apply (HP 0 S i S' i') in H. exact H.
Qed.

(* ========================================================================== *)
(*  2. The two target statements                                              *)
(* ========================================================================== *)

(* mueq descends out of [lift 1 k] on the left. *)
Definition mueq_lift_target_glm (k : nat) (f g : term) : Prop :=
  exists g0, g = lift 1 k g0 /\ mueq f g0.

(* mubeq descends out of the TCase branch map of [lift 1 k]. *)
Definition mubeq_lift_target_glm (k : nat) (bs bs' : list (term * term)) : Prop :=
  exists bs0, bs' = lift_branches k bs0 /\ mubeq bs bs0.

(* ========================================================================== *)
(*  3. Branch lemmas, one per mueq constructor                                *)
(* ========================================================================== *)

(* Each branch lemma receives, besides the constructor's mueq premises, the   *)
(* induction hypotheses available at that node:                               *)
(*   IH   : forall k f, lift 1 k f = <premise lhs> ->                         *)
(*            exists g0, <premise rhs> = lift 1 k g0 /\ mueq f g0             *)
(* and delivers the target for the branch's own head.                         *)

(* ---- variables and sorts -------------------------------------------------- *)

Lemma branch_var_glm : forall n k f,
    lift 1 k f = TVar n ->
    exists g0, TVar n = lift 1 k g0 /\ mueq f g0.
Proof.
  intros n k f Hl.
  destruct (lift_shape_var_glm _ _ _ Hl) as [m Hf].
  subst f. exists (TVar m). split;
    [symmetry; exact Hl | apply me_var].
Qed.

Lemma branch_sort_glm : forall s k f,
    lift 1 k f = TSort s ->
    exists g0, TSort s = lift 1 k g0 /\ mueq f g0.
Proof.
  intros s k f Hl.
  destruct (lift_shape_sort_glm _ _ _ Hl) as [s' [Hf Hs]].
  subst f.
  exists (TSort s'). split.
  - cbn [lift]. rewrite <- Hs. reflexivity.
  - apply me_sort.
Qed.

(* ---- unary heads ----------------------------------------------------------- *)

Lemma branch_lam_glm : forall b b' k f,
    mueq b b' ->
    (forall k f, lift 1 k f = b ->
       exists g0, b' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TLam b ->
    exists g0, TLam b' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros b b' k f Hm IH Hl.
  destruct (lift_shape_lam_glm _ _ _ Hl) as [b0 [Hf eb]].
  destruct (IH (S k) b0 (eq_sym eb)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TLam g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_lam. exact Hm1.
Qed.

Lemma branch_fst_glm : forall p p' k f,
    mueq p p' ->
    (forall k f, lift 1 k f = p ->
       exists g0, p' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TFst p ->
    exists g0, TFst p' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros p p' k f Hm IH Hl.
  destruct (lift_shape_fst_glm _ _ _ Hl) as [p0 [Hf ep]].
  destruct (IH k p0 (eq_sym ep)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TFst g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_fst. exact Hm1.
Qed.

Lemma branch_snd_glm : forall p p' k f,
    mueq p p' ->
    (forall k f, lift 1 k f = p ->
       exists g0, p' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TSnd p ->
    exists g0, TSnd p' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros p p' k f Hm IH Hl.
  destruct (lift_shape_snd_glm _ _ _ Hl) as [p0 [Hf ep]].
  destruct (IH k p0 (eq_sym ep)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TSnd g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_snd. exact Hm1.
Qed.

Lemma branch_enumt_glm : forall E E' k f,
    mueq E E' ->
    (forall k f, lift 1 k f = E ->
       exists g0, E' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TEnumT E ->
    exists g0, TEnumT E' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros E E' k f Hm IH Hl.
  destruct (lift_shape_enumt_glm _ _ _ Hl) as [E0 [Hf eE]].
  destruct (IH k E0 (eq_sym eE)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TEnumT g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_enumt. exact Hm1.
Qed.

Lemma branch_esucc_glm : forall n n' k f,
    mueq n n' ->
    (forall k f, lift 1 k f = n ->
       exists g0, n' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TESucc n ->
    exists g0, TESucc n' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros n n' k f Hm IH Hl.
  destruct (lift_shape_esucc_glm _ _ _ Hl) as [n0 [Hf en]].
  destruct (IH k n0 (eq_sym en)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TESucc g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_esucc. exact Hm1.
Qed.

Lemma branch_idesc_glm : forall IT IT' k f,
    mueq IT IT' ->
    (forall k f, lift 1 k f = IT ->
       exists g0, IT' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIDesc IT ->
    exists g0, TIDesc IT' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros IT IT' k f Hm IH Hl.
  destruct (lift_shape_idesc_glm _ _ _ Hl) as [IT0 [Hf eIT]].
  destruct (IH k IT0 (eq_sym eIT)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TIDesc g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_idesc. exact Hm1.
Qed.

Lemma branch_ivar_glm : forall i i' k f,
    mueq i i' ->
    (forall k f, lift 1 k f = i ->
       exists g0, i' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIVar i ->
    exists g0, TIVar i' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros i i' k f Hm IH Hl.
  destruct (lift_shape_ivar_glm _ _ _ Hl) as [i0 [Hf ei]].
  destruct (IH k i0 (eq_sym ei)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TIVar g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_ivar. exact Hm1.
Qed.

Lemma branch_mui_glm : forall R R' k f,
    mueq R R' ->
    (forall k f, lift 1 k f = R ->
       exists g0, R' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TMuI R ->
    exists g0, TMuI R' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros R R' k f Hm IH Hl.
  destruct (lift_shape_mui_glm _ _ _ Hl) as [R0 [Hf eR]].
  destruct (IH k R0 (eq_sym eR)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TMuI g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_mui. exact Hm1.
Qed.

Lemma branch_mus_glm : forall Sf Sf' k f,
    mueq Sf Sf' ->
    (forall k f, lift 1 k f = Sf ->
       exists g0, Sf' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TMuS Sf ->
    exists g0, TMuS Sf' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros Sf Sf' k f Hm IH Hl.
  destruct (lift_shape_mus_glm _ _ _ Hl) as [Sf0 [Hf eSf]].
  destruct (IH k Sf0 (eq_sym eSf)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TMuS g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_mus. exact Hm1.
Qed.

Lemma branch_in_glm : forall x x' k f,
    mueq x x' ->
    (forall k f, lift 1 k f = x ->
       exists g0, x' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIn x ->
    exists g0, TIn x' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros x x' k f Hm IH Hl.
  destruct (lift_shape_in_glm _ _ _ Hl) as [x0 [Hf ex]].
  destruct (IH k x0 (eq_sym ex)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TIn g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_in. exact Hm1.
Qed.

Lemma branch_list_glm : forall A A' k f,
    mueq A A' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TList A ->
    exists g0, TList A' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' k f Hm IH Hl.
  destruct (lift_shape_list_glm _ _ _ Hl) as [A0 [Hf eA]].
  destruct (IH k A0 (eq_sym eA)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TList g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_list. exact Hm1.
Qed.

Lemma branch_lnil_glm : forall A A' k f,
    mueq A A' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TLNil A ->
    exists g0, TLNil A' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' k f Hm IH Hl.
  destruct (lift_shape_lnil_glm _ _ _ Hl) as [A0 [Hf eA]].
  destruct (IH k A0 (eq_sym eA)) as [g1 [Hu1 Hm1]].
  subst f.
  exists (TLNil g1). split.
  - cbn [lift]. rewrite Hu1. reflexivity.
  - apply me_lnil. exact Hm1.
Qed.

(* ---- nullary heads ---------------------------------------------------------- *)

Lemma branch_unitt_glm : forall k f,
    lift 1 k f = TUnitT ->
    exists g0, TUnitT = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_unitt_glm _ _ Hl) as Hf.
  subst f.
  exists TUnitT. split; [reflexivity | apply me_unitt].
Qed.

Lemma branch_unit_glm : forall k f,
    lift 1 k f = TUnit ->
    exists g0, TUnit = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_unit_glm _ _ Hl) as Hf.
  subst f.
  exists TUnit. split; [reflexivity | apply me_unit].
Qed.

Lemma branch_uid_glm : forall k f,
    lift 1 k f = TUId ->
    exists g0, TUId = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_uid_glm _ _ Hl) as Hf.
  subst f.
  exists TUId. split; [reflexivity | apply me_uid].
Qed.

Lemma branch_tag_glm : forall s k f,
    lift 1 k f = TTag s ->
    exists g0, TTag s = lift 1 k g0 /\ mueq f g0.
Proof.
  intros s k f Hl.
  destruct (lift_shape_tag_glm _ _ _ Hl) as [s' [Hf Hs]].
  subst f.
  exists (TTag s'). split.
  - cbn [lift]. rewrite <- Hs. reflexivity.
  - apply me_tag.
Qed.

Lemma branch_enumu_glm : forall k f,
    lift 1 k f = TEnumU ->
    exists g0, TEnumU = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_enumu_glm _ _ Hl) as Hf.
  subst f.
  exists TEnumU. split; [reflexivity | apply me_enumu].
Qed.

Lemma branch_nile_glm : forall k f,
    lift 1 k f = TNilE ->
    exists g0, TNilE = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_nile_glm _ _ Hl) as Hf.
  subst f.
  exists TNilE. split; [reflexivity | apply me_nile].
Qed.

Lemma branch_ezero_glm : forall k f,
    lift 1 k f = TEZero ->
    exists g0, TEZero = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_ezero_glm _ _ Hl) as Hf.
  subst f.
  exists TEZero. split; [reflexivity | apply me_ezero].
Qed.

Lemma branch_i1_glm : forall k f,
    lift 1 k f = TI1 ->
    exists g0, TI1 = lift 1 k g0 /\ mueq f g0.
Proof.
  intros k f Hl.
  pose proof (lift_shape_i1_glm _ _ Hl) as Hf.
  subst f.
  exists TI1. split; [reflexivity | apply me_i1].
Qed.

(* ---- binary heads, both components at k -------------------------------------- *)

Lemma branch_app_glm : forall g g' a a' k f,
    mueq g g' -> mueq a a' ->
    (forall k f, lift 1 k f = g ->
       exists g0, g' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = a ->
       exists g0, a' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TApp g a ->
    exists g0, TApp g' a' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros g g' a a' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_app_glm _ _ _ _ Hl) as [g0 [a0 [Hf [eg ea]]]].
  destruct (IH1 k g0 (eq_sym eg)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k a0 (eq_sym ea)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TApp h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_app; assumption.
Qed.

Lemma branch_pair_glm : forall a a' b b' k f,
    mueq a a' -> mueq b b' ->
    (forall k f, lift 1 k f = a ->
       exists g0, a' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = b ->
       exists g0, b' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TPair a b ->
    exists g0, TPair a' b' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros a a' b b' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_pair_glm _ _ _ _ Hl) as [a0 [b0 [Hf [ea eb]]]].
  destruct (IH1 k a0 (eq_sym ea)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k b0 (eq_sym eb)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TPair h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_pair; assumption.
Qed.

Lemma branch_conse_glm : forall tg tg' E E' k f,
    mueq tg tg' -> mueq E E' ->
    (forall k f, lift 1 k f = tg ->
       exists g0, tg' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = E ->
       exists g0, E' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TConsE tg E ->
    exists g0, TConsE tg' E' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros tg tg' E E' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_conse_glm _ _ _ _ Hl) as [tg0 [E0 [Hf [etg eE]]]].
  destruct (IH1 k tg0 (eq_sym etg)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k E0 (eq_sym eE)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TConsE h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_conse; assumption.
Qed.

Lemma branch_epi_glm : forall E E' P P' k f,
    mueq E E' -> mueq P P' ->
    (forall k f, lift 1 k f = E ->
       exists g0, E' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = P ->
       exists g0, P' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TEPi E P ->
    exists g0, TEPi E' P' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros E E' P P' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_epi_glm _ _ _ _ Hl) as [E0 [P0 [Hf [eE eP]]]].
  destruct (IH1 k E0 (eq_sym eE)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k P0 (eq_sym eP)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TEPi h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_epi; assumption.
Qed.

Lemma branch_iprod_glm : forall A A' B B' k f,
    mueq A A' -> mueq B B' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = B ->
       exists g0, B' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIProd A B ->
    exists g0, TIProd A' B' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' B B' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_iprod_glm _ _ _ _ Hl) as [A0 [B0 [Hf [eA eB]]]].
  destruct (IH1 k A0 (eq_sym eA)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k B0 (eq_sym eB)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TIProd h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_iprod; assumption.
Qed.

Lemma branch_ipi_glm : forall Sd Sd' T T' k f,
    mueq Sd Sd' -> mueq T T' ->
    (forall k f, lift 1 k f = Sd ->
       exists g0, Sd' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = T ->
       exists g0, T' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIPi Sd T ->
    exists g0, TIPi Sd' T' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros Sd Sd' T T' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_ipi_glm _ _ _ _ Hl) as [Sd0 [T0 [Hf [eSd eT]]]].
  destruct (IH1 k Sd0 (eq_sym eSd)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k T0 (eq_sym eT)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TIPi h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_ipi; assumption.
Qed.

Lemma branch_isig_glm : forall Sd Sd' T T' k f,
    mueq Sd Sd' -> mueq T T' ->
    (forall k f, lift 1 k f = Sd ->
       exists g0, Sd' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = T ->
       exists g0, T' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TISig Sd T ->
    exists g0, TISig Sd' T' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros Sd Sd' T T' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_isig_glm _ _ _ _ Hl) as [Sd0 [T0 [Hf [eSd eT]]]].
  destruct (IH1 k Sd0 (eq_sym eSd)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k T0 (eq_sym eT)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TISig h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_isig; assumption.
Qed.

Lemma branch_ichoice_glm : forall E E' T T' k f,
    mueq E E' -> mueq T T' ->
    (forall k f, lift 1 k f = E ->
       exists g0, E' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = T ->
       exists g0, T' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIChoice E T ->
    exists g0, TIChoice E' T' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros E E' T T' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_ichoice_glm _ _ _ _ Hl) as [E0 [T0 [Hf [eE eT]]]].
  destruct (IH1 k E0 (eq_sym eE)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k T0 (eq_sym eT)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TIChoice h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_ichoice; assumption.
Qed.

Lemma branch_interp_glm : forall D D' X X' k f,
    mueq D D' -> mueq X X' ->
    (forall k f, lift 1 k f = D ->
       exists g0, D' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = X ->
       exists g0, X' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TInterp D X ->
    exists g0, TInterp D' X' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros D D' X X' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_interp_glm _ _ _ _ Hl) as [D0 [X0 [Hf [eD eX]]]].
  destruct (IH1 k D0 (eq_sym eD)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k X0 (eq_sym eX)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TInterp h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_interp; assumption.
Qed.

(* ---- binary heads, second component at S k ------------------------------------ *)

Lemma branch_pi_glm : forall A A' B B' k f,
    mueq A A' -> mueq B B' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = B ->
       exists g0, B' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TPi A B ->
    exists g0, TPi A' B' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' B B' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_pi_glm _ _ _ _ Hl) as [A0 [B0 [Hf [eA eB]]]].
  destruct (IH1 k A0 (eq_sym eA)) as [h1 [Hu1 Hm1]].
  destruct (IH2 (S k) B0 (eq_sym eB)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TPi h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_pi; assumption.
Qed.

Lemma branch_sigma_glm : forall A A' B B' k f,
    mueq A A' -> mueq B B' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = B ->
       exists g0, B' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TSigma A B ->
    exists g0, TSigma A' B' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' B B' k f p1 p2 IH1 IH2 Hl.
  destruct (lift_shape_sigma_glm _ _ _ _ Hl) as [A0 [B0 [Hf [eA eB]]]].
  destruct (IH1 k A0 (eq_sym eA)) as [h1 [Hu1 Hm1]].
  destruct (IH2 (S k) B0 (eq_sym eB)) as [h2 [Hu2 Hm2]].
  subst f.
  exists (TSigma h1 h2). split.
  - cbn [lift]. rewrite Hu1, Hu2. reflexivity.
  - apply me_sigma; assumption.
Qed.

(* ---- ternary heads ------------------------------------------------------------ *)

Lemma branch_lcons_glm : forall A A' a a' l l' k f,
    mueq A A' -> mueq a a' -> mueq l l' ->
    (forall k f, lift 1 k f = A ->
       exists g0, A' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = a ->
       exists g0, a' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = l ->
       exists g0, l' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TLCons A a l ->
    exists g0, TLCons A' a' l' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros A A' a a' l l' k f p1 p2 p3 IH1 IH2 IH3 Hl.
  destruct (lift_shape_lcons_glm _ _ _ _ _ Hl) as [A0 [a0 [l0 [Hf [eA [ea el]]]]]].
  destruct (IH1 k A0 (eq_sym eA)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k a0 (eq_sym ea)) as [h2 [Hu2 Hm2]].
  destruct (IH3 k l0 (eq_sym el)) as [h3 [Hu3 Hm3]].
  subst f.
  exists (TLCons h1 h2 h3). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hu3. reflexivity.
  - apply me_lcons; assumption.
Qed.

(* ---- quaternary heads ----------------------------------------------------------- *)

Lemma branch_switch_glm : forall E E' P P' p p' e e' k f,
    mueq E E' -> mueq P P' -> mueq p p' -> mueq e e' ->
    (forall k f, lift 1 k f = E ->
       exists g0, E' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = P ->
       exists g0, P' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = p ->
       exists g0, p' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = e ->
       exists g0, e' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TSwitch E P p e ->
    exists g0, TSwitch E' P' p' e' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros E E' P P' p p' e e' k f p1 p2 p3 p4 IH1 IH2 IH3 IH4 Hl.
  destruct (lift_shape_switch_glm _ _ _ _ _ _ Hl) as
    [E0 [P0 [p0 [e0 [Hf [eE [eP [ep ee]]]]]]]].
  destruct (IH1 k E0 (eq_sym eE)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k P0 (eq_sym eP)) as [h2 [Hu2 Hm2]].
  destruct (IH3 k p0 (eq_sym ep)) as [h3 [Hu3 Hm3]].
  destruct (IH4 k e0 (eq_sym ee)) as [h4 [Hu4 Hm4]].
  subst f.
  exists (TSwitch h1 h2 h3 h4). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hu3, Hu4. reflexivity.
  - apply me_switch; assumption.
Qed.

Lemma branch_iall_glm : forall D D' X X' xs xs' P P' k f,
    mueq D D' -> mueq X X' -> mueq xs xs' -> mueq P P' ->
    (forall k f, lift 1 k f = D ->
       exists g0, D' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = X ->
       exists g0, X' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = xs ->
       exists g0, xs' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = P ->
       exists g0, P' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TIAll D X xs P ->
    exists g0, TIAll D' X' xs' P' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros D D' X X' xs xs' P P' k f p1 p2 p3 p4 IH1 IH2 IH3 IH4 Hl.
  destruct (lift_shape_iall_glm _ _ _ _ _ _ Hl) as
    [D0 [X0 [xs0 [P0 [Hf [eD [eX [exs eP]]]]]]]].
  destruct (IH1 k D0 (eq_sym eD)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k X0 (eq_sym eX)) as [h2 [Hu2 Hm2]].
  destruct (IH3 k xs0 (eq_sym exs)) as [h3 [Hu3 Hm3]].
  destruct (IH4 k P0 (eq_sym eP)) as [h4 [Hu4 Hm4]].
  subst f.
  exists (TIAll h1 h2 h3 h4). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hu3, Hu4. reflexivity.
  - apply me_iall; assumption.
Qed.

(* ---- quinary heads ---------------------------------------------------------------- *)

Lemma branch_ind_glm : forall R R' P P' s s' i i' x x' k f,
    mueq R R' -> mueq P P' -> mueq s s' -> mueq i i' -> mueq x x' ->
    (forall k f, lift 1 k f = R ->
       exists g0, R' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = P ->
       exists g0, P' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = s ->
       exists g0, s' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = i ->
       exists g0, i' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = x ->
       exists g0, x' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = TInd R P s i x ->
    exists g0, TInd R' P' s' i' x' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros R R' P P' s s' i i' x x' k f p1 p2 p3 p4 p5
    IH1 IH2 IH3 IH4 IH5 Hl.
  destruct (lift_shape_ind_glm _ _ _ _ _ _ _ Hl) as
    [R0 [P0 [s0 [i0 [x0 [Hf [eR [eP [es [ei ex]]]]]]]]]].
  destruct (IH1 k R0 (eq_sym eR)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k P0 (eq_sym eP)) as [h2 [Hu2 Hm2]].
  destruct (IH3 k s0 (eq_sym es)) as [h3 [Hu3 Hm3]].
  destruct (IH4 k i0 (eq_sym ei)) as [h4 [Hu4 Hm4]].
  destruct (IH5 k x0 (eq_sym ex)) as [h5 [Hu5 Hm5]].
  subst f.
  exists (TInd h1 h2 h3 h4 h5). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hu3, Hu4, Hu5. reflexivity.
  - apply me_ind; assumption.
Qed.

Lemma branch_hyps_glm : forall D D' X X' P P' h h' xs xs' k f,
    mueq D D' -> mueq X X' -> mueq P P' -> mueq h h' -> mueq xs xs' ->
    (forall k f, lift 1 k f = D ->
       exists g0, D' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = X ->
       exists g0, X' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = P ->
       exists g0, P' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = h ->
       exists g0, h' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = xs ->
       exists g0, xs' = lift 1 k g0 /\ mueq f g0) ->
    lift 1 k f = THyps D X P h xs ->
    exists g0, THyps D' X' P' h' xs' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros D D' X X' P P' h h' xs xs' k f p1 p2 p3 p4 p5
    IH1 IH2 IH3 IH4 IH5 Hl.
  destruct (lift_shape_hyps_glm _ _ _ _ _ _ _ Hl) as
    [D0 [X0 [P0 [h0 [xs0 [Hf [eD [eX [eP [eh exs]]]]]]]]]].
  destruct (IH1 k D0 (eq_sym eD)) as [h1 [Hu1 Hm1]].
  destruct (IH2 k X0 (eq_sym eX)) as [h2 [Hu2 Hm2]].
  destruct (IH3 k P0 (eq_sym eP)) as [h3 [Hu3 Hm3]].
  destruct (IH4 k h0 (eq_sym eh)) as [h4 [Hu4 Hm4]].
  destruct (IH5 k xs0 (eq_sym exs)) as [h5 [Hu5 Hm5]].
  subst f.
  exists (THyps h1 h2 h3 h4 h5). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hu3, Hu4, Hu5. reflexivity.
  - apply me_hyps; assumption.
Qed.

(* ---- the exceptional me_muapp branch --------------------------------------------- *)

(* The only branch whose closure needs a conversion-level fact: the mueq    *)
(* rule carries an arbitrary conv premise, so descent through it needs the  *)
(* conv muS-app descent [conv_muapp_lift1_descent_glm].  The branch lemma   *)
(* takes that premise as an ordinary hypothesis (a binder, not an axiom).   *)
Lemma branch_muapp_glm : forall S1 S2 i1 i2 k f,
    conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
    conv_muapp_lift1_descent_glm ->
    lift 1 k f = TApp (TMuS S1) i1 ->
    exists g0, TApp (TMuS S2) i2 = lift 1 k g0 /\ mueq f g0.
Proof.
  intros S1 S2 i1 i2 k f Hc HP Hl.
  destruct (lift_shape_app_glm _ _ _ _ Hl) as [f1 [a1 [Hf [e1 e2]]]].
  destruct (lift_shape_mus_glm _ _ _ (eq_sym e1)) as [s0 [Hf1 eS]].
  assert (Hprem : conv (lift 1 k (TApp (TMuS s0) a1)) (TApp (TMuS S2) i2)).
  { cbn [lift]. rewrite <- eS, <- e2. exact Hc. }
  destruct (HP k s0 a1 S2 i2 Hprem) as [S0' [i0' [Heq Hconv]]].
  exists (TApp (TMuS S0') i0'). split.
  - exact Heq.
  - subst f1. subst f. apply me_muapp. exact Hconv.
Qed.

(* ---- TCase: the mubeq branch ------------------------------------------------ *)

Lemma branch_case_glm : forall M M' Q Q' bs bs' k f,
    mueq M M' -> mueq Q Q' -> mubeq bs bs' ->
    (forall k f, lift 1 k f = M ->
       exists g0, M' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = Q ->
       exists g0, Q' = lift 1 k g0 /\ mueq f g0) ->
    (forall k bs0, lift_branches k bs0 = bs ->
       exists bs0', bs' = lift_branches k bs0' /\ mubeq bs0 bs0') ->
    lift 1 k f = TCase M Q bs ->
    exists g0, TCase M' Q' bs' = lift 1 k g0 /\ mueq f g0.
Proof.
  intros M M' Q Q' bs bs' k f p1 p2 pub IH1 IH2 Ipub Hl.
  destruct (lift_shape_case_glm _ _ _ _ _ Hl) as
    [M0 [Q0 [bs0 [Hf [eM [eQ ebs]]]]]].
  destruct (IH1 k M0 (eq_sym eM)) as [h1 [Hu1 Hm1']].
  destruct (IH2 k Q0 (eq_sym eQ)) as [h2 [Hu2 Hm2']].
  destruct (Ipub k bs0 (eq_sym ebs)) as [bs0' [Hbs1 Hbs2]].
  subst f.
  exists (TCase h1 h2 bs0'). split.
  - cbn [lift]. rewrite Hu1, Hu2, Hbs1. reflexivity.
  - apply me_case; assumption.
Qed.

(* ---- mubeq branch lemmas ------------------------------------------------------ *)

Lemma mbranch_nil_glm : forall k bs0,
    lift_branches k bs0 = [] ->
    exists bs0', [] = lift_branches k bs0' /\ mubeq bs0 bs0'.
Proof.
  intros k bs0 H.
  destruct bs0 as [| [c0 b0] rst];
    try (exists []; split; [reflexivity | constructor]).
  cbn [lift_branches map] in H. discriminate.
Qed.

Lemma mbranch_cons_glm : forall c c' b b' bs bs' k bs0,
    mueq c c' -> mueq b b' -> mubeq bs bs' ->
    (forall k f, lift 1 k f = c ->
       exists g0, c' = lift 1 k g0 /\ mueq f g0) ->
    (forall k f, lift 1 k f = b ->
       exists g0, b' = lift 1 k g0 /\ mueq f g0) ->
    (forall k bs0, lift_branches k bs0 = bs ->
       exists bs0', bs' = lift_branches k bs0' /\ mubeq bs0 bs0') ->
    lift_branches k bs0 = (c, b) :: bs ->
    exists bs0', (c', b') :: bs' = lift_branches k bs0' /\ mubeq bs0 bs0'.
Proof.
  intros c c' b b' bs bs' k bs0 Hm1 Hm2 Hmub IH1 IH2 IHt H.
  destruct bs0 as [| [c0 b0] rest].
  - cbn [lift_branches map] in H. discriminate.
  - cbn [lift_branches map] in H.
    injection H as ec eb et.
    destruct (IH1 k c0 ec) as [h1 [Hu1 Hm1']].
    destruct (IH2 (S k) b0 eb) as [h2 [Hu2 Hm2']].
    destruct (IHt k rest et) as [rest' [Ht1 Ht2]].
    exists ((h1, h2) :: rest'). split.
    + cbn [lift_branches map]. rewrite Hu1, Hu2, Ht1. reflexivity.
    + apply mbe_cons; assumption.
Qed.

(* ========================================================================== *)
(*  4. The mutual descent theorem (combined scheme induction)                 *)
(* ========================================================================== *)

Theorem mueq_mubeq_lift_descent_glm :
  conv_muapp_lift1_descent_glm ->
  (forall t u, mueq t u ->
     forall k f, lift 1 k f = t ->
     exists g0, u = lift 1 k g0 /\ mueq f g0) /\
  (forall bs bs', mubeq bs bs' ->
     forall k bs0, lift_branches k bs0 = bs ->
     exists bs0', bs' = lift_branches k bs0' /\ mubeq bs0 bs0').
Proof.
  intros HP.
  apply (mueq_mubeq_ind
    (fun t u _ => forall k f, lift 1 k f = t ->
        exists g0, u = lift 1 k g0 /\ mueq f g0)
    (fun bs bs' _ => forall k bs0, lift_branches k bs0 = bs ->
        exists bs0', bs' = lift_branches k bs0' /\ mubeq bs0 bs0')).
  - intros n. exact (fun k f Hl => branch_var_glm n k f Hl).
  - intros k0. exact (fun k f Hl => branch_sort_glm k0 k f Hl).
  - intros A A' B B' m p1 m0 p2.
    exact (fun k f Hl => branch_pi_glm A A' B B' k f m m0 p1 p2 Hl).
  - intros b b' m p1. exact (fun k f Hl => branch_lam_glm b b' k f m p1 Hl).
  - intros g g' a a' m p1 m0 p2.
    exact (fun k f Hl => branch_app_glm g g' a a' k f m m0 p1 p2 Hl).
  - intros S1 S2 i1 i2 c.
    exact (fun k f Hl => branch_muapp_glm S1 S2 i1 i2 k f c HP Hl).
  - intros A A' B B' m p1 m0 p2.
    exact (fun k f Hl => branch_sigma_glm A A' B B' k f m m0 p1 p2 Hl).
  - intros a a' b b' m p1 m0 p2.
    exact (fun k f Hl => branch_pair_glm a a' b b' k f m m0 p1 p2 Hl).
  - intros p p' m p1. exact (fun k f Hl => branch_fst_glm p p' k f m p1 Hl).
  - intros p p' m p1. exact (fun k f Hl => branch_snd_glm p p' k f m p1 Hl).
  - exact branch_unitt_glm.
  - exact branch_unit_glm.
  - exact branch_uid_glm.
  - intros s0. exact (fun k f Hl => branch_tag_glm s0 k f Hl).
  - exact branch_enumu_glm.
  - exact branch_nile_glm.
  - intros tg tg' E0 E0' m p1 m0 p2.
    exact (fun k f Hl => branch_conse_glm tg tg' E0 E0' k f m m0 p1 p2 Hl).
  - intros E E' m p1. exact (fun k f Hl => branch_enumt_glm E E' k f m p1 Hl).
  - exact branch_ezero_glm.
  - intros n n' m p1. exact (fun k f Hl => branch_esucc_glm n n' k f m p1 Hl).
  - intros E E' P1 P' m p1 m0 p2.
    exact (fun k f Hl => branch_epi_glm E E' P1 P' k f m m0 p1 p2 Hl).
  - intros E E' P1 P' p p' e e' m p1 m0 p2 m1 p3 m2 p4.
    exact (fun k f Hl =>
      branch_switch_glm E E' P1 P' p p' e e' k f m m0 m1 m2 p1 p2 p3 p4 Hl).
  - intros I I' m p1. exact (fun k f Hl => branch_idesc_glm I I' k f m p1 Hl).
  - intros i i' m p1. exact (fun k f Hl => branch_ivar_glm i i' k f m p1 Hl).
  - exact branch_i1_glm.
  - intros A A' B B' m p1 m0 p2.
    exact (fun k f Hl => branch_iprod_glm A A' B B' k f m m0 p1 p2 Hl).
  - intros Sd Sd' T T' m p1 m0 p2.
    exact (fun k f Hl => branch_ipi_glm Sd Sd' T T' k f m m0 p1 p2 Hl).
  - intros Sd Sd' T T' m p1 m0 p2.
    exact (fun k f Hl => branch_isig_glm Sd Sd' T T' k f m m0 p1 p2 Hl).
  - intros E E' T T' m p1 m0 p2.
    exact (fun k f Hl => branch_ichoice_glm E E' T T' k f m m0 p1 p2 Hl).
  - intros D D' X X' m p1 m0 p2.
    exact (fun k f Hl => branch_interp_glm D D' X X' k f m m0 p1 p2 Hl).
  - intros R R' m p1. exact (fun k f Hl => branch_mui_glm R R' k f m p1 Hl).
  - intros Sf Sf' m p1.
    exact (fun k f Hl => branch_mus_glm Sf Sf' k f m p1 Hl).
  - intros x x' m p1. exact (fun k f Hl => branch_in_glm x x' k f m p1 Hl).
  - intros R R' P1 P' s s' i i' x x' m p1 m0 p2 m1 p3 m2 p4 m3 p5.
    exact (fun k f Hl =>
      branch_ind_glm R R' P1 P' s s' i i' x x' k f
        m m0 m1 m2 m3 p1 p2 p3 p4 p5 Hl).
  - intros D D' X X' xs xs' P1 P' m p1 m0 p2 m1 p3 m2 p4.
    exact (fun k f Hl =>
      branch_iall_glm D D' X X' xs xs' P1 P' k f m m0 m1 m2 p1 p2 p3 p4 Hl).
  - intros D D' X X' P1 P' h h' xs xs' m p1 m0 p2 m1 p3 m2 p4 m3 p5.
    exact (fun k f Hl =>
      branch_hyps_glm D D' X X' P1 P' h h' xs xs' k f
        m m0 m1 m2 m3 p1 p2 p3 p4 p5 Hl).
  - intros A A' m p1. exact (fun k f Hl => branch_list_glm A A' k f m p1 Hl).
  - intros A A' m p1. exact (fun k f Hl => branch_lnil_glm A A' k f m p1 Hl).
  - intros A A' a a' l l' m p1 m0 p2 m1 p3.
    exact (fun k f Hl =>
      branch_lcons_glm A A' a a' l l' k f m m0 m1 p1 p2 p3 Hl).
  - intros M M' Q0 Q' bs bs' m pm m0 pq m1 pmub.
    exact (fun k f Hl =>
      branch_case_glm M M' Q0 Q' bs bs' k f m m0 m1 pm pq pmub Hl).
  - exact mbranch_nil_glm.
  - intros c c' b b' bs bs' m pc m0 pb m1 pt.
    exact (fun k bs0 H =>
      mbranch_cons_glm c c' b b' bs bs' k bs0 m m0 m1 pc pb pt H).
Qed.

(* ========================================================================== *)
(*  5. Consumer-facing theorems                                               *)
(* ========================================================================== *)

(* Full mueq lift descent at any offset, conditional on the isolated premise. *)
Theorem mueq_lift_descent_k_glm : conv_muapp_lift1_descent_glm ->
    forall k f g, mueq (lift 1 k f) g ->
      exists g0, g = lift 1 k g0 /\ mueq f g0.
Proof.
  intros HP k f g Hm.
  exact (proj1 (mueq_mubeq_lift_descent_glm HP) _ _ Hm k f eq_refl).
Qed.

(* The requested statement: mueq lift-1 descent at offset 0. *)
Theorem mueq_lift1_descent_glm : conv_muapp_lift1_descent_glm ->
    forall f g, mueq (lift 1 0 f) g ->
      exists g0, g = lift 1 0 g0 /\ mueq f g0.
Proof.
  exact (fun HP => mueq_lift_descent_k_glm HP 0).
Qed.

(* Full mubeq (TCase branch list) lift descent at any offset, conditional on  *)
(* the same isolated premise — this is what TCase needs in the root eta       *)
(* simulation.                                                                *)
Theorem mubeq_lift_descent_k_glm : conv_muapp_lift1_descent_glm ->
    forall k bs bs', mubeq (lift_branches k bs) bs' ->
      exists bs0, bs' = lift_branches k bs0 /\ mubeq bs bs0.
Proof.
  intros HP k bs bs' Hm.
  exact (proj2 (mueq_mubeq_lift_descent_glm HP) _ _ Hm k bs eq_refl).
Qed.

Theorem mubeq_lift1_descent_glm : conv_muapp_lift1_descent_glm ->
    forall bs bs', mubeq (lift_branches 0 bs) bs' ->
      exists bs0, bs' = lift_branches 0 bs0 /\ mubeq bs bs0.
Proof.
  exact (fun HP => mubeq_lift_descent_k_glm HP 0).
Qed.

(* Same statement with lift's raw branch map, for consumers working against   *)
(* the literal TCase clause of lift.                                          *)
Theorem mubeq_lift1_descent_map_glm : conv_muapp_lift1_descent_glm ->
    forall bs bs',
      mubeq (map (fun '(c, b) => (lift 1 0 c, lift 1 1 b)) bs) bs' ->
      exists bs0,
        bs' = map (fun '(c, b) => (lift 1 0 c, lift 1 1 b)) bs0 /\
        mubeq bs bs0.
Proof.
  exact mubeq_lift1_descent_glm.
Qed.

(* mubeq descent needs mueq descent only through the branch components;      *)
(* factored form for consumers that already hold mueq descent.               *)
Lemma mubeq_lift_descent_of_mueq_glm :
  (forall k f g, mueq (lift 1 k f) g ->
     exists g0, g = lift 1 k g0 /\ mueq f g0) ->
  forall k bs bs', mubeq (lift_branches k bs) bs' ->
    exists bs0, bs' = lift_branches k bs0 /\ mubeq bs bs0.
Proof.
  intros Hmued k bs.
  induction bs as [| [c b] rest IH]; intros bs' Hmub.
  - cbn [lift_branches map] in Hmub. inversion Hmub; subst.
    exists []. split; [reflexivity | constructor].
  - cbn [lift_branches map] in Hmub.
    inversion Hmub as [| c0 c0' b0 b0' rst rst' Hc Hb Ht ]; subst.
    destruct (Hmued k c c0' Hc) as [c0'' [Hc1 Hc2]].
    destruct (Hmued (S k) b b0' Hb) as [b0'' [Hb1 Hb2]].
    destruct (IH rst' Ht) as [rest0 [Ht1 Ht2]].
    exists ((c0'', b0'') :: rest0). split.
    + cbn [lift_branches map]. rewrite Hc1, Hb1, Ht1. reflexivity.
    + apply mbe_cons; assumption.
Qed.

(* Symmetric form: mueq against a lift on the RIGHT descends too. *)
Theorem mueq_lift1_descent_sym_glm : conv_muapp_lift1_descent_glm ->
    forall f g, mueq f (lift 1 0 g) ->
      exists f0, f = lift 1 0 f0 /\ mueq f0 g.
Proof.
  intros HP f g H.
  destruct (mueq_lift1_descent_glm HP g f (mueq_sym _ _ H)) as [f0 [Hf Hm]].
  exists f0. split; [exact Hf | apply mueq_sym; exact Hm].
Qed.

Theorem mueq_lift_descent_sym_k_glm : conv_muapp_lift1_descent_glm ->
    forall k f g, mueq f (lift 1 k g) ->
      exists f0, f = lift 1 k f0 /\ mueq f0 g.
Proof.
  intros HP k f g H.
  destruct (mueq_lift_descent_k_glm HP k g f (mueq_sym _ _ H)) as [f0 [Hf Hm]].
  exists f0. split; [exact Hf | apply mueq_sym; exact Hm].
Qed.

(* ========================================================================== *)
(*  6. Closedness                                                             *)
(* ========================================================================== *)

Print Assumptions mueq_mubeq_lift_descent_glm.
Print Assumptions mueq_lift_descent_k_glm.
Print Assumptions mueq_lift1_descent_glm.
Print Assumptions mueq_lift1_descent_sym_glm.
Print Assumptions mubeq_lift_descent_k_glm.
Print Assumptions mubeq_lift1_descent_glm.
Print Assumptions mubeq_lift1_descent_map_glm.
Print Assumptions mubeq_lift_descent_of_mueq_glm.
Print Assumptions conv_muapp_lift0_of_k_glm.
