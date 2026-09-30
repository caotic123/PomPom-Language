(* GLM worker 1 — conv-subst layer 1: the substituent side.                  *)
(*                                                                           *)
(*   conv_subst_rigid_glm : conv u u' -> forall t k,                         *)
(*                             conv (subst u k t) (subst u' k t)             *)
(*                                                                           *)
(* This needs NO conv t t' — substituting two convertible terms into the     *)
(* SAME term t only needs an induction on t itself: every constructor is a   *)
(* conv congruence, and the only interesting leaf is TVar k, where both      *)
(* sides are lifts of the substituents, handled by the closed conv_lift_glm. *)
(* This halves the work of the full two-sided theorem: once conv t t'        *)
(* transports one substituent (the conv induction), the other side is        *)
(* swapped in by conv_subst_rigid_glm and cv_trans.                          *)
(*                                                                           *)
(* Induction is on tsize (tsize_strong_ind), because the TCase branch list   *)
(* carries terms no structural subterm covers; tsize_case_bs /               *)
(* tsize_case_bs_body bound them, exactly as in Progress.v's tsize_lift.     *)
(* The TCase branch lists differ pointwise (u vs u'), so the whole map is    *)
(* transported clause by clause with cv_case_br over a generalized prefix.   *)

Require Import TypeRules Progress.
Require Import _glm_conv_lift_bundle_main.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Pointwise-convertible substituted branch lists give conv TCase, by        *)
(* cv_case_br along the list (generalized over the prefix L).                *)
Lemma conv_case_branch_map_prefix_glm :
  forall (bs : list (term * term)) (M Q u u' : term) (k : nat),
    (forall c b, In (c, b) bs ->
        conv (subst u k c) (subst u' k c) /\
        conv (subst u (S k) b) (subst u' (S k) b)) ->
    forall L : list (term * term),
      conv (TCase M Q (L ++ map (fun '(c, b) => (subst u k c, subst u (S k) b)) bs))
           (TCase M Q (L ++ map (fun '(c, b) => (subst u' k c, subst u' (S k) b)) bs)).
Proof.
  induction bs as [| [c b] bs0 IH]; intros M Q u u' k H L.
  - (* nil *)
    rewrite !app_nil_r. apply cv_refl.
  - (* cons *)
    cbn [map].
    eapply cv_trans.
    + apply (@cv_case_br M Q L (subst u k c) (subst u' k c)
              (subst u (S k) b) (subst u' (S k) b)
              (map (fun '(c0, b0) => (subst u k c0, subst u (S k) b0)) bs0)).
      * exact (proj1 (H c b (in_eq (c, b) bs0))).
      * exact (proj2 (H c b (in_eq (c, b) bs0))).
    + assert (H0 : forall c0 b0, In (c0, b0) bs0 ->
          conv (subst u k c0) (subst u' k c0) /\
          conv (subst u (S k) b0) (subst u' (S k) b0)).
      { intros c0 b0 HIn. apply (H c0 b0). constructor 2. exact HIn. }
      specialize (IH M Q u u' k H0 (L ++ (subst u' k c, subst u' (S k) b) :: nil)).
      rewrite <- !app_assoc in IH. cbn [app] in IH.
      exact IH.
Qed.

(* Every sibling of a subterm has size >= 1, so a child is strictly smaller. *)
(* glm_pos_all adds 1 <= tsize x for every term-typed variable x in context.  *)
(* (Rocq 9.1 Ltac1 has no bare '?x' hypothesis-name pattern, so we match on   *)
(*  hypotheses whose type is term — for a context variable x : term that      *)
(*  binds exactly x.)                                                         *)
Ltac glm_pos_all :=
  repeat
    match goal with
    | [ H : term |- _ ] =>
        lazymatch goal with
        | [ G : 1 <= tsize H |- _ ] => fail
        | _ => pose proof (tsize_pos H)
        end
    | _ => fail
    end.

Ltac glm_sz := cbn [tsize]; glm_pos_all; lia.

Theorem conv_subst_rigid_glm : forall u u' : term, conv u u' ->
    forall t k, conv (subst u k t) (subst u' k t).
Proof.
  intros u u' Hconv.
  apply (tsize_strong_ind
           (fun t => forall k, conv (subst u k t) (subst u' k t))).
  intros t IH kk. destruct t; cbn [subst].
  - (* TVar *)
    destruct (Nat.ltb n kk) eqn:Hlt.
    + apply cv_refl.
    + destruct (Nat.eqb n kk) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst n.
        exact (conv_lift_glm u u' Hconv kk 0).
      * apply cv_refl.
  - (* TSort *) apply cv_refl.
  - (* TPi *) apply cv_pi; apply IH; glm_sz.
  - (* TLam *) apply cv_lam. apply IH. glm_sz.
  - (* TApp *) apply cv_app; apply IH; glm_sz.
  - (* TSigma *) apply cv_sigma; apply IH; glm_sz.
  - (* TPair *) apply cv_pair; apply IH; glm_sz.
  - (* TFst *) apply cv_fst. apply IH. glm_sz.
  - (* TSnd *) apply cv_snd. apply IH. glm_sz.
  - (* TUnitT *) apply cv_refl.
  - (* TUnit *) apply cv_refl.
  - (* TUId *) apply cv_refl.
  - (* TTag *) apply cv_refl.
  - (* TEnumU *) apply cv_refl.
  - (* TNilE *) apply cv_refl.
  - (* TConsE *) apply cv_conse; apply IH; glm_sz.
  - (* TEnumT *) apply cv_enumt. apply IH. glm_sz.
  - (* TEZero *) apply cv_refl.
  - (* TESucc *) apply cv_esucc. apply IH. glm_sz.
  - (* TEPi *) apply cv_epi; apply IH; glm_sz.
  - (* TSwitch *) apply cv_switch; apply IH; glm_sz.
  - (* TIDesc *) apply cv_idesc. apply IH. glm_sz.
  - (* TIVar *) apply cv_ivar. apply IH. glm_sz.
  - (* TI1 *) apply cv_refl.
  - (* TIProd *) apply cv_iprod; apply IH; glm_sz.
  - (* TIPi *) apply cv_ipi; apply IH; glm_sz.
  - (* TISig *) apply cv_isig; apply IH; glm_sz.
  - (* TIChoice *) apply cv_ichoice; apply IH; glm_sz.
  - (* TInterp *) apply cv_interp; apply IH; glm_sz.
  - (* TMuI *) apply cv_mui. apply IH. glm_sz.
  - (* TMuS *) apply cv_mus. apply IH. glm_sz.
  - (* TIn *) apply cv_in. apply IH. glm_sz.
  - (* TInd *) apply cv_ind; apply IH; glm_sz.
  - (* TIAll *) apply cv_iall; apply IH; glm_sz.
  - (* THyps *) apply cv_hyps; apply IH; glm_sz.
  - (* TList *) apply cv_list. apply IH. glm_sz.
  - (* TLNil *) apply cv_lnil. apply IH. glm_sz.
  - (* TLCons *) apply cv_lcons; apply IH; glm_sz.
  - (* TCase *)
    assert (Hbr : forall c b, In (c, b) bs ->
        conv (subst u kk c) (subst u' kk c) /\
        conv (subst u (S kk) b) (subst u' (S kk) b)).
    { intros c b HIn. split.
      - apply IH. apply (tsize_case_bs t1 t2 bs c b HIn).
      - apply IH. apply (tsize_case_bs_body t1 t2 bs c b HIn). }
    eapply cv_trans.
    + apply (@cv_case (subst u kk t1) (subst u' kk t1)
                      (subst u kk t2) (subst u' kk t2)
                      (map (fun '(c, b) => (subst u kk c, subst u (S kk) b)) bs)).
      * apply IH. glm_sz.
      * apply IH. glm_sz.
    + assert (Hc := conv_case_branch_map_prefix_glm bs (subst u' kk t1)
                       (subst u' kk t2) u u' kk Hbr []).
      cbn [app] in Hc. exact Hc.
Qed.

Check conv_subst_rigid_glm :
  forall u u' : term, conv u u' -> forall t k, conv (subst u k t) (subst u' k t).
