Require Import TypeRules Progress.

(* GLM worker 2: desc_against is stable under de Bruijn lifting, assuming    *)
(* eval is (the lifting-compatibility of the weak-head evaluation used by    *)
(* the desc_against constructors is NOT proved here — it is hypothesized).  *)

Definition eval_lift_compatible_glm : Prop :=
  forall (d k : nat) (t u : term),
    eval t u -> eval (lift d k t) (lift d k u).

Section DescAgainstLiftGlm.

Hypothesis eval_lift_compat : eval_lift_compatible_glm.

Lemma desc_against_lift_glm :
  forall D, desc_against D -> forall d k, desc_against (lift d k D).
Proof.
  intros D H.
  induction H as
    [ D0 E T Hnil Hecons
    | D0 A B HprodL HdescL IHprodL
    | D0 A B HprodR HdescR IHprodR
    | D0 E T tg E' Hch Hecons Hzero IHzero Hcons IHcons ]; intros d k.
  - (* ag_choice_nil *)
    apply (@ag_choice_nil (lift d k D0) (lift d k E) (lift d k T)).
    + exact (eval_lift_compat d k _ _ Hnil).
    + exact (eval_lift_compat d k _ _ Hecons).
  - (* ag_prod_left *)
    apply (@ag_prod_left (lift d k D0) (lift d k A) (lift d k B)).
    + exact (eval_lift_compat d k _ _ HprodL).
    + exact (IHprodL d k).
  - (* ag_prod_right *)
    apply (@ag_prod_right (lift d k D0) (lift d k A) (lift d k B)).
    + exact (eval_lift_compat d k _ _ HprodR).
    + exact (IHprodR d k).
  - (* ag_choice_cons *)
    apply (@ag_choice_cons (lift d k D0) (lift d k E) (lift d k T)
                           (lift d k tg) (lift d k E')).
    + exact (eval_lift_compat d k _ _ Hch).
    + exact (eval_lift_compat d k _ _ Hecons).
    + exact (IHzero d k).
    + rewrite <- (lift_lift_one_zero T d k). exact (IHcons d k).
Qed.

End DescAgainstLiftGlm.

Check desc_against_lift_glm :
  eval_lift_compatible_glm ->
  forall D, desc_against D -> forall d k, desc_against (lift d k D).
