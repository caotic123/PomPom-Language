Require Import Progress.
Import TypeRules.

Lemma enum_pos_inv_luna : forall u m, enum_pos u m ->
    (u = TEZero /\ m = 0) \/
    (exists c0 m1, u = TESucc c0 /\ m = S m1 /\ enum_pos c0 m1).
Proof.
  intros u m H.
  inversion H; subst; [left; auto | right; eauto].
Qed.

(* pending: the requested statement is false for the raw [step] relation.
   [st_beta] can reduce a lambda application to [TEZero]. *)

Lemma not_step_enum_pos_stable_luna :
    ~ (forall t u, step t u -> forall m, enum_pos u m -> enum_pos t m).
Proof.
  intro H.
  specialize (H (TApp (TLam TEZero) TUnit) TEZero
    (st_beta TEZero TUnit) 0 pos_zero).
  inversion H.
Qed.
