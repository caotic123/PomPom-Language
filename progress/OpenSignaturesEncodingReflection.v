From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesEncodingReduction OpenSignaturesEncodingFreshness.
Require Import OpenSignaturesSubstitution.
Import ListNotations.

Theorem encode_reduction_inverse : forall a b, DC.reduction a b ->
  forall t env, a = encode env t ->
  exists u, reduction t u /\ encode env u = b.
Proof.
  intros a b H; induction H; intros original env Heq.
  { subst t. destruct (encode_root_inverse original env u H) as [v [Hv He]].
    exists v; split; [now apply red_root|assumption]. }
  { destruct (encode_eta_view original env f (eq_sym Heq)) as [x [body [-> [Hfresh Hbody]]]].
    exists body; split; [now apply red_eta|assumption]. }
  all: destruct original; cbn [encode] in Heq; try discriminate; inversion Heq; subst.
  all: match goal with
    | IH : forall original env, encode ?ctx ?tm = encode env original -> _ |- _ =>
      let u := fresh "u" in let Hr := fresh "Hr" in let He := fresh "He" in
      destruct (IH tm ctx eq_refl) as [u [Hr He]]
    end.
  all: eexists; split; [constructor; eassumption|cbn [encode]; now rewrite He].
Qed.

Lemma encode_reductions_inverse : forall a b,
  nameless.DBParallelBase.rtc DC.reduction a b -> forall t env, a = encode env t ->
  exists u, reduces t u /\ encode env u = b.
Proof.
  intros a b H; induction H; intros t env E.
  - exists t; split; [constructor|symmetry;assumption].
  - destruct (encode_reduction_inverse _ _ H t env E) as [t' [Ht' Et']].
    destruct (IHrtc t' env (eq_sym Et')) as [u [Hu Eu]].
    exists u; split; [econstructor; eassumption|assumption].
Qed.
