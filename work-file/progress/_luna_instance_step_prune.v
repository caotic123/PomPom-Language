Require Import Progress _parent_instance_pruning.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma prune_branches_nth_fwd : forall bs bs' k c b,
  prune_branches bs bs' -> nth_error bs k = Some (c,b) ->
  exists c' b', nth_error bs' k = Some (c',b') /\
    prune_term c c' /\ prune_term b b'.
Proof.
  intros bs bs' k c b H. revert k c b. induction H; intros k x y Hn; destruct k; cbn in Hn.
  - discriminate.
  - discriminate.
  - inversion Hn; subst. eexists; eexists; repeat split; eauto.
  - destruct (IHprune_branches k x y Hn) as [x' [y' [Hxy [Hx Hy]]]].
    exists x',y'. repeat split; cbn; eauto.
Qed.

Lemma prune_branches_nth_bwd : forall bs bs' k c' b',
  prune_branches bs bs' -> nth_error bs' k = Some (c',b') ->
  exists c b, nth_error bs k = Some (c,b) /\
    prune_term c c' /\ prune_term b b'.
Proof.
  intros bs bs' k c' b' H. revert k c' b'. induction H; intros k x y Hn; destruct k; cbn in Hn.
  - discriminate.
  - discriminate.
  - inversion Hn; subst. eexists; eexists; repeat split; eauto.
  - destruct (IHprune_branches k x y Hn) as [x' [y' [Hxy [Hx Hy]]]].
    exists x',y'. repeat split; cbn; eauto.
Qed.

Lemma prune_branches_app_inv : forall pre suf out,
  prune_branches (pre ++ suf) out ->
  exists pre' suf', out = pre' ++ suf' /\
    prune_branches pre pre' /\ prune_branches suf suf'.
Proof.
  intros pre. induction pre as [|[c b] pre IH]; intros suf out H.
  - exists [], out. split; [reflexivity|]. split; [apply pb_nil|exact H].
  - cbn in H. inversion H as [|c0 c1 b0 b1 bs0 bs1 Hc Hb Htail]; subst.
    destruct (IH _ _ Htail) as [pre' [suf' [-> [Hp Hs]]]].
    exists ((c1,b1)::pre'), suf'. repeat split; eauto.
  all: constructor; eauto.
Qed.

Lemma prune_branches_app : forall pre pre' suf suf',
  prune_branches pre pre' -> prune_branches suf suf' ->
  prune_branches (pre ++ suf) (pre' ++ suf').
Proof.
  intros pre pre' suf suf' H. induction H; intros Hs; cbn; eauto using prune_branches.
Qed.

Lemma prune_enum_pos : forall c n d,
  enum_pos c n -> prune_term c d -> d = c.
Proof.
  intros c n d H. revert d. induction H as [|c n H IH]; intros d Hp.
  - inversion Hp; reflexivity.
  - inversion Hp; subst. f_equal.
    apply IH; assumption.
Qed.

Print Assumptions prune_branches_nth_fwd.
Print Assumptions prune_branches_nth_bwd.
Print Assumptions prune_branches_app_inv.
Print Assumptions prune_branches_app.
Print Assumptions prune_enum_pos.
