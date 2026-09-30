(* A shared expansion argument for operators: normalize their arguments,
   then check every possible head contraction after argument reduction. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBFullNormalForms nameless.DBFullReducibility.
Import ListNotations Full.

Definition term_children t : list term :=
  match t with
  | TPi A B | TApp A B | TSigma A B | TPair A B | TConsE A B
  | TIProd A B | TIPi A B | TISig A B | TIChoice A B | TMuI A B => [A;B]
  | TLam b | TFst b | TSnd b | TEnumT b | TESucc b | TIDesc b | TIVar b | TIn b => [b]
  | TEPi _ E P => [E;P]
  | TSwitch _ E P p e => [E;P;p;e]
  | TInterp IT D X | TClose IT D X => [IT;D;X]
  | TInd IT D P s i x => [IT;D;P;s;i;x]
  | TIAll IT D X x P => [IT;D;X;x;P]
  | THyps IT D X P h x => [IT;D;X;P;h;x]
  | TCloseCase _ IT F G i Q b x => [IT;F;G;i;Q;b;x]
  | TCloseInd IT G P s F i x => [IT;G;P;s;F;i;x]
  | _ => []
  end.

Inductive list_reduction : list term -> list term -> Prop :=
| lr_head : forall t u xs, reduction t u -> list_reduction (t::xs) (u::xs)
| lr_tail : forall t xs ys, list_reduction xs ys -> list_reduction (t::xs) (t::ys).
Lemma list_reduction_cons_accessible : forall t, full_SN t -> forall xs,
  Acc (fun ys xs => list_reduction xs ys) xs ->
  Acc (fun ys xs => list_reduction xs ys) (t::xs).
Proof.
  intros t HT; induction HT as [t HT IHt]; intros xs HX.
  induction HX as [xs HX IHx]; constructor; intros ys HY; inversion HY; subst.
  - apply IHt; [eassumption|constructor; exact HX].
  - apply IHx; eassumption.
Qed.
Lemma list_reduction_accessible : forall xs, Forall full_SN xs ->
  Acc (fun ys xs => list_reduction xs ys) xs.
Proof.
  intros xs H; induction H.
  - constructor; intros ys HY; inversion HY.
  - now apply list_reduction_cons_accessible.
Qed.

Definition inner_reduction t u :=
  compatible (rtc reduction) t u /\ list_reduction (term_children t) (term_children u).
Inductive head_reduction : term -> term -> Prop :=
| hr_root : forall t u, root_step t = Some u -> head_reduction t u
| hr_eta : forall f, head_reduction (TLam (TApp (lift 1 0 f) (TVar 0))) f.

Lemma compatible_reductions_refl : forall t, compatible (rtc reduction) t t.
Proof. destruct t; constructor; apply rtc_refl. Qed.
Lemma compatible_reductions_trans : forall t u v,
  compatible (rtc reduction) t u -> compatible (rtc reduction) u v ->
  compatible (rtc reduction) t v.
Proof.
  intros t u v H; destruct H; intro H'; inversion H'; subst;
    constructor; eapply rtc_trans; eassumption.
Qed.
Lemma reduction_head_or_inner : forall t u, reduction t u ->
  head_reduction t u \/ inner_reduction t u.
Proof.
  intros t u H; destruct H; try solve [left; constructor; assumption || reflexivity].
  all: right; split; [constructor; auto using rtc_refl, rtc_one|cbn [term_children]].
  all: repeat first [apply lr_head; assumption|apply lr_tail].
Qed.
Lemma inner_reduction_accessible : forall t, Forall full_SN (term_children t) ->
  Acc (fun u t => inner_reduction t u) t.
Proof.
  intros t HT; pose proof (list_reduction_accessible _ HT) as HS; clear HT.
  remember (term_children t) as xs eqn:HE; revert t HE.
  induction HS as [xs HS IH]; intros t HE; constructor; intros u [_ HU].
  apply (IH (term_children u)); [now rewrite HE|reflexivity].
Qed.

Theorem normalization_by_head_expansion : forall t,
  Forall full_SN (term_children t) ->
  (forall u v, compatible (rtc reduction) t u -> head_reduction u v -> full_SN v) ->
  full_SN t.
Proof.
  intros t HT; pose proof (inner_reduction_accessible _ HT) as HS; clear HT.
  induction HS as [t HS IH]; intro HR; constructor; intros u HU.
  destruct (reduction_head_or_inner _ _ HU) as [HH|HI].
  - apply (HR t u); [apply compatible_reductions_refl|exact HH].
  - apply (IH u HI); intros v w HV HW; apply (HR v w);
      [eapply compatible_reductions_trans; [exact (proj1 HI)|exact HV]|exact HW].
Qed.
Theorem computability_by_head_expansion : forall R, candidate R -> forall t,
  Forall full_SN (term_children t) ->
  (forall u, compatible (rtc reduction) t u -> neutral u) ->
  (forall u v, compatible (rtc reduction) t u -> head_reduction u v -> R v) -> R t.
Proof.
  intros R CR t HT; pose proof (inner_reduction_accessible _ HT) as HS; clear HT.
  induction HS as [t HS IH]; intros HN HR.
  apply (candidate_neutral CR); [apply HN, compatible_reductions_refl|].
  intros u HU; destruct (reduction_head_or_inner _ _ HU) as [HH|HI].
  - apply (HR t u); [apply compatible_reductions_refl|exact HH].
  - apply (IH u HI).
    + intros v HV; apply HN; eapply compatible_reductions_trans; [exact (proj1 HI)|exact HV].
    + intros v w HV HW; apply (HR v w);
        [eapply compatible_reductions_trans; [exact (proj1 HI)|exact HV]|exact HW].
Qed.

Print Assumptions normalization_by_head_expansion.
Print Assumptions computability_by_head_expansion.
