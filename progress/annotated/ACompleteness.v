(* Annotation completeness: every raw typing derivation has an annotated
   program with the same erasure and the same type. Together with
   [typing_erasure], annotated and raw typing coincide modulo erasure.
   The raw rules carry formation premises for every result type, so the
   annotations are reconstructed from subderivations. *)
From Stdlib Require Import List Arith Lia.
Require Export annotated.AGenAll.
Import ListNotations.

Definition shape_TPi t := match t with TPi _ _ => True | _ => False end.
Definition shape_TSigma t := match t with TSigma _ _ => True | _ => False end.

Lemma pi_generation : forall Gamma t T, typing Gamma t T ->
  shape_TPi t -> exists A B j k, t = TPi A B /\
  typing Gamma A (Raw.TSort j) /\ typing (erase A :: Gamma) B (Raw.TSort k) /\
  RC.type_comparison (Raw.TSort (Nat.max j k)) T.
Proof. agen. Qed.

Lemma sigma_generation : forall Gamma t T, typing Gamma t T ->
  shape_TSigma t -> exists A B j k, t = TSigma A B /\
  typing Gamma A (Raw.TSort j) /\ typing (erase A :: Gamma) B (Raw.TSort k) /\
  RC.type_comparison (Raw.TSort (Nat.max j k)) T.
Proof. agen. Qed.

Lemma erase_pi_inv : forall t A B, erase t = Raw.TPi A B ->
  exists A' B', t = TPi A' B' /\ erase A' = A /\ erase B' = B.
Proof.
  destruct t; cbn [erase]; intros; try discriminate.
  inversion H; subst; eauto.
Qed.

Lemma erase_sigma_inv : forall t A B, erase t = Raw.TSigma A B ->
  exists A' B', t = TSigma A' B' /\ erase A' = A /\ erase B' = B.
Proof.
  destruct t; cbn [erase]; intros; try discriminate.
  inversion H; subst; eauto.
Qed.

(* An annotated formation of a raw Pi or Sigma type exposes both
   annotation components and their formations. *)
Lemma annotated_pi_formation : forall Gamma t A B k,
  erase t = Raw.TPi A B -> typing Gamma t (Raw.TSort k) ->
  exists A' B' j l, erase A' = A /\ erase B' = B /\
  typing Gamma A' (Raw.TSort j) /\ typing (A :: Gamma) B' (Raw.TSort l).
Proof.
  intros Gamma t A B k HE HT.
  destruct (erase_pi_inv _ _ _ HE) as [A' [B' [-> [<- <-]]]].
  destruct (pi_generation _ _ _ HT I) as [A0 [B0 [j [l [HP [HA [HB _]]]]]]].
  inversion HP; subst; exists A0, B0, j, l; repeat split; assumption.
Qed.

Lemma annotated_sigma_formation : forall Gamma t A B k,
  erase t = Raw.TSigma A B -> typing Gamma t (Raw.TSort k) ->
  exists A' B' j l, erase A' = A /\ erase B' = B /\
  typing Gamma A' (Raw.TSort j) /\ typing (A :: Gamma) B' (Raw.TSort l).
Proof.
  intros Gamma t A B k HE HT.
  destruct (erase_sigma_inv _ _ _ HE) as [A' [B' [-> [<- <-]]]].
  destruct (sigma_generation _ _ _ HT I) as [A0 [B0 [j [l [HP [HA [HB _]]]]]]].
  inversion HP; subst; exists A0, B0, j, l; repeat split; assumption.
Qed.

Ltac open_annotations :=
  repeat match goal with
  | H : exists t, erase t = _ /\ typing _ t _ |- _ =>
      let a := fresh "a" in let He := fresh "He" in let Ht := fresh "Ht" in
      destruct H as [a [He Ht]]
  end.
Ltac open_formations :=
  repeat match goal with
  | He : erase ?t = Raw.TPi _ _, Ht : typing _ ?t (Raw.TSort _) |- _ =>
      let A := fresh "A" in let B := fresh "B" in
      let HA := fresh "HA" in let HB := fresh "HB" in
      destruct (annotated_pi_formation _ _ _ _ _ He Ht)
        as [A [B [? [? [HA [HB [? ?]]]]]]]; clear He Ht
  | He : erase ?t = Raw.TSigma _ _, Ht : typing _ ?t (Raw.TSort _) |- _ =>
      let A := fresh "A" in let B := fresh "B" in
      let HA := fresh "HA" in let HB := fresh "HB" in
      destruct (annotated_sigma_formation _ _ _ _ _ He Ht)
        as [A [B [? [? [HA [HB [? ?]]]]]]]; clear He Ht
  end.
Ltac substitute_erasures :=
  repeat match goal with
  | He : erase ?t = ?x |- _ => is_var x; subst x
  end.

Ltac rebuild := first
  [ eapply ty_cumul; [apply ty_unitT; assumption|lia]
  | eauto 3 using typing ].
Ltac witness := first
  [ match goal with |- exists t, erase t = erase ?x /\ _ =>
      exists x; split; [reflexivity|solve [rebuild]] end
  | refine (ex_intro _ (TVar _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TSort _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TPi _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TLam _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TApp _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TSigma _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TPair _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TFst _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TSnd _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TUnitT) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TUnit) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TUId) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TTag _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TEnumU) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TNilE) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TConsE _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TEnumT _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TEZero _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TESucc _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TEPi _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TSwitch _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIDesc _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIVar _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TI1 _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIBot _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIProd _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIPi _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TISig _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIChoice _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TInterp _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TMuI _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TInMu _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TInClose _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TInd _ _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TIAll _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (THyps _ _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TClose _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TCloseCase _ _ _ _ _ _ _ _) _); split; [reflexivity|solve [rebuild]]
  | refine (ex_intro _ (TCloseInd _ _ _ _ _ _ _) _); split; [reflexivity|solve [rebuild]] ].

Theorem annotation_completeness : forall Gamma r A, RT.typing Gamma r A ->
  exists t, erase t = r /\ typing Gamma t A.
Proof.
  intros Gamma r A H; induction H; open_annotations; open_formations;
    substitute_erasures; witness.
Qed.

(* Raw and annotated typing coincide modulo erasure. *)
Corollary typing_iff_annotation : forall Gamma r A,
  RT.typing Gamma r A <-> exists t, erase t = r /\ typing Gamma t A.
Proof.
  intros Gamma r A; split; [apply annotation_completeness|].
  intros [t [<- Ht]]; exact (typing_erasure _ _ _ Ht).
Qed.

Print Assumptions annotation_completeness.
