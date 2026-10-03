(* Generation lemmas for every annotated constructor used by root
   preservation.  Each follows the same shape-based pattern: induct on
   typing, discard shape mismatches, transport the comparison through the
   three type-changing rules. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AMacros.
Import ListNotations.

Definition shape_TConsE t := match t with TConsE _ _ => True | _ => False end.
Definition shape_TEZero t := match t with TEZero _ _ => True | _ => False end.
Definition shape_TESucc t := match t with TESucc _ _ _ => True | _ => False end.
Definition shape_TEPi t := match t with TEPi _ _ _ => True | _ => False end.
Definition shape_TSwitch t := match t with TSwitch _ _ _ _ _ => True | _ => False end.
Definition shape_TIVar t := match t with TIVar _ _ => True | _ => False end.
Definition shape_TI1 t := match t with TI1 _ => True | _ => False end.
Definition shape_TIBot t := match t with TIBot _ => True | _ => False end.
Definition shape_TIProd t := match t with TIProd _ _ _ => True | _ => False end.
Definition shape_TIPi t := match t with TIPi _ _ _ => True | _ => False end.
Definition shape_TISig t := match t with TISig _ _ _ => True | _ => False end.
Definition shape_TIChoice t := match t with TIChoice _ _ _ => True | _ => False end.
Definition shape_TInterp t := match t with TInterp _ _ _ => True | _ => False end.
Definition shape_TMuI t := match t with TMuI _ _ => True | _ => False end.
Definition shape_TInMu t := match t with TInMu _ _ _ _ => True | _ => False end.
Definition shape_TInClose t := match t with TInClose _ _ _ _ _ => True | _ => False end.
Definition shape_TIAll t := match t with TIAll _ _ _ _ _ => True | _ => False end.
Definition shape_THyps t := match t with THyps _ _ _ _ _ _ => True | _ => False end.
Definition shape_TInd t := match t with TInd _ _ _ _ _ _ => True | _ => False end.
Definition shape_TClose t := match t with TClose _ _ _ => True | _ => False end.
Definition shape_TCloseCase t := match t with TCloseCase _ _ _ _ _ _ _ _ => True | _ => False end.
Definition shape_TCloseInd t := match t with TCloseInd _ _ _ _ _ _ _ => True | _ => False end.

Ltac agen :=
  intros Gamma t T H; induction H; intros HS; cbn in HS; try contradiction;
  try match goal with
  | IH : _ -> exists _, _ |- _ => destruct (IH HS)
  end;
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end; subst;
  repeat eexists; repeat split; try reflexivity; try eassumption;
  first
    [ apply RC.cmp_conversion, RCore.cv_refl
    | eapply RC.comparison_right_conversion; eassumption
    | eapply RC.comparison_transitive;
      [ eassumption
      | apply RC.comparison_universe;
        first [apply RT.ul_sort | apply RT.ul_pi]; eassumption ] ].

Lemma conse_generation : forall Gamma t T, typing Gamma t T ->
  shape_TConsE t -> exists tag E,
  t = TConsE tag E /\ typing Gamma tag Raw.TUId /\ typing Gamma E Raw.TEnumU /\
  RC.type_comparison Raw.TEnumU T.
Proof. agen. Qed.

Lemma zero_generation : forall Gamma t T, typing Gamma t T ->
  shape_TEZero t -> exists tag E, t = TEZero tag E /\
  typing Gamma tag Raw.TUId /\ typing Gamma E Raw.TEnumU /\
  RC.type_comparison (Raw.TEnumT (Raw.TConsE (erase tag) (erase E))) T.
Proof. agen. Qed.

Lemma succ_generation : forall Gamma t T, typing Gamma t T ->
  shape_TESucc t -> exists tag E n, t = TESucc tag E n /\
  typing Gamma tag Raw.TUId /\ typing Gamma E Raw.TEnumU /\
  typing Gamma n (Raw.TEnumT (erase E)) /\
  RC.type_comparison (Raw.TEnumT (Raw.TConsE (erase tag) (erase E))) T.
Proof. agen. Qed.

Lemma epi_generation : forall Gamma t T, typing Gamma t T ->
  shape_TEPi t -> exists k E P, t = TEPi k E P /\
  typing Gamma E Raw.TEnumU /\
  typing Gamma P (Raw.TPi (Raw.TEnumT (erase E)) (Raw.TSort k)) /\
  RC.type_comparison (Raw.TSort k) T.
Proof. agen. Qed.

Lemma switch_generation : forall Gamma t T, typing Gamma t T ->
  shape_TSwitch t -> exists k E P p e, t = TSwitch k E P p e /\
  typing Gamma E Raw.TEnumU /\
  typing Gamma P (Raw.TPi (Raw.TEnumT (erase E)) (Raw.TSort k)) /\
  typing Gamma p (Raw.TEPi k (erase E) (erase P)) /\
  typing Gamma e (Raw.TEnumT (erase E)) /\
  RC.type_comparison (Raw.TApp (erase P) (erase e)) T.
Proof. agen. Qed.

Lemma ivar_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIVar t -> exists IT i, t = TIVar IT i /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma i (erase IT) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma i1_generation : forall Gamma t T, typing Gamma t T ->
  shape_TI1 t -> exists IT, t = TI1 IT /\
  typing Gamma IT (Raw.TSort 0) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma ibot_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIBot t -> exists IT, t = TIBot IT /\
  typing Gamma IT (Raw.TSort 0) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma iprod_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIProd t -> exists IT A B, t = TIProd IT A B /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma A (Raw.TIDesc (erase IT)) /\
  typing Gamma B (Raw.TIDesc (erase IT)) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma ipi_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIPi t -> exists IT A D, t = TIPi IT A D /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma A (Raw.TSort 0) /\
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma isig_generation : forall Gamma t T, typing Gamma t T ->
  shape_TISig t -> exists IT A D, t = TISig IT A D /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma A (Raw.TSort 0) /\
  typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma ichoice_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIChoice t -> exists IT E D, t = TIChoice IT E D /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma E Raw.TEnumU /\
  typing Gamma D (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT))) /\
  RC.type_comparison (Raw.TIDesc (erase IT)) T.
Proof. agen. Qed.

Lemma interp_generation : forall Gamma t T, typing Gamma t T ->
  shape_TInterp t -> exists IT D X, t = TInterp IT D X /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.TIDesc (erase IT)) /\
  typing Gamma X (Raw.Family (erase IT)) /\
  RC.type_comparison (Raw.TSort 0) T.
Proof. agen. Qed.

Lemma mui_generation : forall Gamma t T, typing Gamma t T ->
  shape_TMuI t -> exists IT D, t = TMuI IT D /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.Def (erase IT)) /\
  RC.type_comparison (Raw.Family (erase IT)) T.
Proof. agen. Qed.

Lemma in_mui_generation : forall Gamma t T, typing Gamma t T ->
  shape_TInMu t -> exists IT D i xs, t = TInMu IT D i xs /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.Def (erase IT)) /\
  typing Gamma i (erase IT) /\
  typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
    (Raw.TMuI (erase IT) (erase D))) /\
  RC.type_comparison (Raw.MuAt (erase IT) (erase D) (erase i)) T.
Proof. agen. Qed.

Lemma in_close_generation : forall Gamma t T, typing Gamma t T ->
  shape_TInClose t -> exists IT F G i xs, t = TInClose IT F G i xs /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma F (Raw.Def (erase IT)) /\
  typing Gamma G (Raw.Def (erase IT)) /\ typing Gamma i (erase IT) /\
  typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) /\
  RC.type_comparison (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) T.
Proof. agen. Qed.

Lemma iall_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIAll t -> exists IT D X xs P, t = TIAll IT D X xs P /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.TIDesc (erase IT)) /\
  typing Gamma X (Raw.Family (erase IT)) /\
  typing Gamma xs (Raw.TInterp (erase IT) (erase D) (erase X)) /\
  typing Gamma P (Raw.motive (erase IT) (erase X)) /\
  RC.type_comparison (Raw.TSort 0) T.
Proof. agen. Qed.

Lemma hyps_generation : forall Gamma t T, typing Gamma t T ->
  shape_THyps t -> exists IT D X P h xs, t = THyps IT D X P h xs /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.TIDesc (erase IT)) /\
  typing Gamma X (Raw.Family (erase IT)) /\
  typing Gamma P (Raw.motive (erase IT) (erase X)) /\
  typing Gamma h (Raw.recursive_method (erase IT) (erase X) (erase P)) /\
  typing Gamma xs (Raw.TInterp (erase IT) (erase D) (erase X)) /\
  RC.type_comparison (Raw.TIAll (erase IT) (erase D) (erase X) (erase xs)
    (erase P)) T.
Proof. agen. Qed.

Lemma ind_generation : forall Gamma t T, typing Gamma t T ->
  shape_TInd t -> exists IT D P st i x, t = TInd IT D P st i x /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma D (Raw.Def (erase IT)) /\
  typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) /\
  typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) /\
  typing Gamma i (erase IT) /\
  typing Gamma x (Raw.MuAt (erase IT) (erase D) (erase i)) /\
  RC.type_comparison (Raw.TApp (erase P) (Raw.TPair (erase i) (erase x))) T.
Proof. agen. Qed.

Lemma close_generation : forall Gamma t T, typing Gamma t T ->
  shape_TClose t -> exists IT F G, t = TClose IT F G /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma F (Raw.Def (erase IT)) /\
  typing Gamma G (Raw.Def (erase IT)) /\
  RC.type_comparison (Raw.Family (erase IT)) T.
Proof. agen. Qed.

Lemma close_case_generation : forall Gamma t T, typing Gamma t T ->
  shape_TCloseCase t -> exists k IT F G i Q b x, t = TCloseCase k IT F G i Q b x /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma F (Raw.Def (erase IT)) /\
  typing Gamma G (Raw.Def (erase IT)) /\ typing Gamma i (erase IT) /\
  typing Gamma Q (Raw.TPi (Raw.CloseAt (erase IT) (erase F) (erase G)
    (erase i)) (Raw.TSort k)) /\
  typing Gamma b (Raw.close_case_method (erase IT) (erase F) (erase G)
    (erase i) (erase Q)) /\
  typing Gamma x (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) /\
  RC.type_comparison (Raw.TApp (erase Q) (erase x)) T.
Proof. agen. Qed.

Lemma close_ind_generation : forall Gamma t T, typing Gamma t T ->
  shape_TCloseInd t -> exists IT G P st F i x, t = TCloseInd IT G P st F i x /\
  typing Gamma IT (Raw.TSort 0) /\ typing Gamma G (Raw.Def (erase IT)) /\
  typing Gamma P (Raw.close_motive (erase IT) (erase G)) /\
  typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) /\
  typing Gamma F (Raw.Def (erase IT)) /\ typing Gamma i (erase IT) /\
  typing Gamma x (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) /\
  RC.type_comparison (Raw.TApp (Raw.TApp (Raw.TApp (erase P) (erase F))
    (erase i)) (erase x)) T.
Proof. agen. Qed.
