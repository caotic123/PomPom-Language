(* Binary interpretation of small types (universe 0) mutually with the
   interpretation of description codes as relational functors. Type
   relatedness is structural, so related enumeration codes are literally the
   same list of names. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelFix.
Import ListNotations.

Definition choice_rel (n : nat) (FC : nat -> functor) (X : fam) (e : term) : rel :=
  fun t u => exists m, m < n /\ conv e (enum_position m) /\ FC m X t u.

Inductive S2 : term -> term -> rel -> Prop :=
| s2_unit : forall A B, conv A TUnitT -> conv B TUnitT -> S2 A B unit_rel
| s2_uid : forall A B, conv A TUId -> conv B TUId -> S2 A B tag_rel
| s2_enumu : forall A B, conv A TEnumU -> conv B TEnumU -> S2 A B code_rel
| s2_enum : forall A B E E' L,
    conv A (TEnumT E) -> conv B (TEnumT E') -> conv E (code L) -> conv E' (code L) ->
    S2 A B (enum_rel (List.length L))
| s2_pi : forall A B x U V y U' V' RU RV,
    conv A (TPi x U V) -> conv B (TPi y U' V') -> S2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
    S2 A B (pi_rel RU RV)
| s2_sigma : forall A B x U V y U' V' RU RV,
    conv A (TSigma x U V) -> conv B (TSigma y U' V') -> S2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
    S2 A B (sigma_rel RU RV)
| s2_mu : forall A B IT D i IT' D' i' RI F,
    conv A (MuAt IT D i) -> conv B (MuAt IT' D' i') ->
    S2 IT IT' RI -> closed i -> closed i' -> RI i i' ->
    (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp D j) (TApp D' j') (F j)) ->
    S2 A B (mu_rel RI F i)
| s2_close : forall A B IT Fd G i IT' Fd' G' i' RI FF FG,
    conv A (CloseAt IT Fd G i) -> conv B (CloseAt IT' Fd' G' i') ->
    S2 IT IT' RI -> closed i -> closed i' -> RI i i' ->
    D2 RI (TApp Fd i) (TApp Fd' i') FF ->
    (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp G j) (TApp G' j') (FG j)) ->
    S2 A B (roll (FF (mu_rel RI FG)))
| s2_equiv : forall A B R S, S2 A B R -> rel_equiv R S -> S2 A B S
with D2 : rel -> term -> term -> functor -> Prop :=
| d2_var : forall RI D D' i i', conv D (TIVar i) -> conv D' (TIVar i') ->
    closed i -> closed i' -> RI i i' -> D2 RI D D' (fun X => X i)
| d2_one : forall RI D D', conv D TI1 -> conv D' TI1 -> D2 RI D D' (fun _ => unit_rel)
| d2_bot : forall RI D D', conv D TIBot -> conv D' TIBot -> D2 RI D D' (fun _ => empty_rel)
| d2_prod : forall RI D D' A B A' B' FA FB,
    conv D (TIProd A B) -> conv D' (TIProd A' B') ->
    closed A -> closed B -> closed A' -> closed B' ->
    D2 RI A A' FA -> D2 RI B B' FB ->
    D2 RI D D' (fun X => sigma_rel (FA X) (fun _ _ => FB X))
| d2_pi : forall RI D D' A E A' E' RA FE,
    conv D (TIPi A E) -> conv D' (TIPi A' E') ->
    closed A -> closed E -> closed A' -> closed E' -> S2 A A' RA ->
    (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
    D2 RI D D' (fun X => pi_rel RA (fun a _ => FE a X))
| d2_sig : forall RI D D' A E A' E' RA FE,
    conv D (TISig A E) -> conv D' (TISig A' E') ->
    closed A -> closed E -> closed A' -> closed E' -> S2 A A' RA ->
    (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
    D2 RI D D' (fun X => sigma_rel RA (fun a _ => FE a X))
| d2_choice : forall RI D D' E C E' C' L FC,
    conv D (TIChoice E C) -> conv D' (TIChoice E' C') ->
    closed C -> closed C' ->
    conv E (code L) -> conv E' (code L) ->
    (forall n, n < List.length L ->
      D2 RI (TApp C (enum_position n)) (TApp C' (enum_position n)) (FC n)) ->
    D2 RI D D' (fun X => sigma_rel (enum_rel (List.length L)) (fun e _ => choice_rel (List.length L) FC X e))
| d2_equiv : forall RI D D' F G, D2 RI D D' F -> fequiv RI F G -> D2 RI D D' G.

Scheme S2_mind := Minimality for S2 Sort Prop
with D2_mind := Minimality for D2 Sort Prop.
Combined Scheme S2_D2_mind from S2_mind, D2_mind.

(* ------------------------------------------------------------------ *)
(* Conversion invariance of the interpreted syntax *)

Ltac conv_chain := solve [eapply cv_trans; [apply cv_sym; eassumption|eassumption]
  | eassumption | apply cv_sym; eassumption].

Lemma S2_D2_conv :
  (forall A B R, S2 A B R -> forall A' B', conv A A' -> conv B B' -> S2 A' B' R) /\
  (forall RI D D' F, D2 RI D D' F -> forall E E', conv D E -> conv D' E' -> D2 RI E E' F).
Proof.
  apply S2_D2_mind; intros; try solve [econstructor; try conv_chain; eauto].
Qed.
Lemma S2_conv : forall A B R A' B', S2 A B R -> conv A A' -> conv B B' -> S2 A' B' R.
Proof. intros; eapply (proj1 S2_D2_conv); eassumption. Qed.
Lemma D2_conv : forall RI D D' F E E', D2 RI D D' F -> conv D E -> conv D' E' -> D2 RI E E' F.
Proof. intros; eapply (proj2 S2_D2_conv); eassumption. Qed.

(* ------------------------------------------------------------------ *)
(* Canonical shapes *)

Inductive S2_shape (A B : term) (R : rel) : Prop :=
| sh_unit : conv A TUnitT -> conv B TUnitT -> rel_equiv R unit_rel -> S2_shape A B R
| sh_uid : conv A TUId -> conv B TUId -> rel_equiv R tag_rel -> S2_shape A B R
| sh_enumu : conv A TEnumU -> conv B TEnumU -> rel_equiv R code_rel -> S2_shape A B R
| sh_enum : forall E E' L, conv A (TEnumT E) -> conv B (TEnumT E') -> conv E (code L) ->
    conv E' (code L) -> rel_equiv R (enum_rel (List.length L)) -> S2_shape A B R
| sh_pi : forall x U V y U' V' RU RV, conv A (TPi x U V) -> conv B (TPi y U' V') -> S2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
    rel_equiv R (pi_rel RU RV) -> S2_shape A B R
| sh_sigma : forall x U V y U' V' RU RV, conv A (TSigma x U V) -> conv B (TSigma y U' V') -> S2 U U' RU ->
    (forall a b, closed a -> closed b -> RU a b -> S2 (subst a x V) (subst b y V') (RV a b)) ->
    rel_equiv R (sigma_rel RU RV) -> S2_shape A B R
| sh_mu : forall IT D i IT' D' i' RI F, conv A (MuAt IT D i) -> conv B (MuAt IT' D' i') ->
    S2 IT IT' RI -> closed i -> closed i' -> RI i i' ->
    (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp D j) (TApp D' j') (F j)) ->
    rel_equiv R (mu_rel RI F i) -> S2_shape A B R
| sh_close : forall IT Fd G i IT' Fd' G' i' RI FF FG,
    conv A (CloseAt IT Fd G i) -> conv B (CloseAt IT' Fd' G' i') ->
    S2 IT IT' RI -> closed i -> closed i' -> RI i i' ->
    D2 RI (TApp Fd i) (TApp Fd' i') FF ->
    (forall j j', closed j -> closed j' -> RI j j' -> D2 RI (TApp G j) (TApp G' j') (FG j)) ->
    rel_equiv R (roll (FF (mu_rel RI FG))) -> S2_shape A B R.

Lemma S2_shape_equiv : forall A B R S, S2_shape A B R -> rel_equiv R S -> S2_shape A B S.
Proof.
  intros A B R S H HE; destruct H;
    [eapply sh_unit|eapply sh_uid|eapply sh_enumu|eapply sh_enum|eapply sh_pi
    |eapply sh_sigma|eapply sh_mu|eapply sh_close]; try eassumption;
    (eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eassumption]).
Qed.

Lemma S2_view : forall A B R, S2 A B R -> S2_shape A B R.
Proof.
  intros A B R H; induction H.
  - eapply sh_unit; eauto using rel_equiv_refl.
  - eapply sh_uid; eauto using rel_equiv_refl.
  - eapply sh_enumu; eauto using rel_equiv_refl.
  - eapply sh_enum; eauto using rel_equiv_refl.
  - eapply sh_pi; eauto using rel_equiv_refl.
  - eapply sh_sigma; eauto using rel_equiv_refl.
  - eapply sh_mu; eauto using rel_equiv_refl.
  - eapply sh_close; eauto using rel_equiv_refl.
  - eapply S2_shape_equiv; eassumption.
Qed.

Inductive D2_shape (RI : rel) (D D' : term) (F : functor) : Prop :=
| dsh_var : forall i i', conv D (TIVar i) -> conv D' (TIVar i') -> closed i -> closed i' -> RI i i' ->
    fequiv RI F (fun X => X i) -> D2_shape RI D D' F
| dsh_one : conv D TI1 -> conv D' TI1 -> fequiv RI F (fun _ => unit_rel) -> D2_shape RI D D' F
| dsh_bot : conv D TIBot -> conv D' TIBot -> fequiv RI F (fun _ => empty_rel) -> D2_shape RI D D' F
| dsh_prod : forall A B A' B' FA FB, conv D (TIProd A B) -> conv D' (TIProd A' B') ->
    closed A -> closed B -> closed A' -> closed B' ->
    D2 RI A A' FA -> D2 RI B B' FB ->
    fequiv RI F (fun X => sigma_rel (FA X) (fun _ _ => FB X)) -> D2_shape RI D D' F
| dsh_pi : forall A E A' E' RA FE, conv D (TIPi A E) -> conv D' (TIPi A' E') ->
    closed A -> closed E -> closed A' -> closed E' -> S2 A A' RA ->
    (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
    fequiv RI F (fun X => pi_rel RA (fun a _ => FE a X)) -> D2_shape RI D D' F
| dsh_sig : forall A E A' E' RA FE, conv D (TISig A E) -> conv D' (TISig A' E') ->
    closed A -> closed E -> closed A' -> closed E' -> S2 A A' RA ->
    (forall a a', closed a -> closed a' -> RA a a' -> D2 RI (TApp E a) (TApp E' a') (FE a)) ->
    fequiv RI F (fun X => sigma_rel RA (fun a _ => FE a X)) -> D2_shape RI D D' F
| dsh_choice : forall E C E' C' L FC, conv D (TIChoice E C) -> conv D' (TIChoice E' C') ->
    closed C -> closed C' ->
    conv E (code L) -> conv E' (code L) ->
    (forall n, n < List.length L ->
      D2 RI (TApp C (enum_position n)) (TApp C' (enum_position n)) (FC n)) ->
    fequiv RI F (fun X => sigma_rel (enum_rel (List.length L)) (fun e _ => choice_rel (List.length L) FC X e)) ->
    D2_shape RI D D' F.

Lemma D2_shape_equiv : forall RI D D' F G, D2_shape RI D D' F -> fequiv RI F G -> D2_shape RI D D' G.
Proof.
  intros RI D D' F G H HE; destruct H;
    [eapply dsh_var|eapply dsh_one|eapply dsh_bot|eapply dsh_prod|eapply dsh_pi
    |eapply dsh_sig|eapply dsh_choice]; try eassumption;
    (eapply fequiv_trans; [apply fequiv_sym; exact HE|eassumption]).
Qed.

Lemma D2_view : forall RI D D' F, D2 RI D D' F -> D2_shape RI D D' F.
Proof.
  intros RI D D' F H; induction H.
  - eapply dsh_var; eauto using fequiv_refl.
  - eapply dsh_one; eauto using fequiv_refl.
  - eapply dsh_bot; eauto using fequiv_refl.
  - eapply dsh_prod; eauto using fequiv_refl.
  - eapply dsh_pi; eauto using fequiv_refl.
  - eapply dsh_sig; eauto using fequiv_refl.
  - eapply dsh_choice; eauto using fequiv_refl.
  - eapply D2_shape_equiv; eassumption.
Qed.

(* Distinct canonical heads of converted terms exclude each other. *)
Ltac shape_contra := exfalso; match goal with
  | H1 : conv ?A ?n1, H2 : conv ?A ?A', H3 : conv ?A' ?n2 |- _ =>
      eapply head_clash with (t := n1) (u := n2);
      [eapply cv_trans; [apply cv_sym; exact H1|eapply cv_trans; [exact H2|exact H3]]
      |reflexivity|reflexivity|discriminate]
  end.
