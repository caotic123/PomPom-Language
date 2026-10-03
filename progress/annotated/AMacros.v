(* Annotated replicas of the raw derived operators used inside root reducts.
   Every lift sits on a leaf subterm so that [erase] commutes with binding
   operations after [erase_lift]/[erase_subst] normalization. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AGeneration annotated.AFunctions.
Import ListNotations.
Module RCore := nameless.DBCore.
Module DT := nameless.DBDerivedTyping.
Module RO := nameless.DBOperatorFormations.
Module RG := nameless.DBGeneration.

(* ---- application helpers ---- *)

(* X i for X : Family IT *)
Definition afamily_app (IT X a : term) : term := TApp IT (TSort 0) X a.
(* D a for D : Def IT *)
Definition adef_app (IT D a : term) : term := TApp IT (TIDesc (lift 1 0 IT)) D a.
(* CloseAt IT F G i *)
Definition aCloseAt (IT F G i : term) : term :=
  TApp IT (TSort 0) (TClose IT F G) i.
(* MuAt IT D i *)
Definition aMuAt (IT D i : term) : term := TApp IT (TSort 0) (TMuI IT D) i.
Definition acarrier (IT G : term) : term := TClose IT G G.
Definition apayload (IT F G i : term) : term :=
  TInterp IT (adef_app IT F i) (acarrier IT G).
(* Def IT as an annotated type *)
Definition aDef (IT : term) : term := TPi IT (TIDesc (lift 1 0 IT)).

(* Σ i:IT. X i *)
Definition atotal (IT X : term) : term :=
  TSigma IT (afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0)).
Definition amotive (IT X : term) : term := TPi (atotal IT X) (TSort 0).

(* the (i, x) pair used by recursive methods, in context [x : X i, i : IT] *)
Definition arec_pair (IT X : term) : term :=
  TPair (lift 2 0 IT)
    (afamily_app (lift 1 0 (lift 2 0 IT)) (lift 1 0 (lift 2 0 X)) (TVar 0))
    (TVar 1) (TVar 0).

(* codomain of a recursive method: Π x:X i. P (i,x) *)
Definition arec_codomain (IT X P : term) : term :=
  TPi (afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0))
    (TApp (atotal (lift 2 0 IT) (lift 2 0 X)) (TSort 0) (lift 2 0 P)
      (arec_pair IT X)).
Definition arecursive_method (IT X P : term) : term :=
  TPi IT (arec_codomain IT X P).

(* enum tail motive: λ e:Enum E. P (succ e) *)
Definition atail_motive (k : nat) (tag E P : term) : term :=
  TLam (TEnumT E) (TSort k)
    (TApp (TEnumT (TConsE (lift 1 0 tag) (lift 1 0 E))) (TSort k)
      (lift 1 0 P) (TESucc (lift 1 0 tag) (lift 1 0 E) (TVar 0))).

(* non-dependent product of two sorts *)
Definition aproduct (A B : term) : term := TSigma A (lift 1 0 B).
Definition aarrow (A B : term) : term := TPi A (lift 1 0 B).
Definition abot : term := TEnumT TNilE.

(* (↑D) #0 under one binder — the description self-application *)
Definition adesc_app_binder (IT A D : term) : term :=
  TApp (lift 1 0 A) (TIDesc (lift 2 0 IT)) (lift 1 0 D) (TVar 0).
Definition adesc_app_binder_enum (IT E D : term) : term :=
  TApp (TEnumT (lift 1 0 E)) (TIDesc (lift 2 0 IT)) (lift 1 0 D) (TVar 0).

(* interpretation of a dependent description under one binder:
   Interp ↑IT ((↑D) #0) ↑X *)
Definition ainterp_binder (IT A D X : term) : term :=
  TInterp (lift 1 0 IT) (adesc_app_binder IT A D) (lift 1 0 X).
Definition ainterp_binder_enum (IT E D X : term) : term :=
  TInterp (lift 1 0 IT) (adesc_app_binder_enum IT E D) (lift 1 0 X).

(* the f-application inside dependent-iall/hyps binders: f #0 *)
Definition aapp_binder (IT A D X f : term) : term :=
  TApp (lift 1 0 A)
    (TInterp (lift 2 0 IT)
      (TApp (lift 2 0 A) (TIDesc (lift 3 0 IT)) (lift 2 0 D) (TVar 0))
      (lift 2 0 X))
    (lift 1 0 f) (TVar 0).

(* IAll ↑IT ((↑D)#0) ↑X ((↑f)#0) ↑P under one binder *)
Definition aiall_binder (IT A D X f P : term) : term :=
  TIAll (lift 1 0 IT) (adesc_app_binder IT A D) (lift 1 0 X)
    (aapp_binder IT A D X f) (lift 1 0 P).
(* Hyps ↑IT ((↑D)#0) ↑X ↑P ↑h ((↑f)#0) under one binder *)
Definition ahyps_binder (IT A D X P h f : term) : term :=
  THyps (lift 1 0 IT) (adesc_app_binder IT A D) (lift 1 0 X)
    (lift 1 0 P) (lift 1 0 h) (aapp_binder IT A D X f).

(* the pair of recursive calls in the iprod hyps step *)
Definition ahyps_prod_pair (IT A B X P h a b : term) : term :=
  TPair (TIAll IT A X a P) (lift 1 0 (TIAll IT B X b P))
    (THyps IT A X P h a) (THyps IT B X P h b).

(* P #0 head of the enum π cons step *)
Definition aepi_head (k : nat) (tag E P : term) : term :=
  TApp (TEnumT (TConsE tag E)) (TSort k) P (TEZero tag E).

(* self-application D a for the isig/ichoice iall steps:
   D a where D : A -> IDesc IT *)
Definition ainstantiate (IT A D a : term) : term :=
  TApp A (lift 1 0 (TIDesc IT)) D a.
Definition ainstantiate_enum (IT E D e : term) : term :=
  TApp (TEnumT E) (lift 1 0 (TIDesc IT)) D e.

(* ---- mu induction ---- *)

(* λ i:IT. λ x:(μ-ann i). Ind (↑²IT)(↑²D)(↑²P)(↑²st) i x *)
Definition amu_rec_body (IT D P st : term) : term :=
  TInd (lift 2 0 IT) (lift 2 0 D) (lift 2 0 P) (lift 2 0 st) (TVar 1) (TVar 0).
Definition amu_rec_lam (IT D P st : term) : term :=
  TLam IT (arec_codomain IT (TMuI IT D) P)
    (TLam
      (afamily_app (lift 1 0 IT) (TMuI (lift 1 0 IT) (lift 1 0 D)) (TVar 0))
      (TApp (atotal (lift 2 0 IT) (TMuI (lift 2 0 IT) (lift 2 0 D))) (TSort 0)
        (lift 2 0 P) (arec_pair IT (TMuI IT D)))
      (amu_rec_body IT D P st)).

(* ---- close induction ---- *)

(* λ p:total IT (carrier IT G). P↑ G↑ (fst p) (snd p)
   Spine annotations are literal subst-instances of the motive's Pi parts so
   erasure lands on exactly the raw computed types. *)
Definition adiagonal_motive (IT G P : term) : term :=
  TLam (atotal IT (acarrier IT G)) (TSort 0)
    (TApp
      (subst (TFst (lift 1 0 IT)
              (afamily_app (lift 1 0 (lift 1 0 IT))
                (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
                (TVar 0))
              (TVar 0)) 0
        (subst (lift 1 0 G) 1
          (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))))
      (TSort 0)
      (TApp (subst (lift 1 0 G) 0 (lift 2 0 IT))
        (subst (lift 1 0 G) 1
          (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
            (TSort 0)))
        (TApp (aDef (lift 1 0 IT))
          (TPi (lift 2 0 IT)
            (TPi (aCloseAt (lift 3 0 IT) (TVar 1) (lift 3 0 G) (TVar 0))
              (TSort 0)))
          (lift 1 0 P) (lift 1 0 G))
        (TFst (lift 1 0 IT)
          (afamily_app (lift 1 0 (lift 1 0 IT))
            (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
            (TVar 0))
          (TVar 0)))
      (TSnd (lift 1 0 IT)
        (afamily_app (lift 1 0 (lift 1 0 IT))
          (lift 1 0 (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)))
          (TVar 0))
        (TVar 0))).

(* λ i:IT. λ x:(carrier i). CloseInd (↑²IT)(↑²G)(↑²P)(↑²st)(↑²G) i x
   — the recursive call recurses on G, the carrier's own description. *)
Definition aclose_rec_body (IT G P st : term) : term :=
  TCloseInd (lift 2 0 IT) (lift 2 0 G) (lift 2 0 P) (lift 2 0 st)
    (lift 2 0 G) (TVar 1) (TVar 0).
Definition aclose_rec_lam (IT G P st : term) : term :=
  TLam IT (arec_codomain IT (acarrier IT G) (adiagonal_motive IT G P))
    (TLam
      (afamily_app (lift 1 0 IT)
        (TClose (lift 1 0 IT) (lift 1 0 G) (lift 1 0 G)) (TVar 0))
      (TApp (atotal (lift 2 0 IT)
              (TClose (lift 2 0 IT) (lift 2 0 G) (lift 2 0 G)))
        (TSort 0)
        (lift 2 0 (adiagonal_motive IT G P))
        (arec_pair IT (acarrier IT G)))
      (aclose_rec_body IT G P st)).

(* ---- mu induction method spine ---- *)

(* the three binder domains / codomain of mu_ind_method as annotated terms:
   ctx [i:IT]    payload: Interp ↑IT ((↑D) #0) (μ ↑IT ↑D) *)
Definition amu_payload (IT D : term) : term :=
  TInterp (lift 1 0 IT)
    (adef_app (lift 1 0 IT) (lift 1 0 D) (TVar 0))
    (TMuI (lift 1 0 IT) (lift 1 0 D)).
(* ctx [x:payload, i:IT]    iall: IAll ↑²IT ((↑²D) #1) (μ ↑²IT ↑²D) #0 ↑²P *)
Definition amu_iall (IT D P : term) : term :=
  TIAll (lift 2 0 IT)
    (adef_app (lift 2 0 IT) (lift 2 0 D) (TVar 1))
    (TMuI (lift 2 0 IT) (lift 2 0 D)) (TVar 0) (lift 2 0 P).
(* ctx [h:iall, x:payload, i:IT]    result: (↑³P) (i, in x) *)
Definition amu_result (IT D P : term) : term :=
  TApp (atotal (lift 3 0 IT) (TMuI (lift 3 0 IT) (lift 3 0 D))) (TSort 0)
    (lift 3 0 P)
    (TPair (lift 3 0 IT)
      (afamily_app (lift 1 0 (lift 3 0 IT))
        (lift 1 0 (TMuI (lift 3 0 IT) (lift 3 0 D))) (TVar 0))
      (TVar 2) (TInMu (lift 3 0 IT) (lift 3 0 D) (TVar 2) (TVar 1))).
Definition amu_ind_codomain (IT D P : term) : term :=
  TPi (amu_payload IT D) (TPi (amu_iall IT D P) (amu_result IT D P)).
Definition amu_ind_method (IT D P : term) : term :=
  TPi IT (amu_ind_codomain IT D P).

(* the st i xs hs spine with codomain annotations as literal subst
   instances of the method type's subterms *)
Definition amethod_app (IT D P st i xs hs : term) : term :=
  TApp (subst xs 0 (subst i 1 (amu_iall IT D P)))
    (subst xs 1 (subst i 2 (amu_result IT D P)))
    (TApp (subst i 0 (amu_payload IT D))
      (subst i 1 (TPi (amu_iall IT D P) (amu_result IT D P)))
      (TApp IT (amu_ind_codomain IT D P) st i)
      xs)
    hs.

(* ---- close induction method spine ---- *)

(* binder domains of close_ind_method = Π F:Def. Π i:IT. Π xs:payload. Π hs:iall. res *)
(* ctx [i,F,Γ] *) Definition acim_payload (IT G : term) : term :=
  apayload (lift 2 0 IT) (TVar 1) (lift 2 0 G) (TVar 0).
(* ctx [xs,i,F,Γ] *) Definition acim_iall (IT G P : term) : term :=
  TIAll (lift 3 0 IT) (adef_app (lift 3 0 IT) (TVar 2) (TVar 1))
    (acarrier (lift 3 0 IT) (lift 3 0 G)) (TVar 0)
    (lift 3 0 (adiagonal_motive IT G P)).
(* ctx [hs,xs,i,F,Γ]: the motive-application (↑⁴P) F i (in x) with
   codomain annotations as literal subst-instances. *)
Definition acim_result (IT G P : term) : term :=
  TApp (subst (TVar 2) 0 (subst (TVar 3) 1
        (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))))
    (TSort 0)
    (TApp (subst (TVar 3) 0 (lift 5 0 IT))
      (subst (TVar 3) 1
        (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0)) (TSort 0)))
      (TApp (aDef (lift 4 0 IT))
        (TPi (lift 5 0 IT)
          (TPi (aCloseAt (lift 6 0 IT) (TVar 1) (lift 6 0 G) (TVar 0))
            (TSort 0)))
        (lift 4 0 P) (TVar 3))
      (TVar 2))
    (TInClose (lift 4 0 IT) (TVar 3) (lift 4 0 G) (TVar 2) (TVar 1)).
(* ctx [F,Γ] *) Definition acim_rest (IT G P : term) : term :=
  TPi (lift 1 0 IT)
    (TPi (acim_payload IT G)
      (TPi (acim_iall IT G P) (acim_result IT G P))).
Definition acim_method (IT G P : term) : term :=
  TPi (aDef IT) (acim_rest IT G P).

(* the st F i xs hs spine, annotations = literal subst-instances *)
Definition acmethod_app (IT G P st F i xs hs : term) : term :=
  TApp (subst xs 0 (subst i 1 (subst F 2 (acim_iall IT G P))))
    (subst xs 1 (subst i 2 (subst F 3 (acim_result IT G P))))
    (TApp (subst i 0 (subst F 1 (acim_payload IT G)))
      (subst i 1 (subst F 2 (TPi (acim_iall IT G P) (acim_result IT G P))))
      (TApp (subst F 0 (lift 1 0 IT))
        (subst F 1 (TPi (acim_payload IT G)
          (TPi (acim_iall IT G P) (acim_result IT G P))))
        (TApp (aDef IT) (acim_rest IT G P) st F)
        i)
      xs)
    hs.

(* close_case reduct: b xs where b : Π x:payload. (↑Q) (in x) *)
Definition aclose_case_codomain (k : nat) (IT F G i Q : term) : term :=
  TApp (aCloseAt (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G) (lift 1 0 i))
    (TSort k) (lift 1 0 Q)
    (TInClose (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G) (lift 1 0 i) (TVar 0)).


(* Σ-pair (i, x) of the total type, and motive application P (i,x) *)
Definition atotal_pair (IT X i x : term) : term :=
  TPair IT (afamily_app (lift 1 0 IT) (lift 1 0 X) (TVar 0)) i x.
Definition amotive_app (IT X P p : term) : term :=
  TApp (atotal IT X) (TSort 0) P p.

(* (h i) x for h : recursive_method IT X P *)
Definition arec_app (IT X P h i x : term) : term :=
  TApp (afamily_app IT X i)
    (TApp (atotal (lift 1 0 IT) (lift 1 0 X)) (TSort 0) (lift 1 0 P)
      (atotal_pair (lift 1 0 IT) (lift 1 0 X) (lift 1 0 i) (TVar 0)))
    (TApp IT (arec_codomain IT X P) h i) x.

(* the hyps argument of the mu induction reduct *)
Definition ahyps_mu (IT D P st i xs : term) : term :=
  THyps IT (adef_app IT D i) (TMuI IT D) P (amu_rec_lam IT D P st) xs.
Definition amu_ind_reduct (IT D P st i xs : term) : term :=
  amethod_app IT D P st i xs (ahyps_mu IT D P st i xs).

(* the hyps argument of the close induction reduct *)
Definition ahyps_close (IT F G P st i xs : term) : term :=
  THyps IT (adef_app IT F i) (acarrier IT G) (adiagonal_motive IT G P)
    (aclose_rec_lam IT G P st) xs.
Definition aclose_ind_reduct (IT G P st F i xs : term) : term :=
  acmethod_app IT G P st F i xs (ahyps_close IT F G P st i xs).

Ltac anorm := cbn [erase]; repeat rewrite erase_lift; repeat rewrite erase_subst.

Lemma erase_afamily_app : forall IT X a,
  erase (afamily_app IT X a) = Raw.TApp (erase X) (erase a).
Proof. intros; reflexivity. Qed.
Lemma erase_adef_app : forall IT D a,
  erase (adef_app IT D a) = Raw.TApp (erase D) (erase a).
Proof. intros; reflexivity. Qed.
Lemma erase_aCloseAt : forall IT F G i,
  erase (aCloseAt IT F G i) = Raw.CloseAt (erase IT) (erase F) (erase G) (erase i).
Proof. intros; reflexivity. Qed.
Lemma erase_aMuAt : forall IT D i,
  erase (aMuAt IT D i) = Raw.MuAt (erase IT) (erase D) (erase i).
Proof. intros; reflexivity. Qed.
Lemma erase_apayload : forall IT F G i,
  erase (apayload IT F G i) = Raw.payload (erase IT) (erase F) (erase G) (erase i).
Proof. intros; reflexivity. Qed.
Lemma erase_atotal : forall IT X,
  erase (atotal IT X) = Raw.total (erase IT) (erase X).
Proof. intros; unfold atotal, afamily_app, Raw.total; anorm; reflexivity. Qed.
Lemma erase_amotive : forall IT X,
  erase (amotive IT X) = Raw.motive (erase IT) (erase X).
Proof.
  intros; unfold amotive, Raw.motive; anorm; rewrite erase_atotal; reflexivity.
Qed.
Lemma erase_arec_pair : forall IT X,
  erase (arec_pair IT X) = Raw.TPair (Raw.TVar 1) (Raw.TVar 0).
Proof. intros; unfold arec_pair, afamily_app; anorm; reflexivity. Qed.
Lemma erase_arec_codomain : forall IT X P,
  erase (arec_codomain IT X P) =
    Raw.TPi (Raw.TApp (Raw.lift 1 0 (erase X)) (Raw.TVar 0))
      (Raw.TApp (Raw.lift 2 0 (erase P)) (Raw.TPair (Raw.TVar 1) (Raw.TVar 0))).
Proof.
  intros; unfold arec_codomain, afamily_app, atotal, arec_pair; anorm.
  reflexivity.
Qed.
Lemma erase_arecursive_method : forall IT X P,
  erase (arecursive_method IT X P) =
    Raw.recursive_method (erase IT) (erase X) (erase P).
Proof.
  intros; unfold arecursive_method, Raw.recursive_method; anorm.
  rewrite erase_arec_codomain; reflexivity.
Qed.
Lemma erase_atail_motive : forall k tag E P,
  erase (atail_motive k tag E P) =
    Raw.TLam (Raw.TApp (Raw.lift 1 0 (erase P))
      (Raw.TESucc (Raw.TVar 0))).
Proof. intros; unfold atail_motive; anorm; reflexivity. Qed.
Lemma erase_adiagonal_motive : forall IT G P,
  erase (adiagonal_motive IT G P) = Raw.diagonal_motive (erase G) (erase P).
Proof.
  intros; unfold adiagonal_motive, atotal, afamily_app, acarrier, aCloseAt,
    Raw.diagonal_motive; anorm; reflexivity.
Qed.

Print Assumptions erase_adiagonal_motive.
