(* ========================================================================== *)
(*  TypeRulesCore.v — the minimal PomPom calculus of progress/type-rules.md,      *)
(*  stated relationally in Rocq.                                              *)
(*                                                                            *)
(*  This file is a SPECIFICATION of the checker described by type-rules.md    *)
(*  (the relational counterpart of app/Checker.hs's typeRules for the         *)
(*  minimal language), not an algorithm. Metatheory statements and proofs    *)
(*  live in individual theorem files, exported together by TypeRules.v.       *)
(*  Every displayed rule of the sketch appears below with its ASCII version   *)
(*  quoted in the comment directly above its constructor.  Statement          *)
(*  choices, all licensed by the sketch itself:                               *)
(*                                                                            *)
(*   - Binding is de Bruijn, so 'capture-avoiding alpha equivalence' (§1) is  *)
(*     the representation itself.                                             *)
(*   - Conversion Γ ⊢ t ≡ u : A is presented UNTYPED (conv), as the           *)
(*     algorithmic reading of §1's generator list: beta and eta for           *)
(*     functions, projection computation for pairs, and the computation       *)
(*     rules for switchₖ, iinduction, and case, closed under congruence.      *)
(*     There is no definition mechanism in the minimal language, so           *)
(*     'transparent definition unfolding' is vacuous here.                    *)
(*   - step is weak-head: the displayed ↦ rules plus congruence only in the   *)
(*     positions a rule inspects — 'the implementation may normalize only as  *)
(*     far as a rule needs' (§1).  conv adds full congruence.                 *)
(*   - One index type per family: `IData [Term]`/`IVar [Term]` packaging is   *)
(*     surface sugar (§1, packTy/packVal), so the core has IDesc I / 'var i.  *)
(*   - List is 'an ordinary small datatype of the PomPom library' (§1); the   *)
(*     minimal calculus takes it primitive so that §7's evaluated-spine side  *)
(*     conditions (labels (S i) ⇓ Φ, c ∈ Φ, Φ ⊆ Ψ) can be stated directly.    *)
(*     Member/Subset/Disjoint of progress/2.pom are library programs and are  *)
(*     deliberately ABSENT from the core rules (§6, third-pass layering).     *)
(*   - Elaboration is out of scope: At/NoDupEnum name resolution, the κ       *)
(*     table, packTy/packVal, and surface µ sugar (§3, §9).  Labels are       *)
(*     ambient positions: Label E := EnumT E.                                 *)
(*   - The paper's Rule 5 stays out of the declarative calculus (§7), and    *)
(*     Sig-case's Ψ ⊆ Φ restriction is a diagnostic, not a rule (§7).         *)
(*   - General definitional equality is ≡βη.  The paper's optional φ pruning  *)
(*     remains in the typed signature-subtyping rule [su_sig].  Pruning is    *)
(*     positive evidence only — a stuck description or index never prunes.    *)
(*   - check carries the declarative eliminator rules App-check, Fst-check,   *)
(*     Snd-check (EID Fig. 1 read declaratively; eliminated type chosen       *)
(*     existentially, formation premise explicit), and Sig-case's scrutinee   *)
(*     premise is Γ ⊢ M ⇐ μˢ S i.  Computation creates eliminations of        *)
(*     checked-only canonical forms — the πₖ reduct applies its raw λ motive  *)
(*     — so a purely synthesizing elimination refutes subject reduction.      *)
(*                                                                            *)
(*  Primary references: Elaborating Inductive Definitions, Figs. 1–4;         *)
(*  constructor-subtyping paper, Rules 1–4, 6, 7 (see type-rules.md).         *)
(* ========================================================================== *)

From Stdlib Require Import List Arith String.
Import ListNotations.

Set Implicit Arguments.

(* ========================================================================== *)
(*  1. Syntax of the minimal language                                         *)
(* ========================================================================== *)

Inductive term : Type :=
(* de Bruijn variable *)
| TVar    (n : nat)
(* Setₖ; * = Set₀ and Type = Set₁ (§1) *)
| TSort   (k : nat)
(* (x:A) → B and λx.b — functions at every Setₖ (EID Fig. 1) *)
| TPi     (A B : term)
| TLam    (b : term)
| TApp    (f a : term)
(* (x:A) × B, (a,b), π₀, π₁ — pairs at every Setₖ (EID Fig. 1) *)
| TSigma  (A B : term)
| TPair   (a b : term)
| TFst    (p : term)
| TSnd    (p : term)
(* 1 and unit (EID Fig. 1; packTy [] = 1, πₖ nilE P ↦ 1) *)
| TUnitT
| TUnit
(* enumerations (EID Fig. 2) *)
| TUId
| TTag    (s : string)
| TEnumU
| TNilE
| TConsE  (t E : term)
| TEnumT  (E : term)
| TEZero
| TESucc  (n : term)
(* πₖ E P and switchₖ E P p e — universe-polymorphic (§2) *)
| TEPi    (E P : term)
| TSwitch (E P p e : term)
(* indexed descriptions and codes (EID Fig. 4, §4) *)
| TIDesc  (IT : term)
| TIVar   (i : term)
| TI1
| TIProd  (A B : term)
| TIPi    (Sd T : term)
| TISig   (Sd T : term)
| TIChoice (E T : term)
(* ⟦D⟧ X (§4) *)
| TInterp (D X : term)
(* μᴵ R, μˢ S, in, iinduction R P step, iAll, hyps (§5, §7) *)
| TMuI    (R : term)
| TMuS    (Sf : term)
| TIn     (x : term)
| TInd    (R P stp i x : term)
| TIAll   (D X xs P : term)
| THyps   (D X P h xs : term)
(* library List, primitive here (see header) *)
| TList   (A : term)
| TLNil   (A : term)
| TLCons  (A a l : term)
(* case M of Q { cₖ xs ⇒ Nₖ } — each body binds one variable (§7) *)
| TCase   (M Q : term) (bs : list (term * term)).

(* -------------------------------------------------------------------------- *)
(*  Lifting and substitution                                                  *)
(* -------------------------------------------------------------------------- *)

Fixpoint lift (d k : nat) (t : term) : term :=
  match t with
  | TVar n => if Nat.ltb n k then TVar n else TVar (d + n)
  | TSort s => TSort s
  | TPi A B => TPi (lift d k A) (lift d (S k) B)
  | TLam b => TLam (lift d (S k) b)
  | TApp f a => TApp (lift d k f) (lift d k a)
  | TSigma A B => TSigma (lift d k A) (lift d (S k) B)
  | TPair a b => TPair (lift d k a) (lift d k b)
  | TFst p => TFst (lift d k p)
  | TSnd p => TSnd (lift d k p)
  | TUnitT => TUnitT
  | TUnit => TUnit
  | TUId => TUId
  | TTag s => TTag s
  | TEnumU => TEnumU
  | TNilE => TNilE
  | TConsE tg E => TConsE (lift d k tg) (lift d k E)
  | TEnumT E => TEnumT (lift d k E)
  | TEZero => TEZero
  | TESucc n => TESucc (lift d k n)
  | TEPi E P => TEPi (lift d k E) (lift d k P)
  | TSwitch E P p e => TSwitch (lift d k E) (lift d k P) (lift d k p) (lift d k e)
  | TIDesc IT => TIDesc (lift d k IT)
  | TIVar i => TIVar (lift d k i)
  | TI1 => TI1
  | TIProd A B => TIProd (lift d k A) (lift d k B)
  | TIPi Sd T => TIPi (lift d k Sd) (lift d k T)
  | TISig Sd T => TISig (lift d k Sd) (lift d k T)
  | TIChoice E T => TIChoice (lift d k E) (lift d k T)
  | TInterp D X => TInterp (lift d k D) (lift d k X)
  | TMuI R => TMuI (lift d k R)
  | TMuS Sf => TMuS (lift d k Sf)
  | TIn x => TIn (lift d k x)
  | TInd R P stp i x =>
      TInd (lift d k R) (lift d k P) (lift d k stp) (lift d k i) (lift d k x)
  | TIAll D X xs P =>
      TIAll (lift d k D) (lift d k X) (lift d k xs) (lift d k P)
  | THyps D X P h xs =>
      THyps (lift d k D) (lift d k X) (lift d k P) (lift d k h) (lift d k xs)
  | TList A => TList (lift d k A)
  | TLNil A => TLNil (lift d k A)
  | TLCons A a l => TLCons (lift d k A) (lift d k a) (lift d k l)
  | TCase M Q bs =>
      TCase (lift d k M) (lift d k Q)
            (map (fun '(c, b) => (lift d k c, lift d (S k) b)) bs)
  end.

Fixpoint subst (u : term) (k : nat) (t : term) : term :=
  match t with
  | TVar n => if Nat.ltb n k then TVar n
              else if Nat.eqb n k then lift k 0 u
              else TVar (Nat.pred n)
  | TSort s => TSort s
  | TPi A B => TPi (subst u k A) (subst u (S k) B)
  | TLam b => TLam (subst u (S k) b)
  | TApp f a => TApp (subst u k f) (subst u k a)
  | TSigma A B => TSigma (subst u k A) (subst u (S k) B)
  | TPair a b => TPair (subst u k a) (subst u k b)
  | TFst p => TFst (subst u k p)
  | TSnd p => TSnd (subst u k p)
  | TUnitT => TUnitT
  | TUnit => TUnit
  | TUId => TUId
  | TTag s => TTag s
  | TEnumU => TEnumU
  | TNilE => TNilE
  | TConsE tg E => TConsE (subst u k tg) (subst u k E)
  | TEnumT E => TEnumT (subst u k E)
  | TEZero => TEZero
  | TESucc n => TESucc (subst u k n)
  | TEPi E P => TEPi (subst u k E) (subst u k P)
  | TSwitch E P p e => TSwitch (subst u k E) (subst u k P) (subst u k p) (subst u k e)
  | TIDesc IT => TIDesc (subst u k IT)
  | TIVar i => TIVar (subst u k i)
  | TI1 => TI1
  | TIProd A B => TIProd (subst u k A) (subst u k B)
  | TIPi Sd T => TIPi (subst u k Sd) (subst u k T)
  | TISig Sd T => TISig (subst u k Sd) (subst u k T)
  | TIChoice E T => TIChoice (subst u k E) (subst u k T)
  | TInterp D X => TInterp (subst u k D) (subst u k X)
  | TMuI R => TMuI (subst u k R)
  | TMuS Sf => TMuS (subst u k Sf)
  | TIn x => TIn (subst u k x)
  | TInd R P stp i x =>
      TInd (subst u k R) (subst u k P) (subst u k stp) (subst u k i) (subst u k x)
  | TIAll D X xs P =>
      TIAll (subst u k D) (subst u k X) (subst u k xs) (subst u k P)
  | THyps D X P h xs =>
      THyps (subst u k D) (subst u k X) (subst u k P) (subst u k h) (subst u k xs)
  | TList A => TList (subst u k A)
  | TLNil A => TLNil (subst u k A)
  | TLCons A a l => TLCons (subst u k A) (subst u k a) (subst u k l)
  | TCase M Q bs =>
      TCase (subst u k M) (subst u k Q)
            (map (fun '(c, b) => (subst u k c, subst u (S k) b)) bs)
  end.

(* ========================================================================== *)
(*  2. The §6 signature layer — ordinary pairs, no new former                 *)
(* ========================================================================== *)

(* Label E := EnumT E                                                    (§3) *)
Definition Label (E : term) : term := TEnumT E.

(* Sig I E  :=  (EnumT E → IDesc I) × List (Label E)          -- : Set₁  (§6) *)
Definition Sig (IT E : term) : term :=
  TSigma (TPi (TEnumT E) (TIDesc (lift 1 0 IT)))
         (lift 1 0 (TList (Label E))).

(* {T :: Φ}   :=  (T, Φ)                {T} := {T :: []}                 (§6) *)
Definition sig_pair (T Phi : term) : term := TPair T Phi.

(* branches S :=  π₀ S                  labels S := π₁ S                 (§6) *)
Definition branches (Sg : term) : term := TFst Sg.
Definition labels   (Sg : term) : term := TSnd Sg.

(* Full S     :=  'σ E (branches S)                                      (§6) *)
Definition Full (E Sg : term) : term := TIChoice E (branches Sg).

(* Carrier S := μᴵ (λ i. Full (S i))                                     (§7) *)
Definition Carrier (E Sf : term) : term :=
  TMuI (TLam (Full (lift 1 0 E) (TApp (lift 1 0 Sf) (TVar 0)))).

(* Keep the enum parameter in the raw refinement type.  Otherwise the same
   signature family can be formed at unrelated enums, and an introduction
   checked with one enum can be eliminated by a case checked with another. *)
Definition SigMu (E Sf : term) : term := TMuS (TPair E Sf).

(* -------------------------------------------------------------------------- *)
(*  Canonical ambient positions: 0, 1+0, 1+1+0, …  — 'checked identity is     *)
(*  the ambient position' (context.md); used by the case reduct's 'the        *)
(*  unique k with cₖ = a'.                                                    *)
(* -------------------------------------------------------------------------- *)

Inductive enum_pos : term -> nat -> Prop :=
| pos_zero : enum_pos TEZero 0
| pos_succ : forall c n, enum_pos c n -> enum_pos (TESucc c) (S n).

(* ========================================================================== *)
(*  3. Small-step reduction — the computation rules the conversion of §1      *)
(*     supports.  `in` itself does not reduce (§1); constructor arguments     *)
(*     may (congruence).  Weak-head congruences cover exactly the positions   *)
(*     a rule inspects.                                                       *)
(* ========================================================================== *)

Inductive step : term -> term -> Prop :=

(* (λx. b) a ↦ b[a/x]                                    [beta; EID Fig. 1] *)
| st_beta : forall b a, step (TApp (TLam b) a) (subst a 0 b)

(* π₀ (a , b) ↦ a                                              [EID Fig. 1b] *)
| st_fst : forall a b, step (TFst (TPair a b)) a

(* π₁ (a , b) ↦ b                                              [EID Fig. 1b] *)
| st_snd : forall a b, step (TSnd (TPair a b)) b

(* πₖ nilE        P ↦ 1                                                 (§2) *)
| st_epi_nil : forall P, step (TEPi TNilE P) TUnitT

(* πₖ (consE t E) P ↦ P 0 × πₖ E (P ∘ 1+)                               (§2) *)
| st_epi_cons : forall tg E P,
    step (TEPi (TConsE tg E) P)
         (TSigma (TApp P TEZero)
                 (lift 1 0 (TEPi E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))))))

(* switchₖ (consE t E) P (p₀, ps) 0      ↦ p₀                           (§2) *)
| st_switch_zero : forall tg E P p0 ps,
    step (TSwitch (TConsE tg E) P (TPair p0 ps) TEZero) p0

(* switchₖ (consE t E) P (p₀, ps) (1+n)  ↦ switchₖ E (P ∘ 1+) ps n      (§2) *)
| st_switch_succ : forall tg E P p0 ps n,
    step (TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n))
         (TSwitch E (TLam (TApp (lift 1 0 P) (TESucc (TVar 0)))) ps n)

(* ⟦'var i⟧ X   = X i                                                   (§4) *)
| st_interp_var : forall i X, step (TInterp (TIVar i) X) (TApp X i)

(* ⟦'1⟧ X       = 1                                                     (§4) *)
| st_interp_one : forall X, step (TInterp TI1 X) TUnitT

(* ⟦A '× B⟧ X   = ⟦A⟧ X × ⟦B⟧ X                                          (§4) *)
| st_interp_prod : forall A B X,
    step (TInterp (TIProd A B) X)
         (TSigma (TInterp A X) (lift 1 0 (TInterp B X)))

(* ⟦'Π S T⟧ X   = (s:S) → ⟦T s⟧ X                                        (§4) *)
| st_interp_pi : forall Sd T X,
    step (TInterp (TIPi Sd T) X)
         (TPi Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))

(* ⟦'Σ S T⟧ X   = (s:S) × ⟦T s⟧ X                                        (§4) *)
| st_interp_sig : forall Sd T X,
    step (TInterp (TISig Sd T) X)
         (TSigma Sd (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))

(* ⟦'σ E T⟧ X   = (e:EnumT E) × ⟦T e⟧ X                                  (§4) *)
| st_interp_choice : forall E T X,
    step (TInterp (TIChoice E T) X)
         (TSigma (TEnumT E) (TInterp (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)))

(* iAll ('var j) X x       P = P (j,x)                                  (§5) *)
| st_iall_var : forall j X x P, step (TIAll (TIVar j) X x P) (TApp P (TPair j x))

(* iAll '1       X unit    P = 1                                        (§5) *)
| st_iall_one : forall X P, step (TIAll TI1 X TUnit P) TUnitT

(* iAll (A '× B) X (a,b)   P = iAll A X a P × iAll B X b P              (§5) *)
| st_iall_prod : forall A B X a b P,
    step (TIAll (TIProd A B) X (TPair a b) P)
         (TSigma (TIAll A X a P) (lift 1 0 (TIAll B X b P)))

(* iAll ('Π S T) X f       P = (s:S) → iAll (T s) X (f s) P             (§5) *)
| st_iall_pi : forall Sd T X f P,
    step (TIAll (TIPi Sd T) X f P)
         (TPi Sd (TIAll (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X)
                        (TApp (lift 1 0 f) (TVar 0)) (lift 1 0 P)))

(* iAll ('Σ S T) X (s,x)   P = iAll (T s) X x P                         (§5) *)
| st_iall_sig : forall Sd T X s x P,
    step (TIAll (TISig Sd T) X (TPair s x) P) (TIAll (TApp T s) X x P)

(* iAll ('σ E T) X (e,x)   P = iAll (T e) X x P                         (§5) *)
| st_iall_choice : forall E T X e x P,
    step (TIAll (TIChoice E T) X (TPair e x) P) (TIAll (TApp T e) X x P)

(* hyps ('var j) X P h x       = h j x                                  (§5) *)
| st_hyps_var : forall j X P h x,
    step (THyps (TIVar j) X P h x) (TApp (TApp h j) x)

(* hyps '1       X P h unit    = unit                                   (§5) *)
| st_hyps_one : forall X P h, step (THyps TI1 X P h TUnit) TUnit

(* hyps (A '× B) X P h (a,b)   = (hyps A X P h a, hyps B X P h b)       (§5) *)
| st_hyps_prod : forall A B X P h a b,
    step (THyps (TIProd A B) X P h (TPair a b))
         (TPair (THyps A X P h a) (THyps B X P h b))

(* hyps ('Π S T) X P h f       = λ s. hyps (T s) X P h (f s)            (§5) *)
| st_hyps_pi : forall Sd T X P h f,
    step (THyps (TIPi Sd T) X P h f)
         (TLam (THyps (TApp (lift 1 0 T) (TVar 0)) (lift 1 0 X) (lift 1 0 P)
                      (lift 1 0 h) (TApp (lift 1 0 f) (TVar 0))))

(* hyps ('Σ S T) X P h (s,x)   = hyps (T s) X P h x                     (§5) *)
| st_hyps_sig : forall Sd T X P h s x,
    step (THyps (TISig Sd T) X P h (TPair s x)) (THyps (TApp T s) X P h x)

(* hyps ('σ E T) X P h (e,x)   = hyps (T e) X P h x                     (§5) *)
| st_hyps_choice : forall E T X P h e x,
    step (THyps (TIChoice E T) X P h (TPair e x)) (THyps (TApp T e) X P h x)

(* iinduction R P step i (in xs)                                        (§5)
     ↦ step i xs (hyps (R i) (μᴵ R) P (iinduction R P step) xs)
   — the partial application (iinduction R P step) is its eta-expansion. *)
| st_ind : forall R P stp i xs,
    step (TInd R P stp i (TIn xs))
         (TApp (TApp (TApp stp i) xs)
               (THyps (TApp R i) (TMuI R) P
                      (TLam (TLam (TInd (lift 2 0 R) (lift 2 0 P) (lift 2 0 stp)
                                        (TVar 1) (TVar 0))))
                      xs))

(* case (in (a, xs)) of Q { cₖ xs ⇒ Nₖ }                                (§7)
     ↦ Nₖ[xs]        for the unique k with cₖ = a
   — labels are compared as canonical ambient positions.  On raw terms the
     FIRST matching clause is selected, and the redex fires only once every
     earlier clause label is canonical with a distinct position: canonical
     positions are step-normal, so the selection is stable and raw case
     reduction is deterministic even on the duplicate-label junk Sig-case
     rejects.  Without this, untyped conversion collapses — the ill-typed
     case (in (0, unit)) of { 0 ⇒ t ; 0 ⇒ u } would reduce to both t and
     u, and cv_sym/cv_trans would then equate arbitrary closed terms.  On
     Sig-case-typed matches the pairwise-distinct premise makes the first
     match THE unique match, as the sketch states.                           *)
| st_case : forall a xs Q bs k c b n,
    nth_error bs k = Some (c, b) ->
    enum_pos c n -> enum_pos a n ->
    (forall j cj bj, j < k -> nth_error bs j = Some (cj, bj) ->
        exists nj, enum_pos cj nj /\ nj <> n) ->
    step (TCase (TIn (TPair a xs)) Q bs) (subst xs 0 b)

(* --- weak-head congruences: only the positions a rule inspects (§1) ------- *)
| st_app1    : forall f f' a, step f f' -> step (TApp f a) (TApp f' a)
| st_fst1    : forall p p', step p p' -> step (TFst p) (TFst p')
| st_snd1    : forall p p', step p p' -> step (TSnd p) (TSnd p')
| st_epi1    : forall E E' P, step E E' -> step (TEPi E P) (TEPi E' P)
| st_switch1 : forall E E' P p e, step E E' -> step (TSwitch E P p e) (TSwitch E' P p e)
| st_switch3 : forall E P p p' e, step p p' -> step (TSwitch E P p e) (TSwitch E P p' e)
| st_switch4 : forall E P p e e', step e e' -> step (TSwitch E P p e) (TSwitch E P p e')
| st_interp1 : forall D D' X, step D D' -> step (TInterp D X) (TInterp D' X)
| st_iall1   : forall D D' X xs P, step D D' -> step (TIAll D X xs P) (TIAll D' X xs P)
| st_iall3   : forall D X xs xs' P, step xs xs' -> step (TIAll D X xs P) (TIAll D X xs' P)
| st_hyps1   : forall D D' X P h xs, step D D' -> step (THyps D X P h xs) (THyps D' X P h xs)
| st_hyps5   : forall D X P h xs xs', step xs xs' -> step (THyps D X P h xs) (THyps D X P h xs')
| st_ind5    : forall R P stp i x x', step x x' -> step (TInd R P stp i x) (TInd R P stp i x')
| st_case1   : forall M M' Q bs, step M M' -> step (TCase M Q bs) (TCase M' Q bs)
(* clause labels evaluate in place so the reduct can compare positions *)
| st_case_lbl : forall M Q bs1 c c' b bs2, step c c' ->
    step (TCase M Q (bs1 ++ (c, b) :: bs2)) (TCase M Q (bs1 ++ (c', b) :: bs2))
(* case selection reads positions arbitrarily deep (enum_pos), so 1+ must
   evaluate its argument — without this a well-typed tag such as
   1+ ((λ_. 0) unit) is stuck forever and a well-typed case on it refutes
   progress.  A canonical position's argument is canonical, so canonical
   positions stay step-normal and first-match selection stays stable. *)
| st_esucc1  : forall n n', step n n' -> step (TESucc n) (TESucc n')
(* `in` itself does not reduce (§1); its argument, and pair components, may *)
| st_in1     : forall x x', step x x' -> step (TIn x) (TIn x')
| st_pair1   : forall a a' b, step a a' -> step (TPair a b) (TPair a' b)
| st_pair2   : forall a b b', step b b' -> step (TPair a b) (TPair a b').

(* t ⇓ v — reduction to the form a side condition inspects (§7 writes        *)
(* `labels (S i) ⇓ Φ` for weak-head evaluation of the enabled list).          *)
Inductive eval : term -> term -> Prop :=
| ev_refl : forall t, eval t t
| ev_step : forall t u v, step t u -> eval u v -> eval t v.

(* ========================================================================== *)
(*  4. The φ layer — the subtyping paper's optional φ-normalization data      *)
(*     supplies the typed signature-subtyping rule below.                     *)
(*                                                                            *)
(*     Paper (Rules section):                                                 *)
(*       Φok := OK(Γ,T,Δ*,Φ) ≡ [ C ∈ Φ | C ∈ C_all ∧                          *)
(*                Γ ⊢ C : Δ_C → T Δ'_C* ∧ ∀j. AGAINST(Δ*_j, Δ'_C_j) ]         *)
(*                                                                            *)
(*       AGAINST(p,t) ≡  ⊤                  if p is a variable                *)
(*                       ∧ᵢ AGAINST(pᵢ,tᵢ)  if p = c p₁…pₖ, t = c t₁…tₖ       *)
(*                       ⊥                  if p = c p⃗, t = c' t⃗, c ≠ c'      *)
(*                       ⊤                  otherwise                         *)
(*                                                                            *)
(*     In the EID rendition the result-index discipline lives inside the      *)
(*     instantiated payload description `branches (S i) c`, so the AGAINST    *)
(*     analog is a conservative, POSITIVELY-derived emptiness judgment on     *)
(*     evaluated description spines.  The head-constructor clash (⊥ case)     *)
(*     becomes a choice over an enumeration spine that evaluates to nilE;     *)
(*     the ⊤ cases are the absent derivations.  Per §7's caveat, failure to   *)
(*     normalize an index or signature never proves impossibility: a stuck    *)
(*     description simply admits no desc_against derivation.                  *)
(* ========================================================================== *)

(* Neutral (stuck) terms, as far as the side conditions must recognize them. *)
Inductive neutral : term -> Prop :=
| ne_var    : forall n, neutral (TVar n)
| ne_app    : forall f a, neutral f -> neutral (TApp f a)
| ne_fst    : forall p, neutral p -> neutral (TFst p)
| ne_snd    : forall p, neutral p -> neutral (TSnd p)
| ne_switch : forall E P p e, neutral e -> neutral (TSwitch E P p e)
| ne_ind    : forall R P stp i x, neutral x -> neutral (TInd R P stp i x)
| ne_case   : forall M Q bs, neutral M -> neutral (TCase M Q bs).

(* The AGAINST analog: this description's interpretation is demonstrably     *)
(* uninhabited (under any carrier).  Conservative: 'var, '1, 'Π, and 'Σ       *)
(* never prune — the paper's ⊤ 'otherwise' clause.                            *)
Inductive desc_against : term -> Prop :=
(* ⊥ case: a choice over the empty enumeration *)
| ag_choice_nil : forall D E T,
    eval D (TIChoice E T) -> eval E TNilE -> desc_against D
(* ∧ case, product: dead on either side *)
| ag_prod_left : forall D A B,
    eval D (TIProd A B) -> desc_against A -> desc_against D
| ag_prod_right : forall D A B,
    eval D (TIProd A B) -> desc_against B -> desc_against D
(* ∧ case, choice: every branch of an exposed enumeration is dead *)
| ag_choice_cons : forall D E T tg E',
    eval D (TIChoice E T) -> eval E (TConsE tg E') ->
    desc_against (TApp T TEZero) ->
    desc_against (TIChoice E' (TLam (TApp (lift 1 0 T) (TESucc (TVar 0))))) ->
    desc_against D.

(*   Φok = OK(Γ,T,Δ*,Φ)
     ────────────────────────────────────────  Normφ                 [paper]
     {T Δ* :: Φ} →φ {T Δ* :: Φok}
   Here the signature is a pair and the type is μˢ S i, so the rewrite       *)
(* reading acts on the evaluated enabled spine: Φ ↝φ Ψ drops SOME labels     *)
(* whose payload at this instance is demonstrably dead and keeps the rest    *)
(* ('repeatedly apply Normφ', so pruning is per-label and need not be        *)
(* exhaustive).  Pruning may stop at any evaluated tail; in particular a     *)
(* neutral tail must be retained because it supplies no negative evidence.   *)
Inductive spine_phi (Sf i : term) : term -> term -> Prop :=
| sph_nil : forall Phi A,
    eval Phi (TLNil A) -> spine_phi Sf i Phi (TLNil A)
| sph_keep : forall Phi A c Phi' Psi',
    eval Phi (TLCons A c Phi') -> spine_phi Sf i Phi' Psi' ->
    spine_phi Sf i Phi (TLCons A c Psi')
| sph_drop : forall Phi A c Phi' Psi',
    eval Phi (TLCons A c Phi') ->
    desc_against (TApp (branches (TApp Sf i)) c) ->
    spine_phi Sf i Phi' Psi' ->
    spine_phi Sf i Phi Psi'
| sph_tail : forall Phi,
    spine_phi Sf i Phi Phi.

(* ========================================================================== *)
(*  5. Conversion — §1: alpha (de Bruijn), beta and eta for functions,        *)
(*     projection computation for pairs, and the computation rules above,     *)
(*     closed under congruence.  We take the paper's option without Eqφ in    *)
(*     general definitional equality.  Refinement pruning remains available   *)
(*     through the typed [su_sig] rule below.  Keeping Eqφ inside this untyped *)
(*     congruence would allow it under arbitrary beta/eta contexts and would   *)
(*     require a substantially stronger conversion-modulo metatheory than the *)
(*     syntax-directed signature rule needs.                                  *)
(* ========================================================================== *)

Inductive conv : term -> term -> Prop :=
| cv_step  : forall t u, step t u -> conv t u
| cv_refl  : forall t, conv t t
| cv_sym   : forall t u, conv t u -> conv u t
| cv_trans : forall t u v, conv t u -> conv u v -> conv t v

(* λx. f x ≡ f                                            [eta; §1] *)
| cv_eta : forall f, conv (TLam (TApp (lift 1 0 f) (TVar 0))) f

(* --- congruence, one former at a time ('Conversion is a congruence', §1) -- *)
| cv_pi     : forall A A' B B', conv A A' -> conv B B' -> conv (TPi A B) (TPi A' B')
| cv_lam    : forall b b', conv b b' -> conv (TLam b) (TLam b')
| cv_app    : forall f f' a a', conv f f' -> conv a a' -> conv (TApp f a) (TApp f' a')
| cv_sigma  : forall A A' B B', conv A A' -> conv B B' -> conv (TSigma A B) (TSigma A' B')
| cv_pair   : forall a a' b b', conv a a' -> conv b b' -> conv (TPair a b) (TPair a' b')
| cv_fst    : forall p p', conv p p' -> conv (TFst p) (TFst p')
| cv_snd    : forall p p', conv p p' -> conv (TSnd p) (TSnd p')
| cv_conse  : forall t t' E E', conv t t' -> conv E E' -> conv (TConsE t E) (TConsE t' E')
| cv_enumt  : forall E E', conv E E' -> conv (TEnumT E) (TEnumT E')
| cv_esucc  : forall n n', conv n n' -> conv (TESucc n) (TESucc n')
| cv_epi    : forall E E' P P', conv E E' -> conv P P' -> conv (TEPi E P) (TEPi E' P')
| cv_switch : forall E E' P P' p p' e e',
    conv E E' -> conv P P' -> conv p p' -> conv e e' ->
    conv (TSwitch E P p e) (TSwitch E' P' p' e')
| cv_idesc  : forall IT IT', conv IT IT' -> conv (TIDesc IT) (TIDesc IT')
| cv_ivar   : forall i i', conv i i' -> conv (TIVar i) (TIVar i')
| cv_iprod  : forall A A' B B', conv A A' -> conv B B' -> conv (TIProd A B) (TIProd A' B')
| cv_ipi    : forall Sd Sd' T T', conv Sd Sd' -> conv T T' -> conv (TIPi Sd T) (TIPi Sd' T')
| cv_isig   : forall Sd Sd' T T', conv Sd Sd' -> conv T T' -> conv (TISig Sd T) (TISig Sd' T')
| cv_ichoice: forall E E' T T', conv E E' -> conv T T' -> conv (TIChoice E T) (TIChoice E' T')
| cv_interp : forall D D' X X', conv D D' -> conv X X' -> conv (TInterp D X) (TInterp D' X')
| cv_mui    : forall R R', conv R R' -> conv (TMuI R) (TMuI R')
| cv_mus    : forall Sf Sf', conv Sf Sf' -> conv (TMuS Sf) (TMuS Sf')
| cv_in     : forall x x', conv x x' -> conv (TIn x) (TIn x')
| cv_ind    : forall R R' P P' stp stp' i i' x x',
    conv R R' -> conv P P' -> conv stp stp' -> conv i i' -> conv x x' ->
    conv (TInd R P stp i x) (TInd R' P' stp' i' x')
| cv_iall   : forall D D' X X' xs xs' P P',
    conv D D' -> conv X X' -> conv xs xs' -> conv P P' ->
    conv (TIAll D X xs P) (TIAll D' X' xs' P')
| cv_hyps   : forall D D' X X' P P' h h' xs xs',
    conv D D' -> conv X X' -> conv P P' -> conv h h' -> conv xs xs' ->
    conv (THyps D X P h xs) (THyps D' X' P' h' xs')
| cv_list   : forall A A', conv A A' -> conv (TList A) (TList A')
| cv_lnil   : forall A A', conv A A' -> conv (TLNil A) (TLNil A')
| cv_lcons  : forall A A' a a' l l',
    conv A A' -> conv a a' -> conv l l' -> conv (TLCons A a l) (TLCons A' a' l')
| cv_case   : forall M M' Q Q' bs, conv M M' -> conv Q Q' ->
    conv (TCase M Q bs) (TCase M' Q' bs)
| cv_case_br : forall M Q bs1 c c' b b' bs2, conv c c' -> conv b b' ->
    conv (TCase M Q (bs1 ++ (c, b) :: bs2)) (TCase M Q (bs1 ++ (c', b') :: bs2)).

(* ========================================================================== *)
(*  6. The §7 side conditions on evaluated label spines — the papers' meta    *)
(*     conditions C ∈ Φ and Φ' ⊆ Φ, adapted only by evaluating the            *)
(*     first-class list.  These are META-LEVEL relations: the core never      *)
(*     mentions the library Member/Subset/Disjoint types (§6).  A condition   *)
(*     that cannot be established is stuck — the rule simply does not apply,  *)
(*     and stuckness is never read as a negative fact (§7).                   *)
(* ========================================================================== *)

(* c ∈ Φ — 'the syntactic search that finds an exposed element convertible   *)
(* to c' (§7), evaluating the list only as far as the search needs.           *)
Inductive spine_mem (c : term) : term -> Prop :=
| sm_here  : forall Phi A c' Phi',
    eval Phi (TLCons A c' Phi') -> conv c c' -> spine_mem c Phi
| sm_there : forall Phi A c' Phi',
    eval Phi (TLCons A c' Phi') -> spine_mem c Phi' -> spine_mem c Phi.

(* A retained open tail may be preceded by additional list cells (§7).       *)
Inductive spine_tail (Phi : term) : term -> Prop :=
| stl_here  : forall Psi, eval Psi Phi -> spine_tail Phi Psi
| stl_there : forall Psi A c Psi',
    eval Psi (TLCons A c Psi') -> spine_tail Phi Psi' -> spine_tail Phi Psi.

(* Φ₁ ⊆ Φ₂ — every exposed element of Φ₁ occurs, up to conversion, in Φ₂.
   [spine_tail Phi Psi] says that [Psi] is obtained by prefixing zero or more
   cells to [Phi]; its base case is directed evaluation back to [Phi].  This
   formulation is stable under substitution and cannot identify a list tail
   with an unrelated eta expansion. *)
Inductive spine_incl : term -> term -> Prop :=
| si_nil     : forall Phi Psi A, eval Phi (TLNil A) -> spine_incl Phi Psi
| si_cons    : forall Phi A c Phi' Psi,
    eval Phi (TLCons A c Phi') -> spine_mem c Psi -> spine_incl Phi' Psi ->
    spine_incl Phi Psi
| si_tail : forall Phi Psi,
    spine_tail Phi Psi -> spine_incl Phi Psi.

(* Sig-case coverage Φ ⊆ Ψ against the clause-label list.  There is no       *)
(* neutral case: 'a stuck coverage check rejects the match with a            *)
(* diagnostic — the checker never guesses a set' (§7).                       *)
Inductive covers (Psi : list term) : term -> Prop :=
| cov_nil  : forall Phi A, eval Phi (TLNil A) -> covers Psi Phi
| cov_cons : forall Phi A c Phi',
    eval Phi (TLCons A c Phi') ->
    Exists (fun c' => conv c c') Psi ->
    covers Psi Phi' -> covers Psi Phi.

(* The elaborated branch labels are canonical ambient positions.  Recording
   that fact here is load-bearing for substitution: raw [~ conv c c'] is not
   stable when an open label is instantiated (for example, ['0; 0] can arise
   from ['x; 0]).  Canonical positions contain no variables, are unchanged by
   lifting/substitution, and their conversion disequality is therefore stable. *)
Inductive distinct : list term -> Prop :=
| dt_nil  : distinct []
| dt_cons : forall c cs n,
    enum_pos c n ->
    Forall (fun c' => ~ conv c c') cs ->
    distinct cs -> distinct (c :: cs).

(* ========================================================================== *)
(*  7. Typing — Γ ⊢ t ⇒ A (synth), Γ ⊢ t ⇐ A (check), Γ ⊢ A ⊑ B (sub).       *)
(*     'Everything else — labels, membership, subset, disjointness,          *)
(*     coverage — is ordinary typing of ordinary terms; no further judgment   *)
(*     forms are introduced.' (§1)                                            *)
(* ========================================================================== *)

Definition ctx := list term.

Inductive wf : ctx -> Prop :=
(* ───────────  (empty context valid) *)
| wf_nil : wf []
(* Γ valid    Γ ⊢ A ⇐ Setₖ
   ─────────────────────── *)
| wf_cons : forall Γ A k, wf Γ -> check Γ A (TSort k) -> wf (A :: Γ)

with synth : ctx -> term -> term -> Prop :=

(* Γ valid    (x : A) ∈ Γ
   ───────────────────────  Var        [EID Fig. 1 background] *)
| sy_var : forall Γ n A,
    wf Γ -> nth_error Γ n = Some A -> synth Γ (TVar n) (lift (S n) 0 A)

(* Γ valid
   ─────────────────────  Sort — predicative; * = Set₀, Type = Set₁ (§1) *)
| sy_sort : forall Γ k, wf Γ -> synth Γ (TSort k) (TSort (S k))

(* Γ ⊢ A : Setₖ    Γ, x:A ⊢ B : Setₖ
   ─────────────────────────────────  Pi-form
   Γ ⊢ (x:A) → B : Setₖ         ['functions exist at every Setₖ', §1] *)
| sy_pi : forall Γ A B k,
    check Γ A (TSort k) -> check (A :: Γ) B (TSort k) ->
    synth Γ (TPi A B) (TSort k)

(* Γ ⊢ A : Setₖ    Γ, x:A ⊢ B : Setₖ
   ─────────────────────────────────  Sigma-form
   Γ ⊢ (x:A) × B : Setₖ         ['pairs exist at every Setₖ', §1; with
   cumulativity (su_sort) 'Set₁ pairs may store Set₀ components'] *)
| sy_sigma : forall Γ A B k,
    check Γ A (TSort k) -> check (A :: Γ) B (TSort k) ->
    synth Γ (TSigma A B) (TSort k)

(* Γ ⊢ f ⇒ (x:A) → B    Γ ⊢ a ⇐ A
   ───────────────────────────────  App        [EID Fig. 1 background] *)
| sy_app : forall Γ f a C A B k,
    check Γ (TPi A B) (TSort k) ->
    synth Γ f C -> eval C (TPi A B) -> check Γ a A ->
    synth Γ (TApp f a) (subst a 0 B)

(* Γ ⊢ p ⇒ (x:A) × B
   ──────────────────  Fst        ['projection computation for pairs', Fig. 1b] *)
| sy_fst : forall Γ p C A B k,
    check Γ (TSigma A B) (TSort k) ->
    synth Γ p C -> eval C (TSigma A B) -> synth Γ (TFst p) A

(* Γ ⊢ p ⇒ (x:A) × B
   ─────────────────────────  Snd *)
| sy_snd : forall Γ p C A B k,
    check Γ (TSigma A B) (TSort k) ->
    synth Γ p C -> eval C (TSigma A B) ->
    synth Γ (TSnd p) (subst (TFst p) 0 B)

(* Γ valid
   ──────────────  Unit-form — at every Setₖ (πₖ nilE P ↦ 1 forces it, §2) *)
| sy_unitT : forall Γ k, wf Γ -> synth Γ TUnitT (TSort k)

(* Γ valid
   ──────────────  unit *)
| sy_unit : forall Γ, wf Γ -> synth Γ TUnit TUnitT

(* Γ valid
   ────────────────  UId-form                                     (§2) *)
| sy_uid : forall Γ, wf Γ -> synth Γ TUId (TSort 0)

(* Γ valid
   ────────────────  EnumU-form                                   (§2) *)
| sy_enumu : forall Γ, wf Γ -> synth Γ TEnumU (TSort 0)

(* Γ valid    s is a valid identifier
   ──────────────────────────────────  tag                        (§2) *)
| sy_tag : forall Γ s, wf Γ -> synth Γ (TTag s) TUId

(* Γ valid
   ────────────────  nilE                                         (§2) *)
| sy_nile : forall Γ, wf Γ -> synth Γ TNilE TEnumU

(* Γ ⊢ t : UId    Γ ⊢ E : EnumU
   ─────────────────────────────  consE                           (§2) *)
| sy_conse : forall Γ tg E,
    check Γ tg TUId -> check Γ E TEnumU -> synth Γ (TConsE tg E) TEnumU

(* Γ ⊢ E : EnumU
   ──────────────────  EnumT-form                                 (§2) *)
| sy_enumt : forall Γ E, check Γ E TEnumU -> synth Γ (TEnumT E) (TSort 0)

(* πₖ : (E : EnumU) → (EnumT E → Setₖ) → Setₖ                     (§2) *)
| sy_epi : forall Γ E P k,
    check Γ E TEnumU -> check Γ P (TPi (TEnumT E) (TSort k)) ->
    synth Γ (TEPi E P) (TSort k)

(* switchₖ : (E : EnumU) → (P : EnumT E → Setₖ)
           → πₖ E P → (e : EnumT E) → P e                         (§2) *)
| sy_switch : forall Γ E P p e k,
    check Γ E TEnumU -> check Γ P (TPi (TEnumT E) (TSort k)) ->
    check Γ p (TEPi E P) -> check Γ e (TEnumT E) ->
    synth Γ (TSwitch E P p e) (TApp P e)

(* Γ ⊢ I : Set₀
   ────────────────────  IDesc-form                               (§1) *)
| sy_idesc : forall Γ IT, check Γ IT (TSort 0) -> synth Γ (TIDesc IT) (TSort 1)

(* Here X : I → Set₀ and ⟦D⟧ X : Set₀                             (§4) *)
| sy_interp : forall Γ D X IT,
    check Γ IT (TSort 0) -> check Γ D (TIDesc IT) ->
    check Γ X (TPi IT (TSort 0)) ->
    synth Γ (TInterp D X) (TSort 0)

(* Γ ⊢ R : I → IDesc I
   ───────────────────────  MuI-form                    [EID Fig. 4; §5] *)
| sy_mui : forall Γ R IT,
    check Γ IT (TSort 0) -> check Γ R (TPi IT (TIDesc (lift 1 0 IT))) ->
    synth Γ (TMuI R) (TPi IT (TSort 0))

(* iAll : (D : IDesc I) → (X : I → Set₀) →
          ⟦D⟧ X → ((Σ i:I. X i) → Set₀) → Set₀                    (§5) *)
| sy_iall : forall Γ D X xs P IT,
    check Γ IT (TSort 0) -> check Γ D (TIDesc IT) ->
    check Γ X (TPi IT (TSort 0)) ->
    check Γ xs (TInterp D X) ->
    check Γ P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
    synth Γ (TIAll D X xs P) (TSort 0)

(* hyps : (D : IDesc I) → (X : I → Set₀) →
          (P : (Σ i:I. X i) → Set₀) →
          ((i:I) → (x : X i) → P (i,x)) →
          (xs : ⟦D⟧ X) → iAll D X xs P                            (§5) *)
| sy_hyps : forall Γ D X P h xs IT,
    check Γ IT (TSort 0) -> check Γ D (TIDesc IT) ->
    check Γ X (TPi IT (TSort 0)) ->
    check Γ P (TPi (TSigma IT (TApp (lift 1 0 X) (TVar 0))) (TSort 0)) ->
    check Γ h (TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
                           (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0))))) ->
    check Γ xs (TInterp D X) ->
    synth Γ (THyps D X P h xs) (TIAll D X xs P)

(* iinduction :
     (R : I → IDesc I) →
     (P : (Σ i:I. μᴵ R i) → Set₀) →
     ((i:I) → (xs : ⟦R i⟧ (μᴵ R)) →
        iAll (R i) (μᴵ R) xs P → P (i, in xs)) →
     (i:I) → (x : μᴵ R i) → P (i,x)                               (§5) *)
| sy_ind : forall Γ R P stp i x IT,
    check Γ IT (TSort 0) ->
    check Γ R (TPi IT (TIDesc (lift 1 0 IT))) ->
    check Γ P (TPi (TSigma IT (TApp (TMuI (lift 1 0 R)) (TVar 0))) (TSort 0)) ->
    check Γ stp
      (TPi IT
        (TPi (TInterp (TApp (lift 1 0 R) (TVar 0)) (TMuI (lift 1 0 R)))
          (TPi (TIAll (TApp (lift 2 0 R) (TVar 1)) (TMuI (lift 2 0 R))
                      (TVar 0) (lift 2 0 P))
            (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1))))))) ->
    check Γ i IT ->
    check Γ x (TApp (TMuI R) i) ->
    synth Γ (TInd R P stp i x) (TApp P (TPair i x))

(* Γ ⊢ I : Set₀    Γ ⊢ E : EnumU    Γ ⊢ S : (i:I) → Sig I E
   ─────────────────────────────────────────────────────────  Sig-mu
   Γ ⊢ μˢ S : I → Set₀                       [BRIDGE; SUB Rule 1; §7] *)
| sy_mus : forall Γ Sf IT E,
    check Γ IT (TSort 0) -> check Γ E TEnumU ->
    check Γ Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    synth Γ (SigMu E Sf) (TPi IT (TSort 0))

(* Γ ⊢ M : μˢ S i    Γ ⊢ Q : Setₖ
   Ψ = (c₁, …, cₘ)    Γ ⊢ cₖ : Label E    the cₖ pairwise distinct
   labels (S i) ⇓ Φ      Φ ⊆ Ψ
   for each k,
     Γ, xs : ⟦branches (S i) cₖ⟧ (Carrier S) ⊢ Nₖ : Q
   ────────────────────────────────────────────────────────  Sig-case
   Γ ⊢ case M of Q { cₖ xs ⇒ Nₖ } : Q        [BRIDGE; SUB Rule 7; §7]
   (the paper's extra restriction Ψ ⊆ Φ is kept as a diagnostic only) *)
| sy_case : forall Γ M Q bs Sf i IT E k Phi,
    check Γ M (TApp (SigMu E Sf) i) ->
    check Γ IT (TSort 0) -> check Γ E TEnumU ->
    check Γ Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check Γ i IT ->
    check Γ Q (TSort k) ->
    distinct (map fst bs) ->
    eval (labels (TApp Sf i)) Phi ->
    covers (map fst bs) Phi ->
    check_branches Γ Sf i E Q bs ->
    synth Γ (TCase M Q bs) Q

(* List — library stand-ins (see header); ordinary Set₀ data (§1) *)
| sy_list : forall Γ A, check Γ A (TSort 0) -> synth Γ (TList A) (TSort 0)
| sy_lnil : forall Γ A, check Γ A (TSort 0) -> synth Γ (TLNil A) (TList A)
| sy_lcons : forall Γ A a l,
    check Γ A (TSort 0) -> check Γ a A -> check Γ l (TList A) ->
    synth Γ (TLCons A a l) (TList A)

with check : ctx -> term -> term -> Prop :=

(* Γ ⊢ t ⇒ A    Γ ⊢ A ≡ B : Setₖ
   ──────────────────────────────  Conv                           (§1)
   Here [conv] is βη definitional equality.  Typed signature pruning is
   expressed by [su_sig]. *)
| ch_conv : forall Γ t A B, synth Γ t A -> conv A B -> check Γ t B

(* Γ ⊢ t ⇐ A    Γ ⊢ A ⊑ B
   ────────────────────────  Declarative subsumption        [SUB] (§1)
   The premise is checking, rather than synthesis, because weak-head
   computation may expose a checked-only introduction (a lambda, pair, or
   [in]).  This is the ordinary declarative closure and makes subsumption
   commute structurally with reduction and substitution. *)
| ch_sub : forall Γ t A B, check Γ t A -> sub Γ A B -> check Γ t B

(* the expected type may be normalized as far as a rule needs (§1) *)
| ch_expand : forall Γ t A B, conv A B -> check Γ t B -> check Γ t A

(* Γ, x:A ⊢ b ⇐ B
   ─────────────────────  Lam            [EID Fig. 1 background] *)
| ch_lam : forall Γ b A B, check (A :: Γ) b B -> check Γ (TLam b) (TPi A B)

(* Γ ⊢ a ⇐ A    Γ ⊢ b ⇐ B[a/x]
   ─────────────────────────────  Pair    [EID Fig. 1 background] *)
| ch_pair : forall Γ a b A B,
    check Γ a A -> check Γ b (subst a 0 B) -> check Γ (TPair a b) (TSigma A B)

(* Declarative completion.  Computation creates eliminations of checked-only
   canonical forms — the πₖ reduct applies the raw λ motive (P 0 × …), case
   scrutinizes a literal `in` — which no synthesis rule covers, so a purely
   synthesizing elimination refutes subject reduction (kernel-checked
   counterexample: πₖ (consE 'c nilE) (λ_. 1) steps to a Σ whose domain
   (λ_. 1) 0 had no derivation).  These are EID Fig. 1's application and
   projection typings read declaratively: the eliminated type is chosen
   existentially, with its formation premise explicit.
   Γ ⊢ (x:A) → B : Setₖ    Γ ⊢ f ⇐ (x:A) → B    Γ ⊢ a ⇐ A
   ─────────────────────────────────────────────────────────  App-check
   Γ ⊢ f a ⇐ B[a/x] *)
| ch_app : forall Γ f a A B k,
    check Γ (TPi A B) (TSort k) ->
    check Γ f (TPi A B) ->
    check Γ a A ->
    check Γ (TApp f a) (subst a 0 B)

(* Γ ⊢ (x:A) × B : Setₖ    Γ ⊢ p ⇐ (x:A) × B
   ───────────────────────────────────────────  Fst-check
   Γ ⊢ π₀ p ⇐ A *)
| ch_fst : forall Γ p A B k,
    check Γ (TSigma A B) (TSort k) ->
    check Γ p (TSigma A B) ->
    check Γ (TFst p) A

(* Γ ⊢ (x:A) × B : Setₖ    Γ ⊢ p ⇐ (x:A) × B
   ───────────────────────────────────────────  Snd-check
   Γ ⊢ π₁ p ⇐ B[π₀ p/x] *)
| ch_snd : forall Γ p A B k,
    check Γ (TSigma A B) (TSort k) ->
    check Γ p (TSigma A B) ->
    check Γ (TSnd p) (subst (TFst p) 0 B)

(* Γ ⊢ t : UId    Γ ⊢ E : EnumU
   ────────────────────────────  0E                               (§2)
   Γ ⊢ 0 : EnumT (consE t E) *)
| ch_ezero : forall Γ tg E,
    check Γ tg TUId -> check Γ E TEnumU ->
    check Γ TEZero (TEnumT (TConsE tg E))

(* Γ ⊢ t : UId    Γ ⊢ n : EnumT E
   ────────────────────────────────  1+E                          (§2)
   Γ ⊢ 1+n : EnumT (consE t E) *)
| ch_esucc : forall Γ tg E n,
    check Γ tg TUId -> check Γ n (TEnumT E) ->
    check Γ (TESucc n) (TEnumT (TConsE tg E))

(* Γ ⊢ i : I
   ────────────────────────  IVar                                 (§4)
   Γ ⊢ 'var i ⇐ IDesc I *)
| ch_ivar : forall Γ i IT, check Γ i IT -> check Γ (TIVar i) (TIDesc IT)

(* ────────────────────────  I1                                   (§4)
   Γ ⊢ '1 ⇐ IDesc I *)
| ch_i1 : forall Γ IT, wf Γ -> check Γ TI1 (TIDesc IT)

(* Γ ⊢ A ⇐ IDesc I    Γ ⊢ B ⇐ IDesc I
   ────────────────────────────────────  IProduct                 (§4)
   Γ ⊢ A '× B ⇐ IDesc I *)
| ch_iprod : forall Γ A B IT,
    check Γ A (TIDesc IT) -> check Γ B (TIDesc IT) ->
    check Γ (TIProd A B) (TIDesc IT)

(* Γ ⊢ S : Set₀    Γ ⊢ T : S → IDesc I
   ────────────────────────────────────  IPi                      (§4)
   Γ ⊢ 'Π S T ⇐ IDesc I *)
| ch_ipi : forall Γ Sd T IT,
    check Γ Sd (TSort 0) -> check Γ T (TPi Sd (TIDesc (lift 1 0 IT))) ->
    check Γ (TIPi Sd T) (TIDesc IT)

(* Γ ⊢ S : Set₀    Γ ⊢ T : S → IDesc I
   ────────────────────────────────────  ISigma                   (§4)
   Γ ⊢ 'Σ S T ⇐ IDesc I *)
| ch_isig : forall Γ Sd T IT,
    check Γ Sd (TSort 0) -> check Γ T (TPi Sd (TIDesc (lift 1 0 IT))) ->
    check Γ (TISig Sd T) (TIDesc IT)

(* Γ ⊢ E : EnumU    Γ ⊢ T : EnumT E → IDesc I
   ──────────────────────────────────────────  IChoice            (§4)
   Γ ⊢ 'σ E T ⇐ IDesc I *)
| ch_ichoice : forall Γ E T IT,
    check Γ E TEnumU ->
    check Γ T (TPi (TEnumT E) (TIDesc (lift 1 0 IT))) ->
    check Γ (TIChoice E T) (TIDesc IT)

(* Γ ⊢ i : I    Γ ⊢ xs : ⟦R i⟧ (μᴵ R)
   ────────────────────────────────────  MuI-in       [EID Fig. 4; §5]
   Γ ⊢ in xs : μᴵ R i
   (the R and I formation premises are the sketch's 'suppressed
    well-formedness premises made explicit') *)
| ch_in_mui : forall Γ xs R i IT,
    check Γ IT (TSort 0) ->
    check Γ R (TPi IT (TIDesc (lift 1 0 IT))) ->
    check Γ i IT ->
    check Γ xs (TInterp (TApp R i) (TMuI R)) ->
    check Γ (TIn xs) (TApp (TMuI R) i)

(* Γ ⊢ i : I    Γ ⊢ c : Label E
   labels (S i) ⇓ Φ      c ∈ Φ
   Γ ⊢ xs : ⟦branches (S i) c⟧ (Carrier S)
   ─────────────────────────────────────────  Sig-in
   Γ ⊢ in (c, xs) : μˢ S i                   [BRIDGE; SUB Rule 3; §7]
   (nothing is stored in the term: the side condition is checked, not
    kept — the refinement is a phantom type) *)
| ch_in_sig : forall Γ c xs Sf i IT E Phi,
    check Γ IT (TSort 0) -> check Γ E TEnumU ->
    check Γ Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check Γ i IT ->
    check Γ c (Label E) ->
    eval (labels (TApp Sf i)) Phi ->
    spine_mem c Phi ->
    check Γ xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
    check Γ (TIn (TPair c xs)) (TApp (SigMu E Sf) i)

with check_branches : ctx -> term -> term -> term -> term -> list (term * term) -> Prop :=
(* the per-clause premises of Sig-case:
     Γ ⊢ cₖ : Label E
     Γ, xs : ⟦branches (S i) cₖ⟧ (Carrier S) ⊢ Nₖ : Q                (§7) *)
| cb_nil : forall Γ Sf i E Q, check_branches Γ Sf i E Q []
| cb_cons : forall Γ Sf i E Q c b bs,
    check Γ c (Label E) ->
    check (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf) :: Γ)
          b (lift 1 0 Q) ->
    check_branches Γ Sf i E Q bs ->
    check_branches Γ Sf i E Q ((c, b) :: bs)

with sub : ctx -> term -> term -> Prop :=

(* `⊑` contains `≡` …                                             (§1) *)
| su_conv : forall Γ A B, conv A B -> sub Γ A B

(* … and is transitive.                                           (§1) *)
| su_trans : forall Γ A B C, sub Γ A B -> sub Γ B C -> sub Γ A C

(* '(or cumulativity)' — the §1 option taken here so that Set₁ pairs
   may store Set₀ components *)
| su_sort : forall Γ j k, j <= k -> sub Γ (TSort j) (TSort k)

(* Γ ⊢ A' ⊑ A    Γ, x:A' ⊢ B ⊑ B'
   ───────────────────────────────────  Pi-sub        [SUB Rule 6; §7]
   Γ ⊢ (x:A) → B ⊑ (x:A') → B' *)
| su_pi : forall Γ A A' B B',
    sub Γ A' A -> sub (A' :: Γ) B B' -> sub Γ (TPi A B) (TPi A' B')

(* Γ ⊢ i : I
   ─────────────────────────  Sig-forget              [SUB Rule 2; §7]
   Γ ⊢ μˢ S i ⊑ Carrier S i
   (the S formation premise is the ambient data of the rule) *)
| su_forget : forall Γ Sf i IT E,
    check Γ IT (TSort 0) -> check Γ E TEnumU ->
    check Γ Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check Γ i IT ->
    sub Γ (TApp (SigMu E Sf) i) (TApp (Carrier E Sf) i)

(* Γ ⊢ (λ i. branches (S₁ i)) ≡ (λ i. branches (S₂ i))
         : (i:I) → EnumT E → IDesc I
   labels (S₁ i) ⇓ Φ₁    labels (S₂ i) ⇓ Φ₂    Φ₁ ⊆ Φ₂
   Γ ⊢ i : I
   ────────────────────────────────────────────────────  Sig-sub
   Γ ⊢ μˢ S₁ i ⊑ μˢ S₂ i                     [SUB Rule 4; §7]
   ('Shared branch descriptions are invariant: structural subtyping
    between different payloads … must not be obtained from label
    inclusion.') *)
| su_sig : forall Γ S1 S2 i IT E Phi1 Phi2,
    check Γ IT (TSort 0) -> check Γ E TEnumU ->
    check Γ S1 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check Γ S2 (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    conv (TLam (branches (TApp (lift 1 0 S1) (TVar 0))))
         (TLam (branches (TApp (lift 1 0 S2) (TVar 0)))) ->
    eval (labels (TApp S1 i)) Phi1 ->
    eval (labels (TApp S2 i)) Phi2 ->
    spine_incl Phi1 Phi2 ->
    check Γ i IT ->
    sub Γ (TApp (SigMu E S1) i) (TApp (SigMu E S2) i).

(* Semantic observations used by the metatheory. *)

(* Weak-head values: introduction and type formers.  Eliminators (App, π₀,   *)
(* π₁, πₖ, switchₖ, ⟦_⟧, iAll, hyps, iinduction, case) are not values; the    *)
(* applied fixed points μᴵ R i and μˢ S i are — 'keeping μᴵ/μˢ opaque except  *)
(* for their stated computation' (context.md, checker migration).             *)
Inductive value : term -> Prop :=
| v_sort   : forall k, value (TSort k)
| v_pi     : forall A B, value (TPi A B)
| v_lam    : forall b, value (TLam b)
| v_sigma  : forall A B, value (TSigma A B)
| v_pair   : forall a b, value (TPair a b)
| v_unitT  : value TUnitT
| v_unit   : value TUnit
| v_uid    : value TUId
| v_tag    : forall s, value (TTag s)
| v_enumu  : value TEnumU
| v_nile   : value TNilE
| v_conse  : forall tg E, value (TConsE tg E)
| v_enumt  : forall E, value (TEnumT E)
| v_ezero  : value TEZero
| v_esucc  : forall n, value (TESucc n)
| v_idesc  : forall IT, value (TIDesc IT)
| v_ivar   : forall i, value (TIVar i)
| v_i1     : value TI1
| v_iprod  : forall A B, value (TIProd A B)
| v_ipi    : forall Sd T, value (TIPi Sd T)
| v_isig   : forall Sd T, value (TISig Sd T)
| v_ichoice: forall E T, value (TIChoice E T)
| v_mui    : forall R, value (TMuI R)
| v_mus    : forall Sf, value (TMuS Sf)
| v_mui_app: forall R i, value (TApp (TMuI R) i)
| v_mus_app: forall Sf i, value (TApp (TMuS Sf) i)
| v_in     : forall x, value (TIn x)
| v_list   : forall A, value (TList A)
| v_lnil   : forall A, value (TLNil A)
| v_lcons  : forall A a l, value (TLCons A a l).

(* The polymorphic empty type. *)
Definition Bot : term := TPi (TSort 0) (TVar 0).
