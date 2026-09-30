From Stdlib Require Import List Arith Bool Lia String.
Require Export FullReductionStructureWork.

Definition term_eq_dec : forall t u : term, {t = u} + {t <> u}.
Proof. decide equality; apply String.string_dec || apply Nat.eq_dec. Defined.

Definition eta_contract t : option term :=
  match t with
  | TLam (TApp f (TVar 0)) =>
    let g := subst (TVar 0) 0 f in
    if term_eq_dec f (lift 1 0 g) then Some g else None
  | _ => None
  end.
Lemma eta_contract_sound : forall t u, eta_contract t = Some u -> reduction t u.
Proof.
  destruct t; intros u H; cbn [eta_contract] in H; try discriminate.
  destruct t; cbn [eta_contract] in H; try discriminate.
  destruct t2; cbn [eta_contract] in H; try discriminate.
  destruct n; cbn [eta_contract] in H; try discriminate.
  destruct (term_eq_dec t1 (lift 1 0 (subst (TVar 0) 0 t1))) as [HE|HE];
    [|discriminate].
  inversion H; subst u. rewrite HE at 1. apply red_eta.
Qed.
Lemma eta_contract_eta : forall f,
  eta_contract (TLam (TApp (lift 1 0 f) (TVar 0))) = Some f.
Proof.
  intros f; cbn [eta_contract]; rewrite subst_lift_zero.
  destruct (term_eq_dec (lift 1 0 f) (lift 1 0 f)); [reflexivity|contradiction].
Qed.
Definition head_next t :=
  match root_step t with Some u => Some u | None => eta_contract t end.
Lemma head_next_sound : forall t u, head_next t = Some u -> reduction t u.
Proof.
  intros t u H; unfold head_next in H; destruct (root_step t) eqn:HR.
  - inversion H; subst; now apply red_root.
  - now apply eta_contract_sound.
Qed.
Lemma head_next_no_root : forall t, head_next t = None -> root_step t = None.
Proof.
  intros t H; unfold head_next in H; destruct (root_step t); congruence.
Qed.
Lemma head_next_eta : forall f,
  head_next (TLam (TApp (lift 1 0 f) (TVar 0))) = Some f.
Proof. intros f; unfold head_next; cbn [root_step]; apply eta_contract_eta. Qed.

Fixpoint full_next (t : term) : option term :=
  match head_next t with
  | Some u => Some u
  | None => match t with
    | TVar n => None
    | TSort k => None
    | TPi A B => match full_next A with Some A' => Some (TPi A' B) | None => match full_next B with Some B' => Some (TPi A B') | None => None end end
    | TLam b => match full_next b with Some b' => Some (TLam b') | None => None end
    | TApp f a => match full_next f with Some f' => Some (TApp f' a) | None => match full_next a with Some a' => Some (TApp f a') | None => None end end
    | TSigma A B => match full_next A with Some A' => Some (TSigma A' B) | None => match full_next B with Some B' => Some (TSigma A B') | None => None end end
    | TPair a b => match full_next a with Some a' => Some (TPair a' b) | None => match full_next b with Some b' => Some (TPair a b') | None => None end end
    | TFst p => match full_next p with Some p' => Some (TFst p') | None => None end
    | TSnd p => match full_next p with Some p' => Some (TSnd p') | None => None end
    | TUnitT => None
    | TUnit => None
    | TUId => None
    | TTag s => None
    | TEnumU => None
    | TNilE => None
    | TConsE tag E => match full_next tag with Some tag' => Some (TConsE tag' E) | None => match full_next E with Some E' => Some (TConsE tag E') | None => None end end
    | TEnumT E => match full_next E with Some E' => Some (TEnumT E') | None => None end
    | TEZero => None
    | TESucc n => match full_next n with Some n' => Some (TESucc n') | None => None end
    | TEPi k E P => match full_next E with Some E' => Some (TEPi k E' P) | None => match full_next P with Some P' => Some (TEPi k E P') | None => None end end
    | TSwitch k E P p e => match full_next E with Some E' => Some (TSwitch k E' P p e) | None => match full_next P with Some P' => Some (TSwitch k E P' p e) | None => match full_next p with Some p' => Some (TSwitch k E P p' e) | None => match full_next e with Some e' => Some (TSwitch k E P p e') | None => None end end end end
    | TIDesc IT => match full_next IT with Some IT' => Some (TIDesc IT') | None => None end
    | TIVar i => match full_next i with Some i' => Some (TIVar i') | None => None end
    | TI1 => None
    | TIBot => None
    | TIProd A B => match full_next A with Some A' => Some (TIProd A' B) | None => match full_next B with Some B' => Some (TIProd A B') | None => None end end
    | TIPi A D => match full_next A with Some A' => Some (TIPi A' D) | None => match full_next D with Some D' => Some (TIPi A D') | None => None end end
    | TISig A D => match full_next A with Some A' => Some (TISig A' D) | None => match full_next D with Some D' => Some (TISig A D') | None => None end end
    | TIChoice E D => match full_next E with Some E' => Some (TIChoice E' D) | None => match full_next D with Some D' => Some (TIChoice E D') | None => None end end
    | TInterp IT D X => match full_next IT with Some IT' => Some (TInterp IT' D X) | None => match full_next D with Some D' => Some (TInterp IT D' X) | None => match full_next X with Some X' => Some (TInterp IT D X') | None => None end end end
    | TMuI IT D => match full_next IT with Some IT' => Some (TMuI IT' D) | None => match full_next D with Some D' => Some (TMuI IT D') | None => None end end
    | TIn x => match full_next x with Some x' => Some (TIn x') | None => None end
    | TInd IT D P s i x => match full_next IT with Some IT' => Some (TInd IT' D P s i x) | None => match full_next D with Some D' => Some (TInd IT D' P s i x) | None => match full_next P with Some P' => Some (TInd IT D P' s i x) | None => match full_next s with Some s' => Some (TInd IT D P s' i x) | None => match full_next i with Some i' => Some (TInd IT D P s i' x) | None => match full_next x with Some x' => Some (TInd IT D P s i x') | None => None end end end end end end
    | TIAll IT D X x P => match full_next IT with Some IT' => Some (TIAll IT' D X x P) | None => match full_next D with Some D' => Some (TIAll IT D' X x P) | None => match full_next X with Some X' => Some (TIAll IT D X' x P) | None => match full_next x with Some x' => Some (TIAll IT D X x' P) | None => match full_next P with Some P' => Some (TIAll IT D X x P') | None => None end end end end end
    | THyps IT D X P h x => match full_next IT with Some IT' => Some (THyps IT' D X P h x) | None => match full_next D with Some D' => Some (THyps IT D' X P h x) | None => match full_next X with Some X' => Some (THyps IT D X' P h x) | None => match full_next P with Some P' => Some (THyps IT D X P' h x) | None => match full_next h with Some h' => Some (THyps IT D X P h' x) | None => match full_next x with Some x' => Some (THyps IT D X P h x') | None => None end end end end end end
    | TClose IT F G => match full_next IT with Some IT' => Some (TClose IT' F G) | None => match full_next F with Some F' => Some (TClose IT F' G) | None => match full_next G with Some G' => Some (TClose IT F G') | None => None end end end
    | TCloseCase k IT F G i Q b x => match full_next IT with Some IT' => Some (TCloseCase k IT' F G i Q b x) | None => match full_next F with Some F' => Some (TCloseCase k IT F' G i Q b x) | None => match full_next G with Some G' => Some (TCloseCase k IT F G' i Q b x) | None => match full_next i with Some i' => Some (TCloseCase k IT F G i' Q b x) | None => match full_next Q with Some Q' => Some (TCloseCase k IT F G i Q' b x) | None => match full_next b with Some b' => Some (TCloseCase k IT F G i Q b' x) | None => match full_next x with Some x' => Some (TCloseCase k IT F G i Q b x') | None => None end end end end end end end
    | TCloseInd IT G P s F i x => match full_next IT with Some IT' => Some (TCloseInd IT' G P s F i x) | None => match full_next G with Some G' => Some (TCloseInd IT G' P s F i x) | None => match full_next P with Some P' => Some (TCloseInd IT G P' s F i x) | None => match full_next s with Some s' => Some (TCloseInd IT G P s' F i x) | None => match full_next F with Some F' => Some (TCloseInd IT G P s F' i x) | None => match full_next i with Some i' => Some (TCloseInd IT G P s F i' x) | None => match full_next x with Some x' => Some (TCloseInd IT G P s F i x') | None => None end end end end end end end
    end
  end.

Lemma full_next_sound : forall t u, full_next t = Some u -> reduction t u.
Proof.
  induction t; intros u H; cbn [full_next] in H.
  all: match type of H with context [match head_next ?s with _ => _ end] =>
    destruct (head_next s) eqn:HR end.
  all: try solve [inversion H; subst; now apply head_next_sound].
  all: repeat match type of H with context [match full_next ?s with _ => _ end] =>
    destruct (full_next s) eqn:? end.
  all: try discriminate; inversion H; subst; solve [constructor; auto].
Qed.
Lemma full_next_complete : forall t,
  full_next t = None -> forall u, ~ reduction t u.
Proof.
  induction t; intros HN u Hu; cbn [full_next] in HN.
  all: match type of HN with context [match head_next ?s with _ => _ end] =>
    destruct (head_next s) eqn:HH; [discriminate|] end.
  all: repeat match type of HN with context [match full_next ?s with _ => _ end] =>
    destruct (full_next s) eqn:?; [discriminate|] end.
  all: pose proof (head_next_no_root _ HH) as Hroot.
  all: inversion Hu; subst; try congruence; try solve [eauto].
  all: try match type of HH with ?X => idtac X end.
  Show.
Abort.
