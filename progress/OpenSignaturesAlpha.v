(* Alpha comparison walks two terms directly, carrying their binder contexts.
   Corresponding bound IDs match; free IDs must be equal. No term keys or hashes
   are constructed. The Setoid registers alpha equivalence on the raw syntax. *)
From Stdlib Require Import List Arith String Bool Lia RelationClasses SetoidClass.
Require Export OpenSignaturesSyntax.
Import ListNotations.
Unset Implicit Arguments.

(* Contexts list enclosing binders, nearest first. Stop at the first match
   on either side: a bound occurrence cannot match a free or outer occurrence. *)
Fixpoint alpha_var (xs ys : list nat) (x y : nat) : bool :=
  match xs, ys with
  | [], [] => Nat.eqb x y
  | a :: xs, b :: ys =>
      match Nat.eqb x a, Nat.eqb y b with
      | true, true => true
      | false, false => alpha_var xs ys x y
      | _, _ => false
      end
  | _, _ => false
  end.

(* Pi/Sigma bind only their codomain. Every other constructor compares its
   ordinary fields in the current contexts. Different shapes never match. *)
Fixpoint alpha_eqb_in (xs ys : list nat) (t u : term) {struct t} : bool :=
  match t, u with
  | TVar x, TVar y => alpha_var xs ys x y
  | TSort k, TSort l => Nat.eqb k l
  | TTag s, TTag t => String.eqb s t
  | TPi x A B, TPi y A' B'
  | TSigma x A B, TSigma y A' B' =>
      alpha_eqb_in xs ys A A' && alpha_eqb_in (x :: xs) (y :: ys) B B'
  | TLam x b, TLam y b' => alpha_eqb_in (x :: xs) (y :: ys) b b'
  | TUnitT, TUnitT | TUnit, TUnit | TUId, TUId | TEnumU, TEnumU
  | TNilE, TNilE | TEZero, TEZero | TI1, TI1 | TIBot, TIBot => true
  | TFst a, TFst a' | TSnd a, TSnd a' | TEnumT a, TEnumT a'
  | TESucc a, TESucc a' | TIDesc a, TIDesc a' | TIVar a, TIVar a'
  | TIn a, TIn a' => alpha_eqb_in xs ys a a'
  | TApp a b, TApp a' b' | TPair a b, TPair a' b'
  | TConsE a b, TConsE a' b' | TIProd a b, TIProd a' b'
  | TIPi a b, TIPi a' b' | TISig a b, TISig a' b'
  | TIChoice a b, TIChoice a' b' | TMuI a b, TMuI a' b' =>
      alpha_eqb_in xs ys a a' && alpha_eqb_in xs ys b b'
  | TInterp a b c, TInterp a' b' c' | TClose a b c, TClose a' b' c' =>
      alpha_eqb_in xs ys a a' && alpha_eqb_in xs ys b b' && alpha_eqb_in xs ys c c'
  | TEPi k E P, TEPi l E' P' =>
      Nat.eqb k l && alpha_eqb_in xs ys E E' && alpha_eqb_in xs ys P P'
  | TSwitch k E P p e, TSwitch l E' P' p' e' =>
      Nat.eqb k l && alpha_eqb_in xs ys E E' && alpha_eqb_in xs ys P P' &&
      alpha_eqb_in xs ys p p' && alpha_eqb_in xs ys e e'
  | TIAll IT D X x P, TIAll IT' D' X' x' P' =>
      alpha_eqb_in xs ys IT IT' && alpha_eqb_in xs ys D D' &&
      alpha_eqb_in xs ys X X' && alpha_eqb_in xs ys x x' && alpha_eqb_in xs ys P P'
  | TInd a b c d e f, TInd a' b' c' d' e' f'
  | THyps a b c d e f, THyps a' b' c' d' e' f' =>
      alpha_eqb_in xs ys a a' && alpha_eqb_in xs ys b b' && alpha_eqb_in xs ys c c' &&
      alpha_eqb_in xs ys d d' && alpha_eqb_in xs ys e e' && alpha_eqb_in xs ys f f'
  | TCloseCase k IT F G i Q b x, TCloseCase l IT' F' G' i' Q' b' x' =>
      Nat.eqb k l && alpha_eqb_in xs ys IT IT' && alpha_eqb_in xs ys F F' &&
      alpha_eqb_in xs ys G G' && alpha_eqb_in xs ys i i' && alpha_eqb_in xs ys Q Q' &&
      alpha_eqb_in xs ys b b' && alpha_eqb_in xs ys x x'
  | TCloseInd IT G P s F i x, TCloseInd IT' G' P' s' F' i' x' =>
      alpha_eqb_in xs ys IT IT' && alpha_eqb_in xs ys G G' && alpha_eqb_in xs ys P P' &&
      alpha_eqb_in xs ys s s' && alpha_eqb_in xs ys F F' && alpha_eqb_in xs ys i i' &&
      alpha_eqb_in xs ys x x'
  | _, _ => false
  end.

Definition alpha_eqb := alpha_eqb_in [] [].
Definition alpha_equiv (t u : term) : Prop := alpha_eqb t u = true.

Lemma alpha_var_refl : forall env x, alpha_var env env x x = true.
Proof.
  induction env as [|a env IH]; intro x; cbn.
  - apply Nat.eqb_refl.
  - destruct (Nat.eqb x a); auto.
Qed.

Lemma alpha_var_sym : forall xs ys x y,
  alpha_var xs ys x y = true -> alpha_var ys xs y x = true.
Proof.
  induction xs as [|a xs IH]; destruct ys as [|b ys];
    intros x y H; cbn in *; try discriminate.
  - now rewrite Nat.eqb_sym.
  - destruct (Nat.eqb x a), (Nat.eqb y b); cbn in *; eauto.
Qed.

Lemma alpha_var_trans : forall xs zs ys x y z,
  alpha_var xs zs x y = true -> alpha_var zs ys y z = true ->
  alpha_var xs ys x z = true.
Proof.
  induction xs as [|a xs IH]; destruct zs as [|b zs];
    destruct ys as [|c ys]; intros x y z Hxy Hyz; cbn in *;
    try discriminate.
  - apply Nat.eqb_eq in Hxy, Hyz. subst. apply Nat.eqb_refl.
  - destruct (Nat.eqb x a), (Nat.eqb y b), (Nat.eqb z c);
      cbn in *; eauto; discriminate.
Qed.

Lemma alpha_eqb_in_refl : forall t env, alpha_eqb_in env env t t = true.
Proof.
  induction t; intro env; cbn [alpha_eqb_in];
    repeat rewrite Bool.andb_true_iff;
    repeat rewrite Nat.eqb_eq;
    repeat rewrite String.eqb_eq;
    intuition auto using alpha_var_refl.
Qed.

Lemma alpha_eqb_in_sym : forall t u xs ys,
  alpha_eqb_in xs ys t u = true -> alpha_eqb_in ys xs u t = true.
Proof.
  induction t; destruct u; intros xs ys H;
    cbn [alpha_eqb_in] in *; try discriminate;
    repeat rewrite Bool.andb_true_iff in *;
    repeat rewrite Nat.eqb_eq in *;
    repeat rewrite String.eqb_eq in *;
    intuition eauto using alpha_var_sym.
Qed.

Lemma alpha_eqb_in_trans : forall t u v xs zs ys,
  alpha_eqb_in xs zs t u = true ->
  alpha_eqb_in zs ys u v = true ->
  alpha_eqb_in xs ys t v = true.
Proof.
  induction t; intros u v xs zs ys Htu Huv;
    destruct u; cbn [alpha_eqb_in] in Htu; try discriminate;
    destruct v; cbn [alpha_eqb_in] in *; try discriminate;
    repeat rewrite Bool.andb_true_iff in *;
    repeat rewrite Nat.eqb_eq in *;
    repeat rewrite String.eqb_eq in *;
    intuition eauto using alpha_var_trans; congruence.
Qed.

#[global] Instance alpha_equiv_Equivalence : Equivalence alpha_equiv.
Proof.
  unfold alpha_equiv, alpha_eqb. split.
  - intro t. apply alpha_eqb_in_refl.
  - intros t u. apply alpha_eqb_in_sym.
  - intros t u v. apply alpha_eqb_in_trans.
Qed.

#[global] Instance term_alpha_setoid : Setoid term :=
  {| equiv := alpha_equiv; setoid_equiv := alpha_equiv_Equivalence |}.

Lemma alpha_eqb_true_iff : forall t u,
  alpha_eqb t u = true <-> alpha_equiv t u.
Proof. reflexivity. Qed.

Lemma alpha_eqb_false_iff : forall t u,
  alpha_eqb t u = false <-> ~ alpha_equiv t u.
Proof.
  intros t u. unfold alpha_equiv. destruct (alpha_eqb t u); intuition discriminate.
Qed.

Lemma alpha_eqb_refl : forall t, alpha_eqb t t = true.
Proof. intro t. apply alpha_eqb_in_refl. Qed.

Lemma alpha_eqb_equiv_left : forall t u v,
  alpha_equiv t u -> alpha_eqb t v = alpha_eqb u v.
Proof.
  intros t u v Htu.
  destruct (alpha_eqb t v) eqn:Htv, (alpha_eqb u v) eqn:Huv; try reflexivity.
  - apply alpha_eqb_false_iff in Huv. exfalso. apply Huv.
    transitivity t; [symmetry; exact Htu | exact Htv].
  - apply alpha_eqb_false_iff in Htv. exfalso. apply Htv.
    transitivity u; assumption.
Qed.

Lemma alpha_equiv_free_ids : forall x y,
  alpha_equiv (TVar x) (TVar y) <-> x = y.
Proof. intros x y. apply Nat.eqb_eq. Qed.

Lemma alpha_distinct_free_ids : forall x y,
  x <> y -> ~ alpha_equiv (TVar x) (TVar y).
Proof. intros x y Hneq Heq. apply Hneq, alpha_equiv_free_ids. exact Heq. Qed.

Lemma alpha_lam_identity : forall x y,
  alpha_equiv (TLam x (TVar x)) (TLam y (TVar y)).
Proof.
  intros x y. unfold alpha_equiv, alpha_eqb. cbn. rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* Term IDs are arena positions, not binding IDs. Allocation is sequential,
   with exact alpha comparison and no hashing. IDs are local to an arena and
   remain stable when that arena is extended through intern. *)
Definition term_id := nat.
Definition arena := list term.
Definition empty_arena : arena := [].
Definition resolve (a : arena) (id : term_id) : option term := nth_error a id.

Fixpoint find_alpha (t : term) (a : arena) : option term_id :=
  match a with
  | [] => None
  | r :: rest =>
      if alpha_eqb t r then Some 0 else option_map S (find_alpha t rest)
  end.

Definition intern (a : arena) (t : term) : arena * term_id :=
  match find_alpha t a with
  | Some id => (a, id)
  | None => (a ++ [t], List.length a)
  end.

(* This invariant holds for every arena built from empty_arena using intern.
   It excludes manually constructed tables with duplicate alpha classes. *)
Definition arena_valid (a : arena) : Prop :=
  forall i j t u, resolve a i = Some t -> resolve a j = Some u ->
    alpha_equiv t u -> i = j.

Lemma empty_arena_valid : arena_valid empty_arena.
Proof. intros [|i] j t u H; discriminate. Qed.

Lemma find_alpha_sound : forall a t id,
  find_alpha t a = Some id ->
  exists r, resolve a id = Some r /\ alpha_equiv t r.
Proof.
  induction a as [|r rest IH]; intros t id H; cbn in H; try discriminate.
  destruct (alpha_eqb t r) eqn:Halpha.
  - inversion H; subst. exists r. split; [reflexivity|].
    apply alpha_eqb_true_iff. exact Halpha.
  - destruct (find_alpha t rest) as [j|] eqn:Hfind; cbn in H; try discriminate.
    inversion H; subst. destruct (IH _ _ Hfind) as [s [Hresolve Hs]].
    exists s. split; assumption.
Qed.

Lemma find_alpha_equiv : forall a t u,
  alpha_equiv t u -> find_alpha t a = find_alpha u a.
Proof.
  induction a as [|r rest IH]; intros t u H; cbn; [reflexivity|].
  rewrite (alpha_eqb_equiv_left t u r H), (IH t u H). reflexivity.
Qed.

Lemma find_alpha_none_not_in : forall a t,
  find_alpha t a = None -> forall r, In r a -> ~ alpha_equiv t r.
Proof.
  induction a as [|r rest IH]; intros t H s Hin; cbn in *; [contradiction|].
  destruct (alpha_eqb t r) eqn:Halpha; try discriminate.
  destruct (find_alpha t rest) eqn:Hfind; cbn in H; try discriminate.
  destruct Hin as [->|Hin].
  - now apply alpha_eqb_false_iff in Halpha.
  - exact (IH t Hfind s Hin).
Qed.

Lemma find_alpha_complete : forall a t r id,
  resolve a id = Some r -> alpha_equiv t r ->
  exists found, find_alpha t a = Some found.
Proof.
  intros a t r id Hresolve Halpha.
  destruct (find_alpha t a) as [found|] eqn:Hfind; [eauto|].
  exfalso. apply (find_alpha_none_not_in a t Hfind r); [|exact Halpha].
  apply nth_error_In with (n := id). exact Hresolve.
Qed.

Lemma intern_existing : forall a t id,
  find_alpha t a = Some id -> intern a t = (a, id).
Proof. intros a t id H. unfold intern. rewrite H. reflexivity. Qed.

Lemma intern_fresh : forall a t,
  find_alpha t a = None -> intern a t = (a ++ [t], List.length a).
Proof. intros a t H. unfold intern. rewrite H. reflexivity. Qed.

Lemma intern_fresh_size : forall a t,
  find_alpha t a = None -> List.length (fst (intern a t)) = S (List.length a).
Proof.
  intros a t H. rewrite (intern_fresh a t H). cbn.
  rewrite length_app. cbn. lia.
Qed.

Lemma intern_reuses_equivalent : forall a t u id,
  find_alpha t a = Some id -> alpha_equiv t u -> intern a u = (a, id).
Proof.
  intros a t u id Hfind Halpha. apply intern_existing.
  rewrite <- (find_alpha_equiv a t u Halpha). exact Hfind.
Qed.

Lemma intern_equiv_id : forall a t u,
  alpha_equiv t u -> snd (intern a t) = snd (intern a u).
Proof.
  intros a t u Halpha. unfold intern.
  rewrite (find_alpha_equiv a t u Halpha).
  destruct (find_alpha u a); reflexivity.
Qed.

Lemma intern_sound : forall a t,
  exists r, resolve (fst (intern a t)) (snd (intern a t)) = Some r /\
    alpha_equiv t r.
Proof.
  intros a t. unfold intern. destruct (find_alpha t a) as [id|] eqn:Hfind; cbn.
  - exact (find_alpha_sound a t id Hfind).
  - exists t. split; [|reflexivity]. unfold resolve.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma intern_id_bound : forall a t,
  snd (intern a t) < List.length (fst (intern a t)).
Proof.
  intros a t. destruct (intern_sound a t) as [r [Hresolve _]].
  apply nth_error_Some. unfold resolve in Hresolve. rewrite Hresolve. discriminate.
Qed.

Lemma intern_resolve_stable : forall a t id r,
  resolve a id = Some r -> resolve (fst (intern a t)) id = Some r.
Proof.
  intros a t id r Hresolve. unfold intern.
  destruct (find_alpha t a); cbn; [exact Hresolve|].
  unfold resolve in *. rewrite nth_error_app1; [exact Hresolve|].
  apply nth_error_Some. rewrite Hresolve. discriminate.
Qed.

Lemma intern_appends : forall a t,
  exists suffix, fst (intern a t) = a ++ suffix.
Proof.
  intros a t. unfold intern. destruct (find_alpha t a); cbn.
  - exists []. now rewrite app_nil_r.
  - exists [t]. reflexivity.
Qed.

Lemma intern_preserves_valid : forall a t,
  arena_valid a -> arena_valid (fst (intern a t)).
Proof.
  intros a t Hvalid. unfold intern.
  destruct (find_alpha t a) as [id|] eqn:Hfind; cbn; [exact Hvalid|].
  intros i j r s Hi Hj Halpha. unfold resolve in *.
  destruct (lt_dec i (List.length a)), (lt_dec j (List.length a)).
  - rewrite nth_error_app1 in Hi, Hj by assumption.
    exact (Hvalid i j r s Hi Hj Halpha).
  - rewrite nth_error_app1 in Hi by assumption.
    rewrite nth_error_app2 in Hj by lia.
    destruct (j - List.length a) as [|[|j_tail]]; cbn in Hj; try discriminate.
    inversion Hj; subst s. exfalso.
    apply (find_alpha_none_not_in a t Hfind r).
    + eapply nth_error_In. exact Hi.
    + symmetry. exact Halpha.
  - rewrite nth_error_app1 in Hj by assumption.
    rewrite nth_error_app2 in Hi by lia.
    destruct (i - List.length a) as [|[|i_tail]]; cbn in Hi; try discriminate.
    inversion Hi; subst r. exfalso.
    apply (find_alpha_none_not_in a t Hfind s).
    + eapply nth_error_In. exact Hj.
    + exact Halpha.
  - rewrite nth_error_app2 in Hi, Hj by lia.
    destruct (i - List.length a) as [|[|i_tail]] eqn:Ei;
      destruct (j - List.length a) as [|[|j_tail]] eqn:Ej;
      cbn in Hi, Hj; try discriminate; lia.
Qed.

Lemma find_alpha_append_fresh : forall a t u,
  find_alpha t a = None -> alpha_equiv t u ->
  find_alpha t (a ++ [u]) = Some (List.length a).
Proof.
  induction a as [|r rest IH]; intros t u Hfind Halpha; cbn in *.
  - apply alpha_eqb_true_iff in Halpha. now rewrite Halpha.
  - destruct (alpha_eqb t r); [discriminate|].
    destruct (find_alpha t rest) eqn:Hrest; cbn in Hfind; try discriminate.
    rewrite (IH t u Hrest Halpha). reflexivity.
Qed.

Lemma find_alpha_intern : forall a t,
  find_alpha t (fst (intern a t)) = Some (snd (intern a t)).
Proof.
  intros a t. unfold intern. destruct (find_alpha t a) eqn:Hfind; cbn.
  - exact Hfind.
  - apply find_alpha_append_fresh; [exact Hfind|reflexivity].
Qed.

Lemma intern_equivalent_after : forall a t u,
  alpha_equiv t u ->
  intern (fst (intern a t)) u = (fst (intern a t), snd (intern a t)).
Proof.
  intros a t u Halpha. apply intern_reuses_equivalent with (t := t);
    [apply find_alpha_intern|exact Halpha].
Qed.

Lemma arena_valid_unique_ids : forall a i j t u,
  arena_valid a -> resolve a i = Some t -> resolve a j = Some u ->
  alpha_equiv t u -> i = j.
Proof. intros a i j t u Hvalid. apply Hvalid. Qed.

Lemma intern_distinct_classes : forall a t u,
  ~ alpha_equiv t u ->
  snd (intern a t) <> snd (intern (fst (intern a t)) u).
Proof.
  intros a t u Hneq Heq.
  destruct (intern_sound a t) as [r [Hr Htr]].
  destruct (intern_sound (fst (intern a t)) u) as [s [Hs Hus]].
  pose proof (intern_resolve_stable (fst (intern a t)) u
    (snd (intern a t)) r Hr) as Hstable.
  rewrite Heq in Hstable. rewrite Hs in Hstable. inversion Hstable; subst s.
  apply Hneq. transitivity r; [exact Htr | symmetry; exact Hus].
Qed.

Lemma intern_distinct_free_ids : forall a x y,
  x <> y ->
  snd (intern a (TVar x)) <>
    snd (intern (fst (intern a (TVar x))) (TVar y)).
Proof.
  intros a x y Hneq. apply intern_distinct_classes, alpha_distinct_free_ids.
  exact Hneq.
Qed.
