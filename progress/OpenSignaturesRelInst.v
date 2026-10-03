(* Instantiation by closed environments: binders, closedness, and
   derived forms up to alpha-equivalence. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelRules OpenSignaturesEncoding.
Import ListNotations.

Definition env := list (nat * term).
Definition env_closed (g : env) := Forall (fun e => closed (snd e)) g.
Definition drop (z : nat) (g : env) : env := filter (fun e => negb (Nat.eqb (fst e) z)) g.

(* ------------------------------------------------------------------ *)
(* Substitution under binders *)

Lemma bind_shadow : forall u x t,
  substitute (bind_substitution (fun v => if Nat.eqb v x then u else TVar v) x x) t = t.
Proof.
  intros u x t; apply substitute_identity_on; intros v _; unfold bind_substitution.
  destruct (Nat.eqb v x) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity|reflexivity].
Qed.
Lemma binder_shadow : forall u x b,
  substitution_binder (fun v => if Nat.eqb v x then u else TVar v) x b = x.
Proof.
  intros; apply substitution_binder_identity; intros v Hv; apply in_remove_iff in Hv as [_ Hv].
  rewrite (proj2 (Nat.eqb_neq v x)) by auto; reflexivity.
Qed.
Lemma subst_pi_shadow : forall u x A B, subst u x (TPi x A B) = TPi x (subst u x A) B.
Proof. intros; unfold subst at 1; cbn [substitute]; rewrite binder_shadow, bind_shadow; reflexivity. Qed.
Lemma subst_lam_shadow : forall u x b, subst u x (TLam x b) = TLam x b.
Proof. intros; unfold subst at 1; cbn [substitute]; rewrite binder_shadow, bind_shadow; reflexivity. Qed.
Lemma subst_sigma_shadow : forall u x A B, subst u x (TSigma x A B) = TSigma x (subst u x A) B.
Proof. intros; unfold subst at 1; cbn [substitute]; rewrite binder_shadow, bind_shadow; reflexivity. Qed.
Lemma subst_closed_sigma : forall u k x A B, free_vars u = [] -> k <> x ->
  subst u k (TSigma x A B) = TSigma x (subst u k A) (subst u k B).
Proof.
  intros u k x A B Hu Hne. unfold subst at 1; cbn [substitute].
  rewrite closed_substitution_binder by assumption.
  now rewrite bind_closed_substitution.
Qed.

Lemma inst_pi : forall g z A B, env_closed g ->
  instantiate g (TPi z A B) = TPi z (instantiate g A) (instantiate (drop z g) B).
Proof.
  induction g as [|[y u] g IH]; intros z A B Hg; [reflexivity|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [instantiate drop filter fst snd] in *.
  destruct (Nat.eq_dec y z) as [->|Hne].
  - rewrite Nat.eqb_refl; cbn [negb]. rewrite subst_pi_shadow, IH by exact Hg'. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq y z)) by exact Hne; cbn [negb instantiate].
    rewrite subst_closed_pi by assumption. apply IH, Hg'.
Qed.
Lemma inst_sigma : forall g z A B, env_closed g ->
  instantiate g (TSigma z A B) = TSigma z (instantiate g A) (instantiate (drop z g) B).
Proof.
  induction g as [|[y u] g IH]; intros z A B Hg; [reflexivity|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [instantiate drop filter fst snd] in *.
  destruct (Nat.eq_dec y z) as [->|Hne].
  - rewrite Nat.eqb_refl; cbn [negb]. rewrite subst_sigma_shadow, IH by exact Hg'. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq y z)) by exact Hne; cbn [negb instantiate].
    rewrite subst_closed_sigma by assumption. apply IH, Hg'.
Qed.
Lemma inst_lam : forall g z b, env_closed g ->
  instantiate g (TLam z b) = TLam z (instantiate (drop z g) b).
Proof.
  induction g as [|[y u] g IH]; intros z b Hg; [reflexivity|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [instantiate drop filter fst snd] in *.
  destruct (Nat.eq_dec y z) as [->|Hne].
  - rewrite Nat.eqb_refl; cbn [negb]. rewrite subst_lam_shadow, IH by exact Hg'. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq y z)) by exact Hne; cbn [negb instantiate].
    rewrite subst_closed_lam by assumption. apply IH, Hg'.
Qed.

Lemma drop_closed : forall z g, env_closed g -> env_closed (drop z g).
Proof.
  intros z g H; unfold drop; induction H; cbn; [constructor|].
  destruct (negb _); [constructor; assumption|assumption].
Qed.

Lemma inst_var_absent : forall g x, ~ In x (map fst g) -> instantiate g (TVar x) = TVar x.
Proof.
  induction g as [|[y u] g IH]; intros x H; [reflexivity|]; cbn [instantiate].
  cbn in H. rewrite subst_var_other by (intro; apply H; left; auto). apply IH; tauto.
Qed.
Lemma drop_absent : forall z g, ~ In z (map fst (drop z g)).
Proof.
  intros z g; induction g as [|[y u] g IH]; cbn; [tauto|].
  destruct (Nat.eqb y z) eqn:E; cbn; [exact IH|].
  apply Nat.eqb_neq in E; intros [H|H]; [congruence|tauto].
Qed.

(* Free variables after instantiation. *)
Lemma inst_free : forall g t y, env_closed g -> In y (free_vars (instantiate g t)) ->
  In y (free_vars t) /\ ~ In y (map fst g).
Proof.
  induction g as [|[x u] g IH]; intros t y Hg H; [cbn in *; tauto|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [instantiate] in H.
  destruct (IH _ _ Hg' H) as [H1 H2].
  apply free_vars_substitute in H1 as [v [Hv Hy]].
  destruct (Nat.eqb v x) eqn:E.
  - cbn in Hu; unfold closed in Hu; rewrite Hu in Hy; contradiction.
  - cbn in Hy; destruct Hy as [<-|[]]; apply Nat.eqb_neq in E.
    split; [exact Hv|]; cbn; intros [Hx|Hx]; [congruence|tauto].
Qed.
Lemma inst_notfree : forall g t z, env_closed g -> ~ In z (free_vars t) ->
  instantiate (drop z g) t = instantiate g t.
Proof.
  induction g as [|[x u] g IH]; intros t z Hg Hz; [reflexivity|].
  inversion Hg as [|? ? Hu Hg']; subst; cbn [drop filter fst instantiate].
  destruct (Nat.eqb x z) eqn:E; cbn [negb instantiate].
  - apply Nat.eqb_eq in E; subst. rewrite subst_not_free by exact Hz. apply IH; assumption.
  - apply IH; [exact Hg'|]. intro H; apply free_vars_substitute in H as [v [Hv Hy]].
    destruct (Nat.eqb v x) eqn:Ev.
    + cbn in Hu; unfold closed in Hu; rewrite Hu in Hy; contradiction.
    + cbn in Hy; destruct Hy as [<-|[]]; contradiction.
Qed.

(* Non-binding constructors commute with instantiation. *)
Ltac inst_struct := let g := fresh "g" in let IH := fresh "IH" in
  intro g; induction g as [|[? ?] ? IH]; intros; [reflexivity|]; cbn [instantiate]; apply IH.

Lemma inst_tpair : forall g a b, instantiate g (TPair a b) = TPair (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_fst : forall g a, instantiate g (TFst a) = TFst (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_snd : forall g a, instantiate g (TSnd a) = TSnd (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_conse : forall g a b, instantiate g (TConsE a b) = TConsE (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_enumt : forall g a, instantiate g (TEnumT a) = TEnumT (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_succ : forall g a, instantiate g (TESucc a) = TESucc (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_epi : forall g k a b, instantiate g (TEPi k a b) = TEPi k (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_switch : forall g k a b c d, instantiate g (TSwitch k a b c d) =
  TSwitch k (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d). Proof. inst_struct. Qed.
Lemma inst_idesc : forall g a, instantiate g (TIDesc a) = TIDesc (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_ivar : forall g a, instantiate g (TIVar a) = TIVar (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_iprod : forall g a b, instantiate g (TIProd a b) = TIProd (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_ipi : forall g a b, instantiate g (TIPi a b) = TIPi (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_isig : forall g a b, instantiate g (TISig a b) = TISig (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_ichoice : forall g a b, instantiate g (TIChoice a b) = TIChoice (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_tinterp : forall g a b c, instantiate g (TInterp a b c) = TInterp (instantiate g a) (instantiate g b) (instantiate g c). Proof. inst_struct. Qed.
Lemma inst_mui : forall g a b, instantiate g (TMuI a b) = TMuI (instantiate g a) (instantiate g b). Proof. inst_struct. Qed.
Lemma inst_tin : forall g a, instantiate g (TIn a) = TIn (instantiate g a). Proof. inst_struct. Qed.
Lemma inst_tind : forall g a b c d e f, instantiate g (TInd a b c d e f) =
  TInd (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d) (instantiate g e) (instantiate g f). Proof. inst_struct. Qed.
Lemma inst_iall : forall g a b c d e, instantiate g (TIAll a b c d e) =
  TIAll (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d) (instantiate g e). Proof. inst_struct. Qed.
Lemma inst_hyps : forall g a b c d e f, instantiate g (THyps a b c d e f) =
  THyps (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d) (instantiate g e) (instantiate g f). Proof. inst_struct. Qed.
Lemma inst_tclose : forall g a b c, instantiate g (TClose a b c) = TClose (instantiate g a) (instantiate g b) (instantiate g c). Proof. inst_struct. Qed.
Lemma inst_ccase : forall g k a b c d e f h, instantiate g (TCloseCase k a b c d e f h) =
  TCloseCase k (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d) (instantiate g e) (instantiate g f) (instantiate g h). Proof. inst_struct. Qed.
Lemma inst_cind : forall g a b c d e f h, instantiate g (TCloseInd a b c d e f h) =
  TCloseInd (instantiate g a) (instantiate g b) (instantiate g c) (instantiate g d) (instantiate g e) (instantiate g f) (instantiate g h). Proof. inst_struct. Qed.
Lemma inst_const : forall g t, (forall u x, subst u x t = t) -> instantiate g t = t.
Proof. intros g t H; induction g as [|[x u] g IH]; [reflexivity|]; cbn [instantiate]; rewrite H; exact IH. Qed.

(* ------------------------------------------------------------------ *)
(* Alpha-equivalence through the nameless encoding *)

Lemma encode_env_ext : forall t env1 env2,
  (forall v, In v (free_vars t) -> encode_var env1 v = encode_var env2 v) ->
  encode env1 t = encode env2 t.
Proof.
  induction t; intros env1 env2 H; cbn [encode]; f_equal.
  all: first
    [ reflexivity
    | apply H; simpl; auto
    | match goal with
      | IH : forall e1 e2, _ -> encode e1 ?tm = encode e2 ?tm |- encode (?x :: _) ?tm = encode (?x :: _) ?tm =>
          apply IH; intros v Hv; cbn [encode_var]; destruct (Nat.eqb v x) eqn:E; [reflexivity|];
          f_equal; apply H; cbn [free_vars]; repeat rewrite in_app_iff; rewrite ?in_remove_iff;
          apply Nat.eqb_neq in E; tauto
      | IH : forall e1 e2, _ -> encode e1 ?tm = encode e2 ?tm |- encode _ ?tm = encode _ ?tm =>
          apply IH; intros v Hv; apply H; cbn [free_vars]; repeat rewrite in_app_iff; rewrite ?in_remove_iff; tauto
      end ].
Qed.
Lemma encode_closed_env : forall t env, closed t -> encode env t = encode [] t.
Proof. intros t env H; apply encode_env_ext; intros v Hv; unfold closed in H; rewrite H in Hv; contradiction. Qed.
