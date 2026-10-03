(* Instantiating a derived form gives the derived form of the instantiated
   components, up to alpha-equivalence (hence conversion). *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelEnv.
Import ListNotations.

Lemma encode_closed_cons : forall t x env, closed t -> encode (x :: env) t = encode [] t.
Proof. intros; apply encode_closed_env; assumption. Qed.

Lemma drop_absent_mono : forall x z g, ~ In x (map fst g) -> ~ In x (map fst (drop z g)).
Proof.
  intros x z g H; induction g as [|[y u] g IH]; cbn in *; [tauto|].
  destruct (Nat.eqb y z); cbn; [apply IH; tauto|].
  intros [Hy|Hy]; [apply H; left; exact Hy|apply IH; [tauto|exact Hy]].
Qed.

Ltac fresh_any := match goal with
  | |- ~ In ?x _ => match x with context [fresh ?ts] =>
      solve [apply (above_fresh_not_free ts); [cbn; auto 10|unfold fresh; lia]] end end.

Ltac env_side := first
  [ assumption
  | repeat apply drop_closed; assumption
  | solve [repeat first [apply drop_absent | apply drop_absent_mono]]
  | fresh_out2
  | fresh_any ].

Ltac inst_simpl := repeat first
  [ rewrite inst_pi by env_side
  | rewrite inst_sigma by env_side
  | rewrite inst_lam by env_side
  | rewrite instantiate_app
  | rewrite inst_tpair | rewrite inst_tin | rewrite inst_tinterp | rewrite inst_mui
  | rewrite inst_iall | rewrite inst_tclose | rewrite inst_idesc | rewrite inst_fst | rewrite inst_snd
  | rewrite instantiate_sort
  | rewrite inst_var_absent by env_side
  | rewrite inst_notfree by env_side ].

Ltac eqb_simpl := repeat match goal with
  | |- context [Nat.eqb ?a ?a] => rewrite (Nat.eqb_refl a)
  | |- context [Nat.eqb ?a ?b] => rewrite (proj2 (Nat.eqb_neq a b)) by lia
  end.

Ltac by_encoding := apply cv_alpha, encode_alpha_iff; cbn [encode encode_var];
  repeat match goal with H : closed ?t |- context [encode (?x :: ?e) ?t] =>
    rewrite (encode_closed_cons t x e H) end; eqb_simpl; reflexivity.

Section Derived.
Variable g : env.
Hypothesis Hg : env_closed g.

Lemma inst_arrow : forall A B, closed (instantiate g A) -> closed (instantiate g B) ->
  conv (instantiate g (arrow A B)) (arrow (instantiate g A) (instantiate g B)).
Proof. intros A B HA HB; unfold arrow; inst_simpl; by_encoding. Qed.

Lemma inst_Def : forall IT, closed (instantiate g IT) ->
  conv (instantiate g (Def IT)) (Def (instantiate g IT)).
Proof. intros IT HI; unfold Def; inst_simpl; by_encoding. Qed.

Lemma inst_Family : forall IT, closed (instantiate g IT) ->
  conv (instantiate g (Family IT)) (Family (instantiate g IT)).
Proof. intros IT HI; unfold Family; inst_simpl; by_encoding. Qed.

Lemma inst_total : forall IT X, closed (instantiate g IT) -> closed (instantiate g X) ->
  conv (instantiate g (total IT X)) (total (instantiate g IT) (instantiate g X)).
Proof. intros IT X HI HX; unfold total; inst_simpl; by_encoding. Qed.

Lemma inst_motive : forall IT X, closed (instantiate g IT) -> closed (instantiate g X) ->
  conv (instantiate g (motive IT X)) (motive (instantiate g IT) (instantiate g X)).
Proof. intros IT X HI HX; unfold motive, arrow, total; inst_simpl; by_encoding. Qed.

Lemma inst_recursive_method : forall IT X P, closed (instantiate g IT) -> closed (instantiate g X) ->
  closed (instantiate g P) ->
  conv (instantiate g (recursive_method IT X P))
    (recursive_method (instantiate g IT) (instantiate g X) (instantiate g P)).
Proof. intros IT X P HI HX HP; unfold recursive_method; inst_simpl; by_encoding. Qed.

Lemma inst_mu_ind_method : forall IT D P, closed (instantiate g IT) -> closed (instantiate g D) ->
  closed (instantiate g P) ->
  conv (instantiate g (mu_ind_method IT D P))
    (mu_ind_method (instantiate g IT) (instantiate g D) (instantiate g P)).
Proof. intros IT D P HI HD HP; unfold mu_ind_method; inst_simpl; by_encoding. Qed.

Lemma inst_close_case_method : forall IT F G i Q, closed (instantiate g IT) -> closed (instantiate g F) ->
  closed (instantiate g G) -> closed (instantiate g i) -> closed (instantiate g Q) ->
  conv (instantiate g (close_case_method IT F G i Q))
    (close_case_method (instantiate g IT) (instantiate g F) (instantiate g G) (instantiate g i) (instantiate g Q)).
Proof. intros IT F G i Q H1 H2 H3 H4 H5; unfold close_case_method, payload, carrier; inst_simpl; by_encoding. Qed.

Lemma inst_close_motive : forall IT G, closed (instantiate g IT) -> closed (instantiate g G) ->
  conv (instantiate g (close_motive IT G)) (close_motive (instantiate g IT) (instantiate g G)).
Proof. intros IT G H1 H2; unfold close_motive, Def, CloseAt; inst_simpl; by_encoding. Qed.

Lemma inst_close_ind_method : forall IT G P, closed (instantiate g IT) -> closed (instantiate g G) ->
  closed (instantiate g P) ->
  conv (instantiate g (close_ind_method IT G P))
    (close_ind_method (instantiate g IT) (instantiate g G) (instantiate g P)).
Proof.
  intros IT G P H1 H2 H3; unfold close_ind_method, Def, payload, carrier, diagonal_motive; inst_simpl; by_encoding.
Qed.

Lemma inst_MuAt : forall IT D i, instantiate g (MuAt IT D i) = MuAt (instantiate g IT) (instantiate g D) (instantiate g i).
Proof. intros; unfold MuAt; rewrite instantiate_app, inst_mui; reflexivity. Qed.
Lemma inst_CloseAt : forall IT F G i, instantiate g (CloseAt IT F G i) =
  CloseAt (instantiate g IT) (instantiate g F) (instantiate g G) (instantiate g i).
Proof. intros; unfold CloseAt; rewrite instantiate_app, inst_tclose; reflexivity. Qed.
Lemma inst_payload : forall IT F G i, instantiate g (payload IT F G i) =
  payload (instantiate g IT) (instantiate g F) (instantiate g G) (instantiate g i).
Proof. intros; unfold payload, carrier; rewrite inst_tinterp, instantiate_app, inst_tclose; reflexivity. Qed.

End Derived.
