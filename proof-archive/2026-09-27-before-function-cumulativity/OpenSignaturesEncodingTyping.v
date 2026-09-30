From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesConfluence OpenSignaturesTransport.
Require nameless.DBSubstitution.
Import ListNotations.

Lemma alpha_var_same_inverse : forall env x y,
  alpha_var env env x y = true -> x = y.
Proof.
  induction env as [|a env IH]; intros x y H; cbn [alpha_var] in H.
  - now apply Nat.eqb_eq.
  - destruct (Nat.eqb x a) eqn:Ex; destruct (Nat.eqb y a) eqn:Ey; try discriminate.
    + apply Nat.eqb_eq in Ex, Ey; congruence.
    + now apply IH.
Qed.
Lemma encode_env_alpha : forall env t u, encode env t = encode env u -> alpha_equiv t u.
Proof.
  intros env t u H. apply encode_alpha_inverse in H; [|reflexivity].
  eapply alpha_env_mono; [exact H|]. intros x y Hx Hy Hxy.
  apply alpha_var_same_inverse in Hxy; subst. apply Nat.eqb_refl.
Qed.
Lemma encode_conversion_inverse : forall env t u,
  DC.conv (encode env t) (encode env u) -> conv t u.
Proof.
  intros env t u H.
  destruct (nameless.DBConfluence.conversion_joinable _ _ H) as [w [Ht Hu]].
  destruct (encode_reductions_inverse _ _ Ht t env eq_refl) as [t' [Htt He]].
  destruct (encode_reductions_inverse _ _ Hu u env eq_refl) as [u' [Huu He']].
  eapply cv_trans; [exact (reduces_conv _ _ Htt)|].
  eapply cv_trans with (u:=u'); [apply cv_alpha;apply (encode_env_alpha env);congruence|].
  apply cv_sym;exact (reduces_conv _ _ Huu).
Qed.

Lemma encode_arrow : forall A B env,
  encode env (arrow A B) = DB.arrow (encode env A) (encode env B).
Proof.
  intros; unfold arrow, DB.arrow; cbn [encode]. f_equal.
  apply encode_fresh, fresh_not_free. cbn; auto.
Qed.
Lemma encode_Def : forall IT env, encode env (Def IT) = DB.Def (encode env IT).
Proof.
  intros; unfold Def, DB.Def; cbn [encode]. rewrite encode_fresh by (apply fresh_not_free;cbn;auto).
  reflexivity.
Qed.
Lemma encode_Family : forall IT env, encode env (Family IT) = DB.Family (encode env IT).
Proof. reflexivity. Qed.
Lemma encode_total : forall IT X env, encode env (total IT X) = DB.total (encode env IT) (encode env X).
Proof.
  intros; unfold total, DB.total; cbn [encode encode_var]. rewrite Nat.eqb_refl.
  rewrite encode_fresh by (apply fresh_not_free;cbn;auto). reflexivity.
Qed.
Lemma encode_motive : forall IT X env, encode env (motive IT X) = DB.motive (encode env IT) (encode env X).
Proof. intros; unfold motive, DB.motive. rewrite encode_arrow, encode_total; reflexivity. Qed.

Local Ltac fresh_terms n :=
  lazymatch n with
  | fresh ?ts => constr:(ts)
  | S ?m => fresh_terms m
  end.
Local Ltac encode_generated_fresh :=
  match goal with |- ~ In ?n (free_vars ?t) =>
    let ts := fresh_terms n in apply (above_fresh_not_free ts t n); [cbn;tauto|lia]
  end.
Local Ltac generated_encoding :=
  cbn [encode encode_var]; repeat rewrite encode_diagonal;
  repeat rewrite Nat.eqb_refl;
  repeat rewrite encode_fresh by encode_generated_fresh;
  cbn [DB.lift];
  repeat match goal with |- context [Nat.eqb ?n ?m] =>
    let E := fresh "E" in assert (E : Nat.eqb n m = false) by (apply Nat.eqb_neq;lia);
    rewrite E;clear E
  end;
  repeat rewrite nameless.DBParallelBase.lift_fuse_zero by lia;
  try reflexivity.

Lemma encode_recursive_method : forall IT X P env,
  encode env (recursive_method IT X P) = DB.recursive_method (encode env IT) (encode env X) (encode env P).
Proof. intros; unfold recursive_method, DB.recursive_method. generated_encoding. Qed.
Lemma encode_close_case_method : forall IT F G i Q env,
  encode env (close_case_method IT F G i Q) = DB.close_case_method
    (encode env IT) (encode env F) (encode env G) (encode env i) (encode env Q).
Proof. intros; unfold close_case_method, DB.close_case_method, payload, DB.payload, carrier, DB.carrier. generated_encoding. Qed.
Lemma encode_close_motive : forall IT G env,
  encode env (close_motive IT G) = DB.close_motive (encode env IT) (encode env G).
Proof. intros; unfold close_motive, DB.close_motive, CloseAt, DB.CloseAt. generated_encoding. now rewrite encode_Def. Qed.
Lemma encode_mu_ind_method : forall IT D P env,
  encode env (mu_ind_method IT D P) = DB.mu_ind_method (encode env IT) (encode env D) (encode env P).
Proof. intros; unfold mu_ind_method, DB.mu_ind_method. generated_encoding. Qed.
Lemma encode_close_ind_method : forall IT G P env,
  encode env (close_ind_method IT G P) = DB.close_ind_method (encode env IT) (encode env G) (encode env P).
Proof.
  intros; unfold close_ind_method, DB.close_ind_method, payload, DB.payload, carrier, DB.carrier.
  generated_encoding. rewrite encode_Def.
  cbn [DB.lift]. repeat rewrite nameless.DBParallelBase.lift_fuse_zero by lia. reflexivity.
Qed.
