(* Erasure commutes with binding, including binding inside annotations. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AErase annotated.ABinding.

Lemma erase_lift : forall t d c,
  erase (lift d c t) = Raw.lift d c (erase t).
Proof.
  induction t; intros d c; cbn [lift erase Raw.lift];
    try solve [destruct (n <? c); reflexivity];
    f_equal; auto.
Qed.

Lemma erase_subst : forall t u c,
  erase (subst u c t) = Raw.subst (erase u) c (erase t).
Proof.
  induction t; intros u c; cbn [subst erase Raw.subst];
    try solve [destruct (n <? c), (n =? c); cbn [erase]; auto using erase_lift];
    f_equal; auto.
Qed.

Lemma erase_arrow : forall A B,
  erase (arrow A B) = Raw.arrow (erase A) (erase B).
Proof. intros; cbn [arrow erase Raw.arrow]; now rewrite erase_lift. Qed.

Lemma erase_product : forall A B,
  erase (product A B) = Raw.product (erase A) (erase B).
Proof. intros; cbn [product erase Raw.product]; now rewrite erase_lift. Qed.

Lemma erase_Def : forall IT, erase (Def IT) = Raw.Def (erase IT).
Proof. intros; cbn [Def erase Raw.Def]; now rewrite erase_lift. Qed.

Lemma erase_Family : forall IT, erase (Family IT) = Raw.Family (erase IT).
Proof. reflexivity. Qed.

Print Assumptions erase_lift.
Print Assumptions erase_subst.
