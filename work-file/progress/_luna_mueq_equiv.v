Require Import _luna_mueq.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma mueq_sym_mut :
    (forall t u, mueq t u -> mueq u t) /\
    (forall bs bs', mubeq bs bs' -> mubeq bs' bs).
Proof.
  apply mueq_mubeq_ind; intros; simpl in *.
  all: try solve [constructor; auto].
  all: try solve [constructor; auto; apply H].
  all: try solve [constructor; auto; apply H; apply H0].
  all: try solve [constructor; auto; apply H; apply H0; apply H1].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2; apply H3].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2; apply H3; apply H4].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2; apply H3; apply H4; apply H5].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2; apply H3; apply H4; apply H5; apply H6].
  all: try solve [constructor; auto; apply H; apply H0; apply H1; apply H2; apply H3; apply H4; apply H5; apply H6; apply H7].
  all: try solve [eapply me_muapp; eapply cv_sym; eassumption].
Qed.

Lemma mueq_sym : forall t u, mueq t u -> mueq u t.
Proof. exact (proj1 mueq_sym_mut). Qed.

Lemma mubeq_sym : forall bs bs', mubeq bs bs' -> mubeq bs' bs.
Proof. exact (proj2 mueq_sym_mut). Qed.

Lemma mueq_trans_mut :
    (forall t u (h : mueq t u), forall v, mueq u v -> mueq t v) /\
    (forall bs bs' (h : mubeq bs bs'), forall bs'', mubeq bs' bs'' -> mubeq bs bs'').
Proof.
  apply mueq_mubeq_ind; intros; simpl in *.
  all: eauto.
  all: try match goal with
    | |- mueq _ ?v =>
        match goal with
        | H : mueq _ v |- _ => destruct H; subst; eauto
        end
    end.
  all: try match goal with
    | |- mubeq _ ?bs =>
        match goal with
        | H : mubeq _ bs |- _ => destruct H; subst; eauto
        end
    end.
Qed.

Lemma mueq_trans : forall t u v, mueq t u -> mueq u v -> mueq t v.
Proof. intros t u v h h'. exact (proj1 mueq_trans_mut t u h v h'). Qed.

Lemma mubeq_trans : forall bs bs' bs'', mubeq bs bs' -> mubeq bs' bs'' -> mubeq bs bs''.
Proof. intros bs bs' bs'' h h'. exact (proj2 mueq_trans_mut bs bs' h bs'' h'). Qed.
