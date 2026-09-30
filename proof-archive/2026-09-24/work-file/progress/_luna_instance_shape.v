Require Import Progress SignatureInstances _parent_instance_pruning _parent_pruning_commute.
Import Progress._tmp_epstep.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Definition instance_luna (B L i : term) : term :=
  TApp (TMuS (TPair B L)) i.

Lemma fstep_instance_inv : forall B L i t,
    fstep (instance_luna B L i) t ->
    (exists B', t = instance_luna B' L i /\ fstep B B') \/
    (exists L', t = instance_luna B L' i /\ fstep L L') \/
    (exists i', t = instance_luna B L i' /\ fstep i i').
Proof.
  intros B L i t H. unfold instance_luna in *.
  inversion H; subst; eauto using fstep.
  all: try solve [inversion H0; subst; eauto using fstep].
  all: try match goal with
    Hf : fstep (TMuS (TPair _ _)) _ |- _ =>
      inversion Hf; subst; eauto using fstep
    end.
  all: try solve [inversion H0; subst; eauto using fstep].
  all: try solve [inversion H1; subst; eauto using fstep].
  all: try solve [inversion H2; subst; eauto using fstep].
  all: try match goal with
    Hx : fstep (TPair _ _) _ |- _ => inversion Hx; subst; eauto using fstep
    end.
  all: try match goal with
    Hx : fstep (TMuS _) _ |- _ => inversion Hx; subst; eauto using fstep
    end.
  all: try solve [inversion H0; subst; eauto using fstep, fs_app1, fs_app2].
  repeat match goal with
  | Hs : step (TApp (TMuS _) _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : step (TMuS _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : step (TPair _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hf : fstep (TMuS _) _ |- _ => inversion Hf; subst; clear Hf
  | Hf : fstep (TPair _ _) _ |- _ => inversion Hf; subst; clear Hf
  end;
  eauto 6 using fstep.
  all: match goal with
    Hx : fstep (TPair ?B ?L) ?S' |- _ =>
      destruct (pruning_fstep_pair_inv B L S' Hx)
        as [[Bnew [-> HB]] | [Lnew [-> HL]]];
      [ left; exists Bnew; auto | right; left; exists Lnew; auto ]
    end.
Qed.
Lemma prune_instance_inv : forall B L i t,
    prune_term (instance_luna B L i) t ->
    exists B' L' i', t = instance_luna B' L' i' /\
      prune_term B B' /\ prune_labels B L L' /\ prune_term i i'.
Proof.
  intros B L i t H. unfold instance_luna in *.
  inversion H; subst.
  all: try match goal with
    Hm : prune_term (TMuS (TPair ?B0 ?L0)) ?f' |- _ =>
      destruct (prune_mus_pair_inv B0 L0 f' Hm)
        as [B' [L' [-> [HB HL]]]];
      eexists; eexists; eexists; repeat split; eauto
    end.
  all: eexists; eexists; eexists; repeat split; eauto.
Qed.

Print Assumptions fstep_instance_inv.
Print Assumptions prune_instance_inv.
