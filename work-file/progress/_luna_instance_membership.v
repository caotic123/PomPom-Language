Require Import Progress SignatureConversion _parent_instance_pruning.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import Progress._work_cjoin Progress._work_cstep_invariants.

Inductive joined_mem (c : term) : term -> Prop :=
| jm_here : forall L A d R,
    cjoin L (TLCons A d R) -> cjoin c d -> joined_mem c L
| jm_there : forall L A d R,
    cjoin L (TLCons A d R) -> joined_mem c R -> joined_mem c L.

Lemma joined_mem_transport : forall c L1,
  joined_mem c L1 -> forall L2, cjoin L1 L2 -> joined_mem c L2.
Proof.
  intros c L1 H. induction H as [L A d R HL Hc | L A d R HL Htail IH]; intros L2 H12.
  - apply jm_here with (L := L2) (A := A) (d := d) (R := R).
    + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
    + exact Hc.
  - apply jm_there with (L := L2) (A := A) (d := d) (R := R).
    + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
    + assert (HC : cjoin L2 (TLCons A d R)).
      { eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL]. }
      exact Htail.
Qed.

Lemma joined_mem_cons_inv : forall c A d R,
  joined_mem c (TLCons A d R) ->
  cjoin c d \/ joined_mem c R.
Proof.
  intros c A d R H. inversion H; subst.
  - left.
    destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ H0) as [_ [Hcd _]].
    eapply cjoin_trans; [exact H1|apply cjoin_sym; exact Hcd].
  - right.
    destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ H0) as [_ [_ Hlr]].
    eapply joined_mem_transport; [exact H1|apply cjoin_sym; exact Hlr].
Qed.

Lemma prune_labels_joined_mem : forall B L L',
  prune_labels B L L' -> forall c P,
  joined_mem (phi_erase c) (phi_erase L) ->
  (forall d, cjoin (phi_erase c) (phi_erase d) ->
    instance_dead (TApp B d) -> P) ->
  joined_mem (phi_erase c) (phi_erase L') \/ P.
Proof.
  intros B L L' H. induction H; intros x P Hmem HP.
  - left. eapply joined_mem_transport; [exact Hmem|].
    assert (Heq : phi_erase L = phi_erase L') by
      (apply prune_erase; assumption).
    rewrite Heq. apply cjoin_refl.
  - destruct (joined_mem_cons_inv _ _ _ _ Hmem) as [Hhead|Htail].
    + change (cjoin (phi_erase x) (phi_erase c)) in Hhead.
      rewrite (prune_erase _ _ H0) in Hhead.
      left. apply jm_here with (L := phi_erase (TLCons A' c' L'))
        (A := phi_erase A') (d := phi_erase c') (R := phi_erase L').
      * apply cjoin_refl.
      * eapply cjoin_trans; [exact Hhead|].
        apply cjoin_refl.
    + destruct (IHprune_labels x P Htail HP) as [Ht|Hp].
      * left. eapply jm_there; [apply cjoin_refl|exact Ht].
      * right; exact Hp.
  - destruct (joined_mem_cons_inv _ _ _ _ Hmem) as [Hhead|Htail].
    + right. eapply HP; [exact Hhead|].
      assumption.
    + destruct (IHprune_labels x P Htail HP) as [Ht|Hp].
      * left; exact Ht.
      * right; exact Hp.
Qed.

Print Assumptions joined_mem_transport.
Print Assumptions joined_mem_cons_inv.
Print Assumptions prune_labels_joined_mem.
