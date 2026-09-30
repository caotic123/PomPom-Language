Require Import Progress SignatureConversion _parent_instance_pruning _luna_instance_membership.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import Progress._work_cjoin Progress._work_cstep_invariants.

Inductive joined_covers (bs : list term) : term -> Prop :=
| jc_nil : forall L A, cjoin L (TLNil A) -> joined_covers bs L
| jc_cons : forall L A d R,
    cjoin L (TLCons A d R) ->
    (exists b, In b bs /\ cjoin (phi_erase b) d) ->
    joined_covers bs R -> joined_covers bs L.

Lemma joined_covers_transport : forall bs L1,
  joined_covers bs L1 -> forall L2, cjoin L1 L2 -> joined_covers bs L2.
Proof.
 intros bs L1 H; induction H as [L A HL|L A d R HL Hb Htail IH]; intros L2 H12.
 - apply jc_nil with (A:=A). eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
 - apply jc_cons with (A:=A) (d:=d) (R:=R).
   + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
   + exact Hb.
   + exact Htail.
Qed.

Lemma joined_covers_cons_inv : forall bs A d R,
  joined_covers bs (TLCons A d R) ->
  (exists b, In b bs /\ cjoin (phi_erase b) d) /\ joined_covers bs R.
Proof.
 intros bs A d R H.
 inversion H as [L0 A0 Hnil | L0 A0 d0 R0 Hlist Hhead Htail].
 - exfalso. eapply no_cjoin_lcons_lnil_luna; eassumption.
 - destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ Hlist)
     as [_ [Hdd0 HRR0]].
   split.
   + destruct Hhead as [b [Hb Hbd0]]. exists b; split; [exact Hb|].
     eapply cjoin_trans; [exact Hbd0|apply cjoin_sym; exact Hdd0].
   + eapply joined_covers_transport; [exact Htail|apply cjoin_sym; exact HRR0].
Qed.

Lemma prune_labels_joined_covers : forall B L L' bs,
  prune_labels B L L' -> joined_covers bs (phi_erase L) ->
  joined_covers bs (phi_erase L').
Proof.
 intros B L L' bs H; induction H as
   [B0 L0 L'0 Hpr
   |B0 A A' c c' L0 L'0 HA Hc Hpl IH
   |B0 A c L0 L'0 Hdead Hpl IH]; intros HC.
 - rewrite <- (prune_erase _ _ Hpr). exact HC.
 - destruct (joined_covers_cons_inv _ _ _ _ HC) as [Hhead Htail].
   apply jc_cons with (A:=phi_erase A') (d:=phi_erase c') (R:=phi_erase L'0).
   + apply cjoin_refl.
   + rewrite <- (prune_erase _ _ Hc). exact Hhead.
   + exact (IH Htail).
 - destruct (joined_covers_cons_inv _ _ _ _ HC) as [_ Htail].
   exact (IH Htail).
Qed.

Lemma covers_joined : forall bs L, covers bs L -> joined_covers bs (phi_erase L).
Proof.
 intros bs L H; induction H.
 - apply jc_nil with (A:=phi_erase A).
   pose proof (conv_of_eval Phi (TLNil A) H) as HC.
   exact (conv_phi_cjoin _ _ HC).
 - apply jc_cons with (A:=phi_erase A) (d:=phi_erase c) (R:=phi_erase Phi').
   + pose proof (conv_of_eval Phi (TLCons A c Phi') H) as HC.
     exact (conv_phi_cjoin _ _ HC).
   + apply Exists_exists in H0. destruct H0 as [b [Hb Hbc]]. exists b; split; [exact Hb|].
     eapply cjoin_trans; [apply cjoin_sym; apply conv_phi_cjoin; exact Hbc|apply cjoin_refl].
   + exact IHcovers.
Qed.


Print Assumptions joined_covers_transport.
Print Assumptions joined_covers_cons_inv.
Print Assumptions prune_labels_joined_covers.
Print Assumptions covers_joined.

Lemma joined_mem_nil_absurd : forall c A,
  joined_mem c (TLNil A) -> False.
Proof.
 intros c A H.
 inversion H as [L A0 d R HL Hc | L A0 d R HL Htail].
 - apply (no_cjoin_lcons_lnil_luna A0 d R A). apply cjoin_sym. exact HL.
 - apply (no_cjoin_lcons_lnil_luna A0 d R A). apply cjoin_sym. exact HL.
Qed.

Lemma joined_mem_covered : forall c L bs,
  joined_mem c L -> joined_covers bs L ->
  exists d, In d bs /\ cjoin c (phi_erase d).
Proof.
 intros c L bs Hm Hcov. revert Hm.
 induction Hcov as [L A HL | L A d R HL [b [Hb Hbd]] Htail IH]; intro Hm.
 - exfalso.
   apply joined_mem_nil_absurd with (c:=c) (A:=A).
   eapply joined_mem_transport; [exact Hm|exact HL].
 - pose proof (joined_mem_transport c L Hm (TLCons A d R) HL) as Hmx.
   destruct (joined_mem_cons_inv c A d R Hmx) as [Hcd|Hmt].
   + exists b. split; [exact Hb|].
     eapply cjoin_trans; [exact Hcd|apply cjoin_sym; exact Hbd].
   + exact (IH Hmt).
Qed.

Print Assumptions joined_mem_nil_absurd.
Print Assumptions joined_mem_covered.
