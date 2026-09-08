Require Import Progress SignatureInstances SignatureConversion _parent_instance_pruning.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.
Import Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma instance_translate_eval_luna : forall t u, eval t u ->
  eval (instance_translate t) (instance_translate u).
Proof.
  intros t u H; induction H as [t|t v u Hstep Heval IH].
  - apply ev_refl.
  - eapply ev_step; [apply instance_translate_step; exact Hstep|exact IH].
Qed.

Lemma instance_translate_eval_fconv_luna : forall t u, eval t u ->
  fconv (instance_translate t) (instance_translate u).
Proof.
  intros t u H; induction H as [t|t v u Hstep Heval IH].
  - apply fc_refl.
  - eapply fc_trans; [apply instance_translate_fstep; apply fs_step; exact Hstep|exact IH].
Qed.

Lemma fconv_lcons_tail_luna : forall A c L L',
  fconv L L' -> fconv (TLCons A c L) (TLCons A c L').
Proof.
  intros A c L L' H.
  apply (fconv_map (fun z => TLCons A c z)).
  intros x y Hxy. apply fs_lcons3. exact Hxy.
  exact H.
Qed.

Lemma instance_dead_translate_luna : forall D,
  desc_against D -> instance_dead (instance_translate D).
Proof.
  intros D HD. exists D. split; [exact HD|].
  exists (phi_erase D). split.
  - apply rtc_one. apply epstep_cstep. apply instance_translate_erased_eta.
  - apply rtc_refl.
Qed.

Lemma instance_phi_spine_aux : forall Sf i Phi Psi,
  spine_phi Sf i Phi Psi ->
  exists L0,
    fconv (instance_translate Phi) L0  /\
    prune_labels
      (branches (TApp (instance_translate Sf) (instance_translate i)))
      L0 (instance_translate Psi).
Proof.
  intros Sf i Phi Psi H; induction H.
  - exists (instance_translate (TLNil A)). split.
    + apply instance_translate_eval_fconv_luna. exact H.
    + apply pl_stop. apply prune_term_refl.
  - destruct IHspine_phi as [L0 [Hf Hp]].
    exists (TLCons (instance_translate A) (instance_translate c) L0).
    split.
    + eapply fc_trans.
      * apply instance_translate_eval_fconv_luna. exact H.
      * apply fconv_lcons_tail_luna. exact Hf.
    + apply pl_keep; try apply prune_term_refl. exact Hp.
  - destruct IHspine_phi as [L0 [Hf Hp]].
    exists (TLCons (instance_translate A) (instance_translate c) L0). split.
    + eapply fc_trans.
      * apply instance_translate_eval_fconv_luna. exact H.
      * apply fconv_lcons_tail_luna. exact Hf.
    + apply pl_drop.
      * change (instance_dead (instance_translate (TApp (branches (TApp Sf i)) c))).
        apply instance_dead_translate_luna. exact H0.
      * exact Hp.
  - exists (instance_translate Phin). split.
    + apply instance_translate_eval_fconv_luna. exact H.
    + apply pl_stop. apply prune_term_refl.
Qed.

Theorem instance_phi_spine_luna : forall Sf i Phi Psi,
  spine_phi Sf i Phi Psi ->
  exists L0, fconv (instance_translate Phi) L0  /\
    prune_labels (branches (TApp (instance_translate Sf) (instance_translate i)))
      L0 (instance_translate Psi).
Proof. exact instance_phi_spine_aux. Qed.

Print Assumptions instance_phi_spine_luna.
