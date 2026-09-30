Require Import Progress SignatureInstances SignatureConversion ErasureCounterexample _parent_instance_pruning _luna_instance_phi_spine.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.
Import Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Inductive instance_conv : term -> term -> Prop :=
| ic_core : forall t u, fconv t u -> instance_conv t u
| ic_prune : forall t u, prune_term t u -> instance_conv t u
| ic_refl : forall t, instance_conv t t
| ic_sym : forall t u, instance_conv t u -> instance_conv u t
| ic_trans : forall t u v, instance_conv t u -> instance_conv u v -> instance_conv t v.

Lemma ic_map : forall (F : term -> term),
  (forall x y, fstep x y -> fstep (F x) (F y)) ->
  (forall x y, prune_term x y -> prune_term (F x) (F y)) ->
  forall x y, instance_conv x y -> instance_conv (F x) (F y).
Proof.
  intros F HF HP x y H; induction H.
  - apply ic_core. eapply fconv_map; [exact HF | exact H].
  - apply ic_prune. eauto.
  - apply ic_refl.
  - apply ic_sym. exact IHinstance_conv.
  - eapply ic_trans; eauto.
Qed.

Lemma ic_map2 : forall (F : term -> term -> term),
  (forall x y z, fstep x y -> fstep (F x z) (F y z)) ->
  (forall z x y, fstep x y -> fstep (F z x) (F z y)) ->
  (forall x y z, prune_term x y -> prune_term (F x z) (F y z)) ->
  (forall z x y, prune_term x y -> prune_term (F z x) (F z y)) ->
  forall x x' y y', instance_conv x x' -> instance_conv y y' ->
    instance_conv (F x y) (F x' y').
Proof.
  intros F Hf1 Hf2 Hp1 Hp2 x x' y y' Hx Hy.
  eapply ic_trans.
  - eapply (ic_map (fun z => F z y)
        (fun a b H => Hf1 a b y H)
        (fun a b H => Hp1 a b y H)); exact Hx.
  - eapply (ic_map (fun z => F x' z)
        (fun a b H => Hf2 x' a b H)
        (fun a b H => Hp2 x' a b H)); exact Hy.
Qed.

Lemma ic_lift : forall t u, instance_conv t u -> forall d k,
  instance_conv (lift d k t) (lift d k u).
Proof.
  intros t u H; induction H; intros d k.
  - apply ic_core. apply fconv_lift_parent. exact H.
  - apply ic_prune. apply prune_lift. exact H.
  - apply ic_refl.
  - apply ic_sym. exact (IHinstance_conv d k).
  - eapply ic_trans; [exact (IHinstance_conv1 d k)|exact (IHinstance_conv2 d k)].
Qed.

Print Assumptions ic_map.
Print Assumptions ic_map2.
Print Assumptions ic_lift.

Lemma ic_signature_prune : forall Sf i Phi Psi,
  eval (labels (TApp Sf i)) Phi ->
  spine_phi Sf i Phi Psi ->
  instance_conv (instance_translate (TApp (TMuS Sf) i))
    (signature_instance
      (branches (TApp (instance_translate Sf) (instance_translate i)))
      (instance_translate Psi) (instance_translate i)).
Proof.
  intros Sf i Phi Psi Heval Hsp.
  destruct (instance_phi_spine_luna Sf i Phi Psi Hsp)
    as [L0 [Hf Hpl]].
  pose proof (instance_translate_musapp Sf i) as Hstep.
  assert (Hbase : instance_conv
      (instance_translate (TApp (TMuS Sf) i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (labels (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate i))).
  { apply ic_core. apply fc_step. apply fs_step. exact Hstep. }
  assert (Htranslated : fconv
      (labels (TApp (instance_translate Sf) (instance_translate i)))
      (instance_translate Phi)).
  { pose proof (instance_translate_eval_fconv_luna _ _ Heval) as Htmp.
    cbn [instance_translate] in Htmp. exact Htmp. }
  assert (Hlabels : instance_conv
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (labels (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        L0 (instance_translate i))).
  { apply (ic_map
      (fun z => signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        z (instance_translate i))).
    - intros x y Hxy. apply fs_app1. apply fs_mus. apply fs_pair2. exact Hxy.
    - intros x y Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair; [apply prune_term_refl | exact Hxy].
      + exact (prune_term_refl _).
    - eapply ic_trans.
      + apply ic_core. exact Htranslated.
      + apply ic_core. exact Hf. }
  assert (Hprune : instance_conv
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        L0 (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate Psi) (instance_translate i))).
  { apply ic_prune. apply pt_app.
    - apply pt_instance; [apply prune_term_refl | exact Hpl].
    - apply prune_term_refl. }
  eapply ic_trans; [exact Hbase|].
  eapply ic_trans; [exact Hlabels|exact Hprune].
Qed.

Print Assumptions ic_signature_prune.


Lemma instance_branch_beta : forall S i,
  fconv
    (TApp (instance_translate
      (TLam (branches (TApp (lift 1 0 S) (TVar 0)))))
      (instance_translate i))
    (branches (TApp (instance_translate S) (instance_translate i))).
Proof.
  intros S i.
  cbn [instance_translate branches].
  rewrite instance_translate_lift.
  pose proof (st_beta
    (TFst (TApp (lift 1 0 (instance_translate S)) (TVar 0)))
    (instance_translate i)) as H.
  cbn [subst] in H.
  rewrite subst_lift_zero in H.
  rewrite Progress._tmp_commute.lift_zero_id_local in H.
  apply fc_step. apply fs_step. exact H.
Qed.

Print Assumptions instance_branch_beta.

Lemma ic_phi : forall S1 S2 i Phi1 Phi2 Psi1 Psi2,
  instance_conv
    (instance_translate (TLam (branches (TApp (lift 1 0 S1) (TVar 0)))))
    (instance_translate (TLam (branches (TApp (lift 1 0 S2) (TVar 0))))) ->
  eval (labels (TApp S1 i)) Phi1 ->
  eval (labels (TApp S2 i)) Phi2 ->
  spine_phi S1 i Phi1 Psi1 ->
  spine_phi S2 i Phi2 Psi2 ->
  instance_conv (instance_translate Psi1) (instance_translate Psi2) ->
  instance_conv (instance_translate (TApp (TMuS S1) i))
    (instance_translate (TApp (TMuS S2) i)).
Proof.
  intros S1 S2 i Phi1 Phi2 Psi1 Psi2 Hbranch He1 He2 Hp1 Hp2 Hpsi.
  pose proof (ic_signature_prune S1 i Phi1 Psi1 He1 Hp1) as Hleft.
  pose proof (ic_signature_prune S2 i Phi2 Psi2 He2 Hp2) as Hright.
  assert (HB : instance_conv
      (branches (TApp (instance_translate S1) (instance_translate i)))
      (branches (TApp (instance_translate S2) (instance_translate i)))).
  { eapply ic_trans.
    - apply ic_sym. apply ic_core. apply instance_branch_beta.
    - eapply ic_trans.
      + apply (ic_map (fun z => TApp z (instance_translate i))).
        * intros x y Hxy. apply fs_app1. exact Hxy.
        * intros x y Hxy. apply pt_app; [exact Hxy|apply prune_term_refl].
        * exact Hbranch.
      + apply ic_core. apply instance_branch_beta. }
  assert (Hmid : instance_conv
      (signature_instance
        (branches (TApp (instance_translate S1) (instance_translate i)))
        (instance_translate Psi1) (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate S2) (instance_translate i)))
        (instance_translate Psi2) (instance_translate i))).
  { apply (ic_map2 (fun B L => signature_instance B L (instance_translate i))).
    - intros x y z Hxy. apply fs_app1. apply fs_mus. apply fs_pair1. exact Hxy.
    - intros z x y Hxy. apply fs_app1. apply fs_mus. apply fs_pair2. exact Hxy.
    - intros x y z Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair.
        * exact Hxy.
        * exact (prune_term_refl _).
      + exact (prune_term_refl _).
    - intros z x y Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair.
        * exact (prune_term_refl _).
        * exact Hxy.
      + exact (prune_term_refl _).
    - exact HB.
    - exact Hpsi. }
  eapply ic_trans; [exact Hleft|].
  eapply ic_trans; [exact Hmid|].
  apply ic_sym. exact Hright.
Qed.

Print Assumptions ic_phi.


Lemma ic_map3 : forall (F : term -> term -> term -> term),
 (forall x y z q, fstep x y -> fstep (F x z q) (F y z q)) ->
 (forall z x y q, fstep x y -> fstep (F z x q) (F z y q)) ->
 (forall z q x y, fstep x y -> fstep (F z q x) (F z q y)) ->
 (forall x y z q, prune_term x y -> prune_term (F x z q) (F y z q)) ->
 (forall z x y q, prune_term x y -> prune_term (F z x q) (F z y q)) ->
 (forall z q x y, prune_term x y -> prune_term (F z q x) (F z q y)) ->
 forall x x' y y' z z', instance_conv x x' -> instance_conv y y' -> instance_conv z z' ->
 instance_conv (F x y z) (F x' y' z').
Proof.
 intros F H1 H2 H3 P1 P2 P3 x x' y y' z z' Hx Hy Hz.
 eapply ic_trans.
 - eapply (ic_map (fun a => F a y z)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Hx].
 - eapply ic_trans.
   + eapply (ic_map (fun b => F x' b z)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hy].
   + eapply (ic_map (fun c => F x' y' c)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hz].
Qed.

Lemma ic_map4 : forall (F : term -> term -> term -> term -> term),
 (forall x y a b q, fstep x y -> fstep (F x a b q) (F y a b q)) ->
 (forall a x y b q, fstep x y -> fstep (F a x b q) (F a y b q)) ->
 (forall a b x y q, fstep x y -> fstep (F a b x q) (F a b y q)) ->
 (forall a b q x y, fstep x y -> fstep (F a b q x) (F a b q y)) ->
 (forall x y a b q, prune_term x y -> prune_term (F x a b q) (F y a b q)) ->
 (forall a x y b q, prune_term x y -> prune_term (F a x b q) (F a y b q)) ->
 (forall a b x y q, prune_term x y -> prune_term (F a b x q) (F a b y q)) ->
 (forall a b q x y, prune_term x y -> prune_term (F a b q x) (F a b q y)) ->
 forall a a' b b' c c' d d', instance_conv a a' -> instance_conv b b' -> instance_conv c c' -> instance_conv d d' ->
 instance_conv (F a b c d) (F a' b' c' d').
Proof.
 intros F H1 H2 H3 H4 P1 P2 P3 P4 a a' b b' c c' d d' Ha Hb Hc Hd.
 eapply ic_trans.
 - eapply (ic_map (fun x => F x b c d)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Ha].
 - eapply ic_trans.
   + eapply (ic_map (fun x => F a' x c d)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hb].
   + eapply ic_trans.
     * eapply (ic_map (fun x => F a' b' x d)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hc].
     * eapply (ic_map (fun x => F a' b' c' x)); [intros; eapply H4; eauto|intros; eapply P4; eauto|exact Hd].
Qed.

Lemma ic_map5 : forall (F : term -> term -> term -> term -> term -> term),
 (forall x y a b c q, fstep x y -> fstep (F x a b c q) (F y a b c q)) ->
 (forall a x y b c q, fstep x y -> fstep (F a x b c q) (F a y b c q)) ->
 (forall a b x y c q, fstep x y -> fstep (F a b x c q) (F a b y c q)) ->
 (forall a b c x y q, fstep x y -> fstep (F a b c x q) (F a b c y q)) ->
 (forall a b c q x y, fstep x y -> fstep (F a b c q x) (F a b c q y)) ->
 (forall x y a b c q, prune_term x y -> prune_term (F x a b c q) (F y a b c q)) ->
 (forall a x y b c q, prune_term x y -> prune_term (F a x b c q) (F a y b c q)) ->
 (forall a b x y c q, prune_term x y -> prune_term (F a b x c q) (F a b y c q)) ->
 (forall a b c x y q, prune_term x y -> prune_term (F a b c x q) (F a b c y q)) ->
 (forall a b c q x y, prune_term x y -> prune_term (F a b c q x) (F a b c q y)) ->
 forall a a' b b' c c' d d' e e', instance_conv a a' -> instance_conv b b' -> instance_conv c c' -> instance_conv d d' -> instance_conv e e' ->
 instance_conv (F a b c d e) (F a' b' c' d' e').
Proof.
 intros F H1 H2 H3 H4 H5 P1 P2 P3 P4 P5 a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
 eapply ic_trans.
 - eapply (ic_map (fun x => F x b c d e)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Ha].
 - eapply ic_trans.
   + eapply (ic_map (fun x => F a' x c d e)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hb].
   + eapply ic_trans.
     * eapply (ic_map (fun x => F a' b' x d e)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hc].
     * eapply ic_trans.
       -- eapply (ic_map (fun x => F a' b' c' x e)); [intros; eapply H4; eauto|intros; eapply P4; eauto|exact Hd].
       -- eapply (ic_map (fun x => F a' b' c' d' x)); [intros; eapply H5; eauto|intros; eapply P5; eauto|exact He].
Qed.

Print Assumptions ic_map3.
Print Assumptions ic_map4.
Print Assumptions ic_map5.

Lemma ic_translate_mus : forall S S',
  instance_conv (instance_translate S) (instance_translate S') ->
  instance_conv (instance_translate (TMuS S)) (instance_translate (TMuS S')).
Proof.
  intros S S' H.
  cbn [instance_translate].
  pose proof (ic_lift _ _ H 1 0) as Hl.
  assert (Hp : instance_conv
      (TPair
        (TFst (TApp (lift 1 0 (instance_translate S)) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate S)) (TVar 0))))
      (TPair
        (TFst (TApp (lift 1 0 (instance_translate S')) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate S')) (TVar 0))))).
  { apply (ic_map2 (fun a b => TPair
        (TFst (TApp a (TVar 0))) (TSnd (TApp b (TVar 0))))).
    - intros x y z Hxy. apply fs_pair1. apply fs_fst. apply fs_app1. exact Hxy.
    - intros z x y Hxy. apply fs_pair2. apply fs_snd. apply fs_app1. exact Hxy.
    - intros x y z Hxy. apply pt_pair.
      + apply pt_fst. apply pt_app.
        * exact Hxy.
        * exact (prune_term_refl _).
      + exact (prune_term_refl _).
    - intros z x y Hxy. apply pt_pair.
      + exact (prune_term_refl _).
      + apply pt_snd. apply pt_app.
        * exact Hxy.
        * exact (prune_term_refl _).
    - exact Hl. - exact Hl. }
  apply (ic_map (fun p => TLam (TApp (TMuS p) (TVar 0)))).
  - intros x y Hxy. apply fs_lam. apply fs_app1. apply fs_mus. exact Hxy.
  - intros x y Hxy. apply pt_lam. apply pt_app.
    + apply pt_mus. exact Hxy.
    + exact (prune_term_refl _).
  - exact Hp.
Qed.

Print Assumptions ic_translate_mus.
