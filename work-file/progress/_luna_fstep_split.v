Require Import Progress _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epbranches_replace_label_luna : forall bs1 c c' b bs2,
    epstep c c' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b) :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c c' b bs2 Hcc'; cbn.
  - constructor; [exact Hcc' | apply epstep_refl | apply epbranches_refl].
  - constructor;
      [apply epstep_refl | apply epstep_refl | apply IH; exact Hcc'].
Qed.

Lemma pbranches_replace_body_luna : forall bs1 c b b' bs2,
    pstep b b' ->
    pbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c,b') :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c b b' bs2 Hbb'; cbn.
  - constructor; [apply pstep_refl | exact Hbb' | apply pbranches_refl].
  - constructor;
      [apply pstep_refl | apply pstep_refl | apply IH; exact Hbb'].
Qed.

Lemma epbranches_replace_body_luna : forall bs1 c b b' bs2,
    epstep b b' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c,b') :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c b b' bs2 Hbb'; cbn.
  - constructor; [apply epstep_refl | exact Hbb' | apply epbranches_refl].
  - constructor;
      [apply epstep_refl | apply epstep_refl | apply IH; exact Hbb'].
Qed.

Lemma fstep_pstep_or_epstep : forall t u,
    fstep t u -> pstep t u \/ epstep t u.
Proof.
  intros t u H.
  induction H;
    try solve [left; apply step_pstep; exact H];
    try solve [right; apply eps_eta; apply epstep_refl];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; econstructor; eauto using pstep_refl, pbranches_refl
      | right; econstructor; eauto using epstep_refl, epbranches_refl ]
    ];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; eapply ps_case; eauto using pstep_refl, pbranches_refl;
        apply pbranches_replace_label; exact Hp
      | right; eapply eps_case; eauto using epstep_refl, epbranches_refl;
        apply epbranches_replace_label_luna; exact He ]
    ];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; eapply ps_case; eauto using pstep_refl, pbranches_refl;
        apply pbranches_replace_body_luna; exact Hp
      | right; eapply eps_case; eauto using epstep_refl, epbranches_refl;
        apply epbranches_replace_body_luna; exact He ]
    ].
Qed.
