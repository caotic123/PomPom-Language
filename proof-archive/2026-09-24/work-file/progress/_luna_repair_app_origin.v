Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma luna_check_mui_synth : forall G t T,
    check G t T ->
    forall R, t = TMuI R ->
    exists IT, synth G (TMuI R) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/
                sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Rq Ht; subst; try discriminate.
  - inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - inversion H; subst. eexists. split; [eassumption | right; eassumption].
  - destruct (IHHck Rq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + left. eapply cv_trans; [exact Hrel | apply cv_sym; exact H].
    + right. eapply su_trans; [exact Hrel | apply su_conv, cv_sym, H].
Qed.

Lemma luna_check_mus_synth : forall G t T,
    check G t T ->
    forall Sf, t = TMuS Sf ->
    exists IT, synth G (TMuS Sf) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/
                sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Sfq Ht; subst; try discriminate.
  - inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - inversion H; subst. eexists. split; [eassumption | right; eassumption].
  - destruct (IHHck Sfq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + left. eapply cv_trans; [exact Hrel | apply cv_sym; exact H].
    + right. eapply su_trans; [exact Hrel | apply su_conv, cv_sym, H].
Qed.

Lemma mu_former_checked_erased_pi_origin_luna : forall G f A B,
    (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf) ->
    check G f (TPi A B) ->
    exists IT, sub G (TPi IT (TSort 0)) (TPi A B).
Proof.
  intros G f A B [ [R ->] | [Sf ->] ] Hf.
  - destruct (luna_check_mui_synth G (TMuI R) (TPi A B) Hf R eq_refl)
      as [IT [Hsyn [Hconv | Hsub]]].
    + exists IT. apply su_conv. exact Hconv.
    + exists IT. exact Hsub.
  - destruct (luna_check_mus_synth G (TMuS Sf) (TPi A B) Hf Sf eq_refl)
      as [IT [Hsyn [Hconv | Hsub]]].
    + exists IT. apply su_conv. exact Hconv.
    + exists IT. exact Hsub.
Qed.

Print Assumptions mu_former_checked_erased_pi_origin_luna.
