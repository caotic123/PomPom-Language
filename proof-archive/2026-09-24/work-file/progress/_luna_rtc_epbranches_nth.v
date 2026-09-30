Require Import Progress _tmp_epstep _tmp_epbranches_nth _work_epstep_rtc.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* A branch tag can move along epstep (the eta constructor is an
   explicit counterexample to tag preservation), so the sound closure
   statement keeps the endpoint tag and records its epstep path. *)
Lemma rtc_epbranches_nth_error_fwd_luna :
    forall bs bs' k c b,
      rtc epbranches bs bs' ->
      nth_error bs k = Some (c,b) ->
      exists c' b',
        nth_error bs' k = Some (c',b') /\
        rtc epstep c c' /\ rtc epstep b b'.
Proof.
  intros bs bs' k c b Hrtc.
  revert k c b.
  induction Hrtc as [bs | bs bs1 bs' Hhead Htail IH].
  - intros k c b Hnth.
    exists c, b. repeat split; [exact Hnth | apply rtc_refl | apply rtc_refl].
  - intros k c b Hnth.
    (* First transport the selected entry through the one-step branch
       relation, then apply the induction hypothesis to the tail. *)
    destruct (epbranches_nth_error bs bs1 k c b Hhead Hnth)
      as [c1 [b1 [Hidx1 [Hc1 Hb1]]]].
    destruct (IH k c1 b1 Hidx1)
      as [c' [b' [Hidx [Hc' Hb']]]].
    eexists c', b'. repeat split; [exact Hidx | |].
    + eapply rtc_trans; [exact (rtc_step Hc1 rtc_refl) | exact Hc'].
    + eapply rtc_trans; [exact (rtc_step Hb1 rtc_refl) | exact Hb'].
Qed.

(* The exact same-tag corollary is valid once the tag is known to be an
   enum position.  This is the form used by case-selection arguments. *)
Lemma epstep_enum_pos_id_luna : forall c c' n,
    epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hstep Hpos. revert c' Hstep.
  induction Hpos as [|c n Hpos IH]; intros c' Hstep.
  - inversion Hstep; reflexivity.
  - inversion Hstep; subst; f_equal; eauto.
Qed.

Lemma rtc_epstep_enum_pos_id_luna : forall c c' n,
    rtc epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hrtc Hpos. revert n Hpos.
  induction Hrtc as [c | c d c' Hstep Htail IH].
  - intros n Hpos; reflexivity.
  - intros n Hpos.
    pose proof (epstep_enum_pos_id_luna c d n Hstep Hpos) as Hcd.
    subst d. exact (IH n Hpos).
Qed.

Lemma rtc_epbranches_nth_error_fwd_tag_luna :
    forall bs bs' k c b n,
      rtc epbranches bs bs' ->
      nth_error bs k = Some (c,b) ->
      enum_pos c n ->
      exists b',
        nth_error bs' k = Some (c,b') /\ rtc epstep b b'.
Proof.
  intros bs bs' k c b n Hrtc Hnth Hpos.
  destruct (rtc_epbranches_nth_error_fwd_luna bs bs' k c b Hrtc Hnth)
    as [c' [b' [Hidx [Hc Hb]]]].
  pose proof (rtc_epstep_enum_pos_id_luna c c' n Hc Hpos) as Heq.
  subst c'. eexists; split; [exact Hidx | exact Hb].
Qed.
