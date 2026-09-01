Require Import TypeRules Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Lemma pstep_case_complete_aux : forall M M' Q Q' bs bs',
    pstep M M' -> pstep M' (pdev M) ->
    pstep Q Q' -> pstep Q' (pdev Q) ->
    pbranches bs bs' ->
    pbranches bs' (map (fun '(c,b) => (pdev c, pdev b)) bs) ->
    pstep (TCase M' Q' bs') (pdev (TCase M Q bs)).
Proof.
  intros M M' Q Q' bs bs' HM HMdev HQ HQdev Hbs Hbsdev.
  destruct M; cbn;
    try solve [eapply ps_case; eauto].
  let z := match goal with
    | Hr : pstep (TIn ?z) _ |- _ => constr:(z)
    end in destruct z; cbn;
    try solve [eapply ps_case; eauto].
  inversion HM; subst.
  match goal with Hr : pstep (TPair _ _) _ |- _ =>
    inversion Hr; clear Hr; subst
  end.
  cbn in HMdev. inversion HMdev; subst.
  match goal with Hr : pstep (TPair _ _) (TPair _ _) |- _ =>
    inversion Hr; clear Hr; subst
  end.
  match goal with |- context [enum_index ?aa] =>
    destruct (enum_index aa) as [n|] eqn:Hidx
  end.
  - rewrite first_branch_map_body.
    destruct (first_branch n bs) as [b0|] eqn:Hfirst.
    + destruct (first_branch_some n bs b0 Hfirst)
        as [k [c [Hnth [Hpos Hpre]]]].
      destruct (pbranches_nth_error bs bs' k c b0 Hbs Hnth)
        as [csel [bsel [Hnth' [Hcc' Hbb']]]].
      assert (Hc' : csel = c) by
        (eapply pstep_enum_pos_id; eauto).
      subst csel.
      destruct (pbranches_nth_error bs'
          (map (fun '(c,b) => (pdev c, pdev b)) bs)
          k c bsel Hbsdev Hnth')
        as [cd [bd [Hnthdev [Hccd Hbbd]]]].
      assert (Hmapnth :
        nth_error (map (fun '(c,b) => (pdev c, pdev b)) bs) k =
          Some (pdev c, pdev b0)).
      { rewrite nth_error_map, Hnth. reflexivity. }
      rewrite Hmapnth in Hnthdev. inversion Hnthdev; subst cd bd.
      pose proof (enum_index_sound _ _ Hidx) as Htpos.
      match type of Htpos with enum_pos ?aa n =>
        match goal with Hat : pstep aa ?ta |- _ =>
          assert (Heqa : ta = aa) by
            (eapply pstep_enum_pos_id; [exact Hat | exact Htpos]);
          subst ta
        end
      end.
      eapply ps_case_red with (k:=k) (c:=c) (b:=bsel) (n:=n).
      * exact Hnth'.
      * exact Hpos.
      * exact Htpos.
      * intros j cj' bj' Hj Hnthj'.
        destruct (pbranches_nth_error_rev bs bs' j cj' bj' Hbs Hnthj')
          as [cj [bj [Hnthj [Hcjcj' Hbjbj']]]].
        destruct (Hpre j cj bj Hj Hnthj) as [nj [Hjpos Hneq]].
        assert (Heqcj : cj' = cj) by
          (eapply pstep_enum_pos_id; eauto).
        subst cj'. exists nj. auto.
      * eauto.
      * exact Hbbd.
    + eapply ps_case; eauto.
  - eapply ps_case; eauto.
Qed.
