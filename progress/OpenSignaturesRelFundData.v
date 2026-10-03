(* Fundamental lemma: description interpretation, inductive families and
   close types. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelFundBase.
Import ListNotations.

Lemma FP_at : forall Gamma t A g1 g2 A1 A2, FP Gamma t A -> closing2 Gamma g1 g2 ->
  conv (instantiate g1 A) A1 -> conv (instantiate g2 A) A2 ->
  rel_at (instantiate g1 t) (instantiate g2 t) A1 A2.
Proof. intros; eapply rel_at_conv; [eauto|apply cv_refl|apply cv_refl|eassumption|eassumption]. Qed.

Ltac cl Hc H := let a := fresh "Hcl" in let b := fresh "Hcl" in
  destruct (inst_closed_typed _ _ _ _ _ Hc H) as [a b].

Lemma FP_small : forall Gamma IT g1 g2, FP Gamma IT (TSort 0) -> closing2 Gamma g1 g2 ->
  rel_at (instantiate g1 IT) (instantiate g2 IT) (TSort 0) (TSort 0).
Proof. intros; eapply FP_at; [eassumption|eassumption|rewrite instantiate_sort; apply cv_refl|rewrite instantiate_sort; apply cv_refl]. Qed.

Lemma FP_family : forall Gamma X IT g1 g2, FP Gamma X (Family IT) -> closing2 Gamma g1 g2 ->
  typing Gamma IT (TSort 0) ->
  rel_at (instantiate g1 X) (instantiate g2 X) (Family (instantiate g1 IT)) (Family (instantiate g2 IT)).
Proof.
  intros Gamma X IT g1 g2 I Hc HIT. envs Hc. cl Hc HIT.
  eapply FP_at; [eassumption|eassumption| |]; apply inst_Family; assumption.
Qed.
Lemma FP_def : forall Gamma D IT g1 g2, FP Gamma D (Def IT) -> closing2 Gamma g1 g2 ->
  typing Gamma IT (TSort 0) ->
  rel_at (instantiate g1 D) (instantiate g2 D) (Def (instantiate g1 IT)) (Def (instantiate g2 IT)).
Proof.
  intros Gamma D IT g1 g2 I Hc HIT. envs Hc. cl Hc HIT.
  eapply FP_at; [eassumption|eassumption| |]; apply inst_Def; assumption.
Qed.

Lemma fund_interp : forall Gamma IT D X, FP Gamma IT (TSort 0) -> FP Gamma D (TIDesc IT) ->
  FP Gamma X (Family IT) -> typing Gamma IT (TSort 0) -> FP Gamma (TInterp IT D X) (TSort 0).
Proof.
  intros Gamma IT D X IIT ID IX HIT g1 g2 Hc.
  pose proof (ID _ _ Hc) as HD; rewrite !inst_idesc in HD.
  rewrite inst_tinterp, inst_tinterp, !instantiate_sort.
  apply sem_interp_rule; [apply (FP_small _ _ _ _ IIT Hc)|exact HD|apply (FP_family _ _ _ _ _ IX Hc HIT)].
Qed.

Lemma fund_mui : forall Gamma IT D, FP Gamma IT (TSort 0) -> FP Gamma D (Def IT) ->
  typing Gamma IT (TSort 0) -> FP Gamma (TMuI IT D) (Family IT).
Proof.
  intros Gamma IT D IIT ID HIT g1 g2 Hc. envs Hc. cl Hc HIT.
  eapply rel_at_conv; [|apply cv_refl|apply cv_refl|apply cv_sym, inst_Family; assumption
    |apply cv_sym, inst_Family; assumption].
  rewrite !inst_mui. apply sem_mui; [apply (FP_small _ _ _ _ IIT Hc)|apply (FP_def _ _ _ _ _ ID Hc HIT)].
Qed.

Lemma fund_in_mui : forall Gamma IT D i xs, FP Gamma IT (TSort 0) -> FP Gamma D (Def IT) ->
  typing Gamma i IT -> FP Gamma i IT -> typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D)) ->
  FP Gamma xs (TInterp IT (TApp D i) (TMuI IT D)) -> typing Gamma IT (TSort 0) ->
  FP Gamma (TIn xs) (MuAt IT D i).
Proof.
  intros Gamma IT D i xs IIT ID Hi Ii Hx Ix HIT g1 g2 Hc. cl Hc Hi. cl Hc Hx.
  pose proof (Ix _ _ Hc) as Hxs. rewrite !inst_tinterp, !instantiate_app, !inst_mui in Hxs.
  rewrite !inst_tin, !inst_MuAt.
  apply sem_in_mu; try assumption; [apply (FP_small _ _ _ _ IIT Hc)|apply (FP_def _ _ _ _ _ ID Hc HIT)|exact (Ii _ _ Hc)].
Qed.

Lemma fund_close : forall Gamma IT F G, FP Gamma IT (TSort 0) -> FP Gamma F (Def IT) ->
  FP Gamma G (Def IT) -> typing Gamma IT (TSort 0) -> FP Gamma (TClose IT F G) (Family IT).
Proof.
  intros Gamma IT F G IIT IF IG HIT g1 g2 Hc. envs Hc. cl Hc HIT.
  eapply rel_at_conv; [|apply cv_refl|apply cv_refl|apply cv_sym, inst_Family; assumption
    |apply cv_sym, inst_Family; assumption].
  rewrite !inst_tclose. apply sem_close; [apply (FP_small _ _ _ _ IIT Hc)
    |apply (FP_def _ _ _ _ _ IF Hc HIT)|apply (FP_def _ _ _ _ _ IG Hc HIT)].
Qed.

Lemma fund_in_close : forall Gamma IT F G i xs, FP Gamma IT (TSort 0) -> FP Gamma F (Def IT) ->
  FP Gamma G (Def IT) -> typing Gamma i IT -> FP Gamma i IT ->
  typing Gamma xs (payload IT F G i) -> FP Gamma xs (payload IT F G i) -> typing Gamma IT (TSort 0) ->
  FP Gamma (TIn xs) (CloseAt IT F G i).
Proof.
  intros Gamma IT F G i xs IIT IF IG Hi Ii Hx Ix HIT g1 g2 Hc. envs Hc. cl Hc Hi. cl Hc Hx.
  pose proof (Ix _ _ Hc) as Hxs. rewrite !inst_payload in Hxs by assumption.
  rewrite !inst_tin, !inst_CloseAt by assumption.
  apply sem_in_close; try assumption; [apply (FP_small _ _ _ _ IIT Hc)|apply (FP_def _ _ _ _ _ IF Hc HIT)
    |apply (FP_def _ _ _ _ _ IG Hc HIT)|exact (Ii _ _ Hc)].
Qed.

Lemma fund_iall : forall Gamma IT D X xs P, FP Gamma IT (TSort 0) -> FP Gamma D (TIDesc IT) ->
  FP Gamma X (Family IT) -> typing Gamma xs (TInterp IT D X) -> FP Gamma xs (TInterp IT D X) ->
  typing Gamma P (motive IT X) -> FP Gamma P (motive IT X) ->
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  FP Gamma (TIAll IT D X xs P) (TSort 0).
Proof.
  intros Gamma IT D X xs P IIT ID IX Hx Ix HP IP HIT HX g1 g2 Hc. envs Hc.
  cl Hc Hx. cl Hc HIT. cl Hc HX.
  pose proof (ID _ _ Hc) as HD; rewrite !inst_idesc in HD.
  pose proof (Ix _ _ Hc) as Hxs; rewrite !inst_tinterp in Hxs.
  rewrite !inst_iall, !instantiate_sort.
  eapply sem_iall_rule; try eassumption; [apply (FP_small _ _ _ _ IIT Hc)|apply (FP_family _ _ _ _ _ IX Hc HIT)|].
  eapply FP_at; [exact IP|exact Hc| |]; apply inst_motive; assumption.
Qed.

Lemma fund_hyps : forall Gamma IT D X P h xs, FP Gamma IT (TSort 0) -> FP Gamma D (TIDesc IT) ->
  FP Gamma X (Family IT) -> typing Gamma P (motive IT X) -> FP Gamma P (motive IT X) ->
  typing Gamma h (recursive_method IT X P) -> FP Gamma h (recursive_method IT X P) ->
  typing Gamma xs (TInterp IT D X) -> FP Gamma xs (TInterp IT D X) ->
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  FP Gamma (THyps IT D X P h xs) (TIAll IT D X xs P).
Proof.
  intros Gamma IT D X P h xs IIT ID IX HP IP Hh Ih Hx Ix HIT HX g1 g2 Hc. envs Hc.
  cl Hc Hx. cl Hc HIT. cl Hc HX. cl Hc HP. cl Hc Hh.
  pose proof (ID _ _ Hc) as HD; rewrite !inst_idesc in HD.
  pose proof (Ix _ _ Hc) as Hxs; rewrite !inst_tinterp in Hxs.
  rewrite !inst_hyps, !inst_iall.
  eapply sem_hyps_rule; try eassumption; [apply (FP_small _ _ _ _ IIT Hc)|apply (FP_family _ _ _ _ _ IX Hc HIT)| |].
  - eapply FP_at; [exact IP|exact Hc| |]; apply inst_motive; assumption.
  - eapply FP_at; [exact Ih|exact Hc| |]; apply inst_recursive_method; assumption.
Qed.

Lemma fund_ind : forall Gamma IT D P st i x, FP Gamma IT (TSort 0) -> FP Gamma D (Def IT) ->
  typing Gamma P (motive IT (TMuI IT D)) -> FP Gamma P (motive IT (TMuI IT D)) ->
  typing Gamma st (mu_ind_method IT D P) -> FP Gamma st (mu_ind_method IT D P) ->
  typing Gamma i IT -> FP Gamma i IT -> typing Gamma x (MuAt IT D i) -> FP Gamma x (MuAt IT D i) ->
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
  FP Gamma (TInd IT D P st i x) (TApp P (TPair i x)).
Proof.
  intros Gamma IT D P st i x IIT ID HP IP Hs Is Hi Ii Hx Ix HIT HD g1 g2 Hc. envs Hc.
  cl Hc HIT. cl Hc HD. cl Hc HP. cl Hc Hs. cl Hc Hi. cl Hc Hx.
  pose proof (Ix _ _ Hc) as Hx'; rewrite !inst_MuAt in Hx'.
  rewrite !inst_tind, !instantiate_app, !inst_tpair.
  apply sem_ind; try assumption.
  - apply (FP_small _ _ _ _ IIT Hc).
  - apply (FP_def _ _ _ _ _ ID Hc HIT).
  - eapply FP_at; [exact IP|exact Hc| |]; (eapply cv_trans; [apply inst_motive; try assumption|
      rewrite inst_mui; apply cv_refl]); rewrite inst_mui; apply closed_mui; assumption.
  - eapply FP_at; [exact Is|exact Hc| |]; apply inst_mu_ind_method; assumption.
  - exact (Ii _ _ Hc).
Qed.

Lemma fund_close_case : forall Gamma k IT F G i Q b x, FP Gamma IT (TSort 0) ->
  FP Gamma F (Def IT) -> FP Gamma G (Def IT) -> typing Gamma i IT -> FP Gamma i IT ->
  typing Gamma Q (arrow (CloseAt IT F G i) (TSort k)) ->
  typing Gamma b (close_case_method IT F G i Q) -> FP Gamma b (close_case_method IT F G i Q) ->
  FP Gamma x (CloseAt IT F G i) -> typing Gamma IT (TSort 0) ->
  typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
  FP Gamma (TCloseCase k IT F G i Q b x) (TApp Q x).
Proof.
  intros Gamma k IT F G i Q b x IIT IF IG Hi Ii HQ Hb Ib Ix HIT HF HG g1 g2 Hc. envs Hc.
  cl Hc HIT. cl Hc HF. cl Hc HG. cl Hc Hi. cl Hc HQ.
  pose proof (Ix _ _ Hc) as Hx'; rewrite !inst_CloseAt in Hx'.
  rewrite !inst_ccase, !instantiate_app.
  apply sem_close_case; try assumption.
  - apply (FP_small _ _ _ _ IIT Hc).
  - apply (FP_def _ _ _ _ _ IF Hc HIT).
  - apply (FP_def _ _ _ _ _ IG Hc HIT).
  - exact (Ii _ _ Hc).
  - eapply FP_at; [exact Ib|exact Hc| |]; apply inst_close_case_method; assumption.
Qed.

Lemma fund_close_ind : forall Gamma IT G P st F i x, FP Gamma IT (TSort 0) ->
  FP Gamma G (Def IT) -> typing Gamma P (close_motive IT G) -> FP Gamma P (close_motive IT G) ->
  typing Gamma st (close_ind_method IT G P) -> FP Gamma st (close_ind_method IT G P) ->
  FP Gamma F (Def IT) -> typing Gamma i IT -> FP Gamma i IT ->
  typing Gamma x (CloseAt IT F G i) -> FP Gamma x (CloseAt IT F G i) ->
  typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) -> typing Gamma F (Def IT) ->
  FP Gamma (TCloseInd IT G P st F i x) (TApp (TApp (TApp P F) i) x).
Proof.
  intros Gamma IT G P st F i x IIT IG HP IP Hs Is IF Hi Ii Hx Ix HIT HG HF g1 g2 Hc. envs Hc.
  cl Hc HIT. cl Hc HG. cl Hc HP. cl Hc Hs. cl Hc HF. cl Hc Hi. cl Hc Hx.
  pose proof (Ix _ _ Hc) as Hx'; rewrite !inst_CloseAt in Hx'.
  rewrite !inst_cind, !instantiate_app.
  apply sem_close_ind; try assumption.
  - apply (FP_small _ _ _ _ IIT Hc).
  - apply (FP_def _ _ _ _ _ IG Hc HIT).
  - eapply FP_at; [exact IP|exact Hc| |]; apply inst_close_motive; assumption.
  - eapply FP_at; [exact Is|exact Hc| |]; apply inst_close_ind_method; assumption.
  - apply (FP_def _ _ _ _ _ IF Hc HIT).
  - exact (Ii _ _ Hc).
Qed.
