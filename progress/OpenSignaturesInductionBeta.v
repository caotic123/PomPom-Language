(* Root computation of close induction and case analysis needs no global
   preservation or normalization assumption. *)
From Stdlib Require Import List.
Require Export OpenSignaturesTypingEncoding.
Require nameless.DBInductionBeta.

Theorem named_close_ind_preservation : forall Gamma IT G P st F i x A u,
  typing Gamma (TCloseInd IT G P st F i x) A ->
  root_step (TCloseInd IT G P st F i x) = Some u -> typing Gamma u A.
Proof.
  intros Gamma IT G P st F i x A u Ht Hr.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [Delta [env [HC HD]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HD) as HT.
  pose proof (nameless.DBInductionBeta.close_ind_reduction_preservation _ _ _ HT
    _ _ _ _ _ _ _ _ eq_refl (encode_root_step _ _ env Hr)) as Hu.
  eapply typing_reflection_given; [exact Hu|exact HC|reflexivity|reflexivity].
Qed.

Theorem named_close_case_preservation : forall Gamma k IT F G i Q b x A u,
  typing Gamma (TCloseCase k IT F G i Q b x) A ->
  root_step (TCloseCase k IT F G i Q b x) = Some u -> typing Gamma u A.
Proof.
  intros Gamma k IT F G i Q b x A u Ht Hr.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [Delta [env [HC HD]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HD) as HT.
  pose proof (nameless.DBInductionBeta.close_case_reduction_preservation _ _ _ HT
    _ _ _ _ _ _ _ _ _ eq_refl (encode_root_step _ _ env Hr)) as Hu.
  eapply typing_reflection_given; [exact Hu|exact HC|reflexivity|reflexivity].
Qed.
