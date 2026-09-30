(* Beta preservation does not require unrestricted eta preservation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesTypingEncoding.
Require nameless.DBBeta.
Import ListNotations.

Theorem named_beta_preservation : forall Gamma x b a T,
  typing Gamma (TApp (TLam x b) a) T -> typing Gamma (subst a x b) T.
Proof.
  intros Gamma x b a T Ht.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [G [env [HC HG]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HG) as HT.
  pose proof (nameless.DBBeta.beta_reduction_preservation _ _ _ HT _ _ eq_refl) as Hbeta.
  eapply typing_reflection_given; [exact Hbeta|exact HC|apply encode_subst|reflexivity].
Qed.
