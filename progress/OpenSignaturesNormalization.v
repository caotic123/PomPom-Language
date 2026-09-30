(* Full normalization transported from the semantic fundamental theorem.
   The older computation-termination bridge remains available independently. *)
Require Export OpenSignaturesTypingEncoding.
Require nameless.DBNormalization.
Require nameless.DBSemanticFundamental.

Lemma encoding_accessibility : forall env t,
  Acc (fun u v => nameless.DBCore.reduction v u) (encode env t) ->
  Acc (fun u v => reduction v u) t.
Proof.
  intros env t H. remember (encode env t) as a eqn:HE.
  revert t HE; induction H as [a Hacc IH]; intros t HE; subst a.
  constructor; intros u Hu.
  apply (IH (encode env u)); [now apply encode_reduction|reflexivity].
Qed.

Theorem named_normalization_from_computation :
  (forall Delta s T, nameless.DBTyping.typing Delta s T ->
    Acc (fun u v => nameless.DBComputationPreservation.computation v u) s) ->
  forall Gamma t A, typing Gamma t A -> Acc (fun u v => reduction v u) t.
Proof.
  intros HC Gamma t A HT.
  destruct (context_representation _ (typing_context _ _ _ HT))
    as [Delta [env [Hctx Hwf]]].
  pose proof (typing_encoding _ _ _ HT _ _ Hctx Hwf) as Htyped.
  apply (encoding_accessibility env).
  eapply nameless.DBNormalization.normalization_from_computation;
    [exact Htyped|eapply HC; exact Htyped].
Qed.

Print Assumptions named_normalization_from_computation.

Theorem named_full_normalization : forall Gamma t A,
  typing Gamma t A -> Acc (fun u v => reduction v u) t.
Proof.
  intros Gamma t A HT.
  destruct (context_representation _ (typing_context _ _ _ HT))
    as [Delta [env [Hctx Hwf]]].
  apply (encoding_accessibility env).
  exact (nameless.DBSemanticFundamental.typing_full_normalization _ _ _
    (typing_encoding _ _ _ HT _ _ Hctx Hwf)).
Qed.

Print Assumptions named_full_normalization.
