(* Beta subject reduction for the new rules, including distinct application
   and lambda annotations related by dependent function cumulativity. *)
Require Export annotated.AGeneration.

Theorem beta_preservation : forall Gamma A B C D b a T,
  typing Gamma (TApp A B (TLam C D b) a) T ->
  typing Gamma (subst a 0 b) T.
Proof.
  intros Gamma A B C D b a T HT.
  destruct (application_generation _ _ _ HT _ _ _ _ eq_refl)
    as [j [k [HA [HB [Hf [Ha HC]]]]]].
  destruct (lambda_generation _ _ _ Hf _ _ _ eq_refl)
    as [l [m [HCform [HDform [Hb Hfun]]]]].
  destruct (RC.comparison_pi_inversion _ _ _ _ Hfun) as [Hdom Hcod].
  assert (HaC : typing Gamma a (erase C)).
  { eapply comparison_typing; [exact Ha|exact Hdom|].
    exists l; exact (typing_erasure _ _ _ HCform). }
  pose proof (substitution _ _ _ _ _ Hb HaC) as Hbeta.
  eapply comparison_typing; [exact Hbeta| |exact (type_correctness _ _ _ HT)].
  eapply RC.comparison_transitive; [exact (RC.comparison_subst _ _ Hcod (erase a) 0)|exact HC].
Qed.

Print Assumptions beta_preservation.
