(* Machine check of docs/type-rules/calculus.tex: the statements of the
   relational-model results cited in its elaboration lemma table.
   Build: make -C progress check-docs *)
Require Import OpenSignatures.
Require Import OpenSignaturesRelFundamental OpenSignaturesRelAdequacy OpenSignaturesRelGraphFunc
  OpenSignaturesRelGraphComp OpenSignaturesRelCoercion OpenSignaturesRelElab.
Goal forall Gamma t A, typing Gamma t A -> forall g1 g2, closing2 Gamma g1 g2 ->
  rel_at (instantiate g1 t) (instantiate g2 t) (instantiate g1 A) (instantiate g2 A).
Proof. exact rel_fundamental. Qed.
Goal forall s1 s2, typing empty_ctx s1 observation_type -> typing empty_ctx s2 observation_type ->
  rel_at s1 s2 observation_type observation_type ->
  forall r, observation r -> (eval s1 r <-> eval s2 r).
Proof. exact rel_adequacy. Qed.
Goal forall Gamma A t u, typing Gamma t A -> typing Gamma u A ->
  (forall g1 g2, closing2 Gamma g1 g2 ->
     rel_at (instantiate g1 t) (instantiate g2 u) (instantiate g1 A) (instantiate g2 A)) ->
  observational_eq Gamma A t u.
Proof. exact rel_observational. Qed.
Goal forall A B G1, Gr A B G1 -> forall G2, Gr A B G2 ->
  forall a1 a2 b1 b2, G1 a1 b1 -> G2 a2 b2 -> rel_at a1 a2 A A -> rel_at b1 b2 B B.
Proof. exact Gr_func. Qed.
Goal forall A B G, Gr A B G -> forall a, closed a -> rel_at a a A A -> exists b, G a b.
Proof. exact Gr_total. Qed.
Goal forall A M B G1 G2, Gr A M G1 -> Gr M B G2 ->
  exists G3, Gr A B G3 /\ forall a m b, G1 a m -> G2 m b -> G3 a b.
Proof. exact Gr_comp. Qed.
Goal forall Gamma A B c, sub Gamma A B c -> forall g, closing2 Gamma g g ->
  exists G, Gr (instantiate g A) (instantiate g B) G /\
    forall a, closed a -> rel_at a a (instantiate g A) (instantiate g A) ->
      G a (TApp (instantiate g c) a).
Proof. exact sub_real. Qed.
Goal forall Gamma IT D D' X q, desc_sub Gamma IT D D' X q -> forall g, closing2 Gamma g g ->
  exists Gp, Gr (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D' X)) Gp /\
    forall xs, closed xs ->
      rel_at xs xs (instantiate g (TInterp IT D X)) (instantiate g (TInterp IT D X)) ->
      Gp xs (TApp (instantiate g q) xs).
Proof. exact desc_real. Qed.
Check gr_eq. Check gr_empty. Check gr_pi. Check gr_sum. Check gr_roll.
Goal forall Gamma A B c d, sub Gamma A B c -> sub Gamma A B d ->
  observational_eq Gamma (arrow A B) c d. Proof. exact coercion_coherence_rel. Qed.
Goal forall Gamma e A t u, elab_check Gamma e A t -> elab_check Gamma e A u ->
  observational_eq Gamma A t u. Proof. exact checking_coherence_rel. Qed.
