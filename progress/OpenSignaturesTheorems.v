(* Metatheory statements for the revised calculus.
   Every Conjecture below is deliberately unproved. None is used to define
   syntax, typing, reduction, elaboration, or the executable examples. *)
From Stdlib Require Import List Arith String.
Require Export OpenSignaturesExamples.
Import ListNotations.

Conjecture context_validity :
  forall Gamma t A, typing Gamma t A -> wf Gamma.
Conjecture type_correctness :
  forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Conjecture weakening :
  forall Gamma t A B k,
    typing Gamma t A -> typing Gamma B (TSort k) ->
    typing (B :: Gamma) (lift 1 0 t) (lift 1 0 A).
Conjecture substitution :
  forall Gamma A t B u,
    typing (A :: Gamma) t B -> typing Gamma u A ->
    typing Gamma (subst u 0 t) (subst u 0 B).
Conjecture conversion_substitution :
  forall t u s k,
    conv t u -> conv (subst s k t) (subst s k u).

Conjecture next_step_sound :
  forall t u, next_step t = Some u -> step t u.
Conjecture run_sound :
  forall fuel t, eval t (run fuel t).
Conjecture preservation :
  forall Gamma t u A, typing Gamma t A -> step t u -> typing Gamma u A.
Conjecture preservation_eval :
  forall Gamma t u A, typing Gamma t A -> eval t u -> typing Gamma u A.
Conjecture progress :
  forall t A, typing [] t A -> value t \/ exists u, step t u.
Conjecture normalization :
  forall Gamma t A, typing Gamma t A ->
    Acc (fun u v => reduction v u) t.
Conjecture full_preservation :
  forall Gamma t u A,
    typing Gamma t A -> reduction t u -> typing Gamma u A.
Conjecture confluence :
  forall Gamma t A u v,
    typing Gamma t A -> reduces t u -> reduces t v ->
    exists w, reduces u w /\ reduces v w.
Conjecture conversion_joinability :
  forall Gamma t u A,
    typing Gamma t A -> typing Gamma u A -> conv t u ->
    exists w, reduces t w /\ reduces u w.
Conjecture consistency :
  forall t, ~ typing [] t Bot.

Conjecture canonical_forms_close :
  forall IT F G i v,
    typing [] v (CloseAt IT F G i) -> value v ->
    exists xs, v = TIn xs /\ typing [] xs (payload IT F G i).
Conjecture canonical_forms_named :
  forall IT F G i t rs,
    typing [] t (CloseAt IT F G i) ->
    row_view [] IT (TApp F i) rs ->
    exists name D n xs,
      nth_error rs n = Some (name,D) /\
      eval t (TIn (TPair (enum_position n) xs)) /\
      typing [] xs (TInterp IT D (carrier IT G)).

Conjecture abort_typing :
  forall Gamma k A z,
    typing Gamma A (TSort k) -> typing Gamma z Bot ->
    typing Gamma (abort k A z) A.
Conjecture unroll_typing :
  forall Gamma IT F G i x,
    close_input Gamma IT F G i ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (unroll IT F G i x) (payload IT F G i).
Conjecture unroll_beta :
  forall IT F G i xs, eval (unroll IT F G i (TIn xs)) xs.
Conjecture close_induction_preservation :
  forall Gamma IT G P st F i x A u,
    typing Gamma (TCloseInd IT G P st F i x) A ->
    root_step (TCloseInd IT G P st F i x) = Some u ->
    typing Gamma u A.

Conjecture row_code_typing :
  forall Gamma IT rs,
    row_input Gamma IT rs ->
    typing Gamma (row_code IT rs) (TIDesc IT).
Conjecture signature_typing :
  forall Gamma IT rs,
    typing Gamma IT (TSort 0) ->
    row_input (IT :: Gamma) (lift 1 0 IT) rs ->
    typing Gamma (signature IT rs) (Def IT).
Conjecture row_position_identity :
  forall rs n name D,
    nth_error rs n = Some (name,D) ->
    label_at (row_enum rs) name (enum_position n).
Conjecture label_resolution_unique :
  forall Gamma rs name a b,
    NoDup (row_names rs) ->
    typing Gamma a (TEnumT (row_enum rs)) ->
    typing Gamma b (TEnumT (row_enum rs)) ->
    label_at (row_enum rs) name a -> label_at (row_enum rs) name b ->
    conv a b.

Conjecture dead_sound :
  forall Gamma IT D X d,
    dead Gamma IT D X d ->
    typing Gamma d (arrow (TInterp IT D X) Bot).
Conjecture dead_close_uninhabited :
  forall IT F G i d,
    close_input [] IT F G i ->
    dead [] IT (TApp F i) (carrier IT G) d ->
    forall x, ~ typing [] x (CloseAt IT F G i).
Conjecture row_handlers_sound :
  forall Gamma IT X Y target source handlers,
    row_input Gamma IT source -> row_input Gamma IT target ->
    typing Gamma X (Family IT) -> typing Gamma Y (TSort 0) ->
    conv Y (TInterp IT (row_code IT target) X) ->
    row_handlers Gamma IT X Y target source handlers ->
    Forall2 (fun entry h =>
      typing Gamma h (arrow (TInterp IT (snd entry) X) Y)) source handlers.
Conjecture description_subtyping_sound :
  forall Gamma IT D D' X q,
    desc_sub Gamma IT D D' X q ->
    typing Gamma q (arrow (TInterp IT D X) (TInterp IT D' X)).
Conjecture subtyping_sound :
  forall Gamma A B c, sub Gamma A B c -> typing Gamma c (arrow A B).
Conjecture case_handlers_sound :
  forall Gamma k IT X Q bs rs handlers,
    row_input Gamma IT rs ->
    typing Gamma X (Family IT) -> typing Gamma Q (TSort k) ->
    elab_cases Gamma k IT X Q bs rs handlers ->
    typing Gamma (tuple handlers)
      (TEPi k (row_enum rs) (handler_motive IT rs X Q)).
Conjecture synthesis_sound :
  forall Gamma e A t, elab_synth Gamma e A t -> typing Gamma t A.
Conjecture checking_sound :
  forall Gamma e A t, elab_check Gamma e A t -> typing Gamma t A.

(* Closing substitutions are necessary for a meaningful open-context
   coherence statement: an inconsistent context need not have a closing
   substitution, and evaluating its free bottom variable is not an
   observation of a closed program. Entries are closed core terms. *)
Fixpoint instantiate (env : list term) (t : term) : term :=
  match env with
  | [] => t
  | u :: env => instantiate env (subst u 0 t)
  end.
Inductive closing : ctx -> list term -> Prop :=
| closing_nil : closing [] []
| closing_cons : forall Gamma env A u,
    wf (A :: Gamma) -> closing Gamma env ->
    typing [] u (instantiate env A) ->
    closing (A :: Gamma) (u :: env).

Conjecture closing_substitution :
  forall Gamma env t A,
    closing Gamma env -> typing Gamma t A ->
    typing [] (instantiate env t) (instantiate env A).

Definition observation_type :=
  TEnumT (TConsE (TTag "true"%string)
    (TConsE (TTag "false"%string) TNilE)).
Definition observation (t : term) :=
  t = TEZero \/ t = TESucc TEZero.
Definition closed_observational_eq A t u :=
  typing [] t A /\ typing [] u A /\
  forall context result,
    typing [A] context observation_type -> observation result ->
    (eval (subst t 0 context) result <-> eval (subst u 0 context) result).
Definition observational_eq Gamma A t u :=
  typing Gamma t A /\ typing Gamma u A /\
  forall env, closing Gamma env ->
    closed_observational_eq (instantiate env A)
      (instantiate env t) (instantiate env u).

(* No judgmental eta rule for close is assumed. *)
Conjecture close_roll_unroll :
  forall Gamma IT F G i x,
    close_input Gamma IT F G i ->
    typing Gamma x (CloseAt IT F G i) ->
    observational_eq Gamma (CloseAt IT F G i)
      (TIn (unroll IT F G i x)) x.
Conjecture coercion_coherence :
  forall Gamma A B c d,
    sub Gamma A B c -> sub Gamma A B d ->
    observational_eq Gamma (arrow A B) c d.
Conjecture checking_coherence :
  forall Gamma e A t u,
    elab_check Gamma e A t -> elab_check Gamma e A u ->
    observational_eq Gamma A t u.

(* Concrete typing/elaboration claims: still unproved, unlike the closed
   syntactic reduction checks in OpenSignaturesExamples. *)
Conjecture list_definitions_well_typed :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    typing Gamma (list_def A) (Def TUnitT) /\
    typing Gamma (nonempty_def A) (Def TUnitT) /\
    typing Gamma (tree_def A) (Def TUnitT).
Conjecture nil_typing :
  forall Gamma A,
    typing Gamma A (TSort 0) -> typing Gamma nil_value (list_type A).
Conjecture cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (list_type A) ->
    typing Gamma (cons_value a xs) (list_type A).
Conjecture nonempty_cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (list_type A) ->
    typing Gamma (nonempty_value a xs) (nonempty_type A).
Conjecture reused_tree_cons_typing :
  forall Gamma A a xs,
    typing Gamma A (TSort 0) -> typing Gamma a A ->
    typing Gamma xs (tree_type A) ->
    typing Gamma (cons_value a xs) (tree_type A).
Conjecture nonempty_observers_typing :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    typing Gamma (head_term A) (arrow (nonempty_type A) A) /\
    typing Gamma (tail_term A) (arrow (nonempty_type A) (list_type A)).
Conjecture nonempty_widening :
  forall Gamma A,
    typing Gamma A (TSort 0) ->
    sub Gamma (nonempty_type A) (list_type A) (to_list A).
Conjecture singleton_source_elaborates :
  elab_check [] (singleton_source TUnit) (nonempty_type TUnitT)
    (singleton TUnit).
Conjecture no_uniform_list_downcast :
  ~ exists c, typing [] c
      (TPi (TSort 0) (arrow (list_type (TVar 0)) (nonempty_type (TVar 0)))).
Conjecture self_restricted_list_empty :
  forall A,
    typing [] A (TSort 0) ->
    forall x, ~ typing [] x (endless_type A).
