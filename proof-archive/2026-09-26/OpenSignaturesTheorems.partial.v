(* Metatheory statements for the revised calculus.
   Every Conjecture below is deliberately unproved. None is used to define
   syntax, typing, reduction, elaboration, or the executable examples. *)
From Stdlib Require Import List Arith String.
Require Export OpenSignaturesExamples.
Import ListNotations.
Require Import Stdlib.Program.Equality.
From Stdlib Require Import FMapFacts.
Module VarMapFacts := FMapFacts.WFacts(VarMap).

(* Context validity follows directly from the core typing rules.
   See PROOF_START.md for the proof approach and acceptance check.
   No later conjectures are used. *)
Theorem context_validity :
  forall Gamma t A, typing Gamma t A -> wf Gamma.
Proof.
  intros Gamma t A Htyping.
  induction Htyping; assumption.
Qed.

Lemma fresh_id_not_in : forall ids, ~ In (fresh_id ids) ids.
Proof.
  assert (Hmax : forall ids n, In n ids -> n <= fold_right Nat.max 0 ids).
  {
    intros ids. induction ids as [|a ids IH]; intros n Hin; simpl in *.
    - contradiction.
    - destruct Hin as [<- | Hin].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
  }
  intros ids Hin. apply Hmax in Hin.
  unfold fresh_id in Hin.
  exact (Nat.nle_succ_diag_l _ Hin).
Qed.

(* Supply any context and any additional IDs to avoid. *)
Lemma exists_fresh_id : forall (Gamma : ctx) (ids : list nat),
  exists z, fresh_in Gamma z /\ ~ In z ids.
Proof.
  intros Gamma ids.
  pose (context_ids := flat_map
    (fun entry => fst entry :: vars (snd entry)) (VarMap.elements Gamma)).
  pose (z := fresh_id (ids ++ context_ids)).
  assert (Hz : ~ In z (ids ++ context_ids)) by apply fresh_id_not_in.
  exists z. split.
  - unfold fresh_in, lookup.
    destruct (VarMap.find z Gamma) as [D |] eqn:Hfind; [|reflexivity].
    exfalso. apply Hz. apply in_or_app. right.
    apply VarMap.find_2 in Hfind.
    apply VarMap.elements_1 in Hfind.
    apply InA_alt in Hfind.
    destruct Hfind as [[q T] [[Hkey Hvalue] Hin]].
    change (z = q) in Hkey.
    unfold context_ids. apply in_flat_map.
    exists (q, T). split; [exact Hin |].
    simpl. left. symmetry. exact Hkey.
  - intro Hin. apply Hz. apply in_or_app. left. exact Hin.
Qed.

Theorem weakening :
  forall Gamma x t A B k,
    fresh_in Gamma x ->
    typing Gamma t A -> typing Gamma B (TSort k) ->
    typing (extend Gamma x B) t A.
(* >> Proved the variable case and all cases without binders. The three
   binder cases remain open, so weakening is still admitted as a whole. *)
Proof.
  intros Gamma x t A B k Hfresh Htyping HB.
  revert x B k Hfresh HB.
  induction Htyping; intros y C l Hfresh HC.
  all: assert (Hwf : wf (extend Gamma y C)) by
    (eapply wf_cons; [eapply context_validity; exact HC | exact HC | exact Hfresh]).

  (* Reapply rules whose premises stay in the same context, using the IHs. *)
  all: try solve [econstructor; eauto].

  - (* ty_var: the fresh extension cannot overwrite an existing variable. *)
    apply ty_var; [exact Hwf |].
    unfold lookup, extend.
    rewrite VarMapFacts.add_neq_o.
    + exact H0.
    + intro Heq. subst y.
      unfold fresh_in in Hfresh.
      rewrite H0 in Hfresh. discriminate.
  
  - 
  destruct (Nat.eq_dec x y) as [Hxx0_eq | Hxx0_neq].
  subst.
  (* >> Generate z with context freshness and an avoidance fact for later. *)
  destruct (exists_fresh_id (extend Gamma y C)
    ([y] ++ vars A ++ vars B ++ vars C)) as [z [Hzfresh Hzavoid]].
  eapply ty_alpha with
    (t := TPi z A (subst (TVar z) y B)).

  apply ty_pi.
  exact Hzfresh.  
  eapply (IHHtyping1 _ _ l).
  assumption.
  assumption.
  

  apply ty_pi.

  (* Remaining: ty_pi, ty_sigma, ty_lam. These require handling binder
     freshness/collisions and transporting derivations between contexts. *)
Admitted.


Theorem type_correctness :
  forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Proof.
  intros Gamma t A Htyping.
  (* Induct on the typing derivation, so each premise supplies its own
     type-correctness induction hypothesis, including beneath binders. *)
  induction Htyping; unfold type_wf in *.

  (* Close the cases whose result is already a known type, a sort, or a
     directly formed primitive type. No conjectures are used here. *)
  all: try solve [
    eauto using ty_sort, ty_unitT, ty_uid, ty_enumu,
      ty_enumt, ty_conse, ty_idesc, ty_iall, context_validity
  ].
   
  dependent induction H.
  admit.
  destruct (Nat.eq_dec x x0) as [Hxx0_eq | Hxx0_neq].
  subst.

  assert (lookup (extend Gamma x0 A0) x0 = Some A -> A = A0).
  clear H2 IHwf H0 H1.  
  unfold extend.
  unfold lookup.

  (* >> add_o is in Stdlib/FSets/FMapFacts.v:380, in the WFacts functor.
     At file scope, import it and instantiate the facts module:
       From Stdlib Require Import FMapFacts.
       Module VarMapFacts := FMapFacts.WFacts(VarMap).
     Then use VarMapFacts.add_o; VarMap itself does not export add_o.
     For lookup at the inserted key, VarMapFacts.add_eq_o is more direct. *)
  rewrite VarMapFacts.add_eq_o.
  congruence.
  reflexivity.
  apply H3 in H2.
  subst.
  exists k.
  

  (* >> Yes: "A is a type" means type_wf Gamma A, which is exactly
     exists k, typing Gamma A (TSort k). The evidence comes from H : wf Gamma
     together with H0, not from a case split on A's syntax.

     The needed auxiliary lemma is:
       forall Gamma x A, wf Gamma -> lookup Gamma x = Some A ->
         exists k, typing Gamma A (TSort k).

     Prove it by induction on wf Gamma, generalizing x and A.
     - Empty context: lookup cannot return Some A.
     - Extension by y : B: wf_cons supplies typing Delta B (TSort j).
       If x = y, lookup gives A = B; weaken that derivation to Gamma
       and choose j. Otherwise, the induction hypothesis supplies k and
       typing Delta A (TSort k); weaken that derivation to Gamma.

     Thus a proved weakening lemma is the prerequisite. Once the auxiliary
     lemma is proved, applying it to H and H0 closes this case. Adding
     "A is a type" as a premise here would assume what we need to prove. *)




  (* Remaining cases, in constructor order:
     ty_var: direct context lookup, type formation and weakening.
     ty_app: Pi formation inversion and substitution.
     ty_fst: Sigma formation inversion.
     ty_snd: Sigma formation inversion and substitution.
     ty_switch: form the motive's application type.
     ty_mui: form Family IT.
     ty_in_mui: form MuAt IT D i.
     ty_ind: form the motive's application to the index/value pair.
     ty_close: form Family IT.
     ty_in_close: form CloseAt IT F G i.
     ty_close_case: form the motive's application type.
     ty_close_ind: form the three successive motive applications.

     The proof is deliberately left open here for these remaining cases.
     Weakening and substitution below are still yours to prove. *)

(* Stable binding IDs: context extension leaves both t and A unchanged. *)

Conjecture substitution :
  forall Gamma x A t B u,
    fresh_in Gamma x ->
    typing (extend Gamma x A) t B -> typing Gamma u A ->
    typing Gamma (subst u x t) (subst u x B).
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
  forall t A, typing empty_ctx t A -> value t \/ exists u, step t u.
Conjecture normalization :
  forall Gamma t A, typing Gamma t A ->
    Acc (fun u v => reduction v u) t.
Conjecture full_preservation :
  forall Gamma t u A,
    typing Gamma t A -> reduction t u -> typing Gamma u A.
(* Named representatives join modulo alpha; alpha conversion itself is not
   a reduction step, so it does not introduce reflexive reduction loops. *)
Conjecture confluence :
  forall Gamma t A u v,
    typing Gamma t A -> reduces t u -> reduces t v ->
    exists w w', reduces u w /\ reduces v w' /\ alpha_equiv w w'.
Conjecture conversion_joinability :
  forall Gamma t u A,
    typing Gamma t A -> typing Gamma u A -> conv t u ->
    exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Conjecture consistency :
  forall t, ~ typing empty_ctx t Bot.

Conjecture canonical_forms_close :
  forall IT F G i v,
    typing empty_ctx v (CloseAt IT F G i) -> value v ->
    exists xs, v = TIn xs /\ typing empty_ctx xs (payload IT F G i).
Conjecture canonical_forms_named :
  forall IT F G i t rs,
    typing empty_ctx t (CloseAt IT F G i) ->
    row_view empty_ctx IT (TApp F i) rs ->
    exists name D n xs,
      nth_error rs n = Some (name,D) /\
      eval t (TIn (TPair (enum_position n) xs)) /\
      typing empty_ctx xs (TInterp IT D (carrier IT G)).

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
  forall Gamma x IT rs,
    fresh_in Gamma x ->
    typing Gamma IT (TSort 0) ->
    row_input (extend Gamma x IT) IT rs ->
    typing Gamma (signature x IT rs) (Def IT).
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
    close_input empty_ctx IT F G i ->
    dead empty_ctx IT (TApp F i) (carrier IT G) d ->
    forall x, ~ typing empty_ctx x (CloseAt IT F G i).
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
   observation of a closed program. Entries pair stable binding IDs with
   closed core terms. *)
Fixpoint instantiate (env : list (nat * term)) (t : term) : term :=
  match env with
  | [] => t
  | (x, u) :: env => instantiate env (subst u x t)
  end.
Inductive closing : ctx -> list (nat * term) -> Prop :=
| closing_nil : closing empty_ctx []
| closing_cons : forall Gamma env x A u,
    fresh_in Gamma x -> wf (extend Gamma x A) -> closing Gamma env ->
    typing empty_ctx u (instantiate env A) ->
    closing (extend Gamma x A) ((x, u) :: env).

Conjecture closing_substitution :
  forall Gamma env t A,
    closing Gamma env -> typing Gamma t A ->
    typing empty_ctx (instantiate env t) (instantiate env A).

Definition observation_type :=
  TEnumT (TConsE (TTag "true"%string)
    (TConsE (TTag "false"%string) TNilE)).
Definition observation (t : term) :=
  t = TEZero \/ t = TESucc TEZero.
Definition closed_observational_eq A t u :=
  typing empty_ctx t A /\ typing empty_ctx u A /\
  forall x context result,
    typing (extend empty_ctx x A) context observation_type -> observation result ->
    (eval (subst t x context) result <-> eval (subst u x context) result).
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

(* Concrete typing/elaboration claims: still unproved.
   Computation regressions are checked separately in OpenSignaturesExamples. *)
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
  elab_check empty_ctx (singleton_source TUnit) (nonempty_type TUnitT)
    (singleton TUnit).
Conjecture no_uniform_list_downcast :
  ~ exists c, typing empty_ctx c
      (TPi 0 (TSort 0) (arrow (list_type (TVar 0)) (nonempty_type (TVar 0)))).
Conjecture self_restricted_list_empty :
  forall A,
    typing empty_ctx A (TSort 0) ->
    forall x, ~ typing empty_ctx x (endless_type A).
