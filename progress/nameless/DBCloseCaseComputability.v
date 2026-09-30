(* Close-case elimination into any candidate family, including motives in
   arbitrary universe levels. Irrelevant operator annotations remain SN. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBHypsComputability nameless.DBSaturatedElimination.
Import ListNotations Full.

Lemma rolled_elements_intro : forall R u, R u -> rolled_elements R (TIn u).
Proof. intros R u Hu; apply saturated_intro; exists u; auto. Qed.
Lemma in_reductions : forall u t, rtc reduction (TIn u) t ->
  exists v, t = TIn v /\ rtc reduction u v.
Proof.
  apply DBInterpretationComputability.reduces_unary; intros u t H; inversion H; subst; [discriminate|].
  eexists; split; [reflexivity|now apply rtc_one].
Qed.
Definition case_plug p x :=
  match p with TCloseCase k IT F G i Q b _ => TCloseCase k IT F G i Q b x | _ => TVar 0 end.

Section CloseCaseCandidate.
Variable Payload : term -> Prop.
Hypothesis payload_candidate : candidate Payload.
Variable Result : term -> term -> Prop.
Hypothesis result_candidate : forall x, rolled_elements Payload x -> candidate (Result x).
Hypothesis result_stable : stable_family (rolled_elements Payload) Result.

Definition case_method b := forall u, Payload u -> Result (TIn u) (TApp b u).
Lemma case_method_reductions : forall b b', case_method b -> rtc reduction b b' -> case_method b'.
Proof.
  intros b b' Hb HR u Hu.
  eapply candidate_reducts; [apply result_candidate; now apply rolled_elements_intro| |exact (Hb u Hu)].
  apply red_star_TApp; [exact HR|constructor].
Qed.
Definition case_parameter p := exists k IT F G i Q b,
  p = TCloseCase k IT F G i Q b (TVar 0) /\
  Forall full_SN [IT;F;G;i;Q;b] /\ case_method b.

Ltac unpack_normalizing_arguments :=
  repeat match goal with H : Forall full_SN (_ :: _) |- _ => inversion H; subst; clear H end.
Ltac pack_normalizing_arguments :=
  repeat (apply Forall_cons;
    [solve [assumption | match goal with
      HR : reduction ?t ?u, HS : full_SN ?t |- full_SN ?u =>
        exact (@Acc_inv term (fun u v => reduction v u) t HS u HR)
      end]|]);
  apply Forall_nil.

Lemma case_parameter_reduct : forall p q,
  case_parameter p -> reduction p q -> case_parameter q.
Proof.
  intros p q [k [IT [F [G [i [Q [b [-> [HS HM]]]]]]]]] HR.
  unpack_normalizing_arguments; inversion HR; subst.
  all: try discriminate.
  all: try solve [match goal with H : reduction (TVar 0) _ |- _ => inversion H; discriminate end].
  all: do 7 eexists; split; [reflexivity|]; split;
    [pack_normalizing_arguments|try exact HM].
  eapply case_method_reductions; [exact HM|now apply rtc_one].
Qed.
Lemma case_argument_reduction : forall p, case_parameter p -> forall x y,
  reduction x y -> reduction (case_plug p x) (case_plug p y).
Proof.
  intros p [k [IT [F [G [i [Q [b [-> _]]]]]]]] x y H.
  cbn [case_plug]; now apply red_TCloseCase_x.
Qed.
Lemma case_plug_neutral : forall p, case_parameter p -> forall x, neutral (case_plug p x).
Proof. intros p [k [IT [F [G [i [Q [b [-> _]]]]]]]] x; exact I. Qed.
Lemma case_neutral_step : forall p, case_parameter p -> forall x u,
  neutral x -> reduction (case_plug p x) u ->
  (exists q, reduction p q /\ u = case_plug q x) \/
  (exists y, reduction x y /\ u = case_plug p y).
Proof.
  intros p [k [IT [F [G [i [Q [b [-> _]]]]]]]] x u HN HR.
  cbn [case_plug] in HR; inversion HR; subst.
  all: try solve [right; eexists; split; [eassumption|reflexivity]].
  all: try solve [destruct x; cbn [neutral root_step] in *; contradiction || discriminate].
  all: left; match goal with |- exists q, _ /\ ?u = _ =>
    lazymatch u with TCloseCase ?k ?IT ?F ?G ?i ?Q ?b _ =>
      exists (TCloseCase k IT F G i Q b (TVar 0)); split;
        [eauto using red_TCloseCase_IT, red_TCloseCase_F, red_TCloseCase_G,
          red_TCloseCase_i, red_TCloseCase_Q, red_TCloseCase_b|reflexivity]
    end end.
Qed.

Lemma case_seed_computable : forall p, case_parameter p -> forall u,
  Payload u -> Result (TIn u) (case_plug p (TIn u)).
Proof.
  intros p [k [IT [F [G [i [Q [b [-> [HS HM]]]]]]]]] u Hu.
  unpack_normalizing_arguments; cbn [case_plug].
  pose proof (rolled_elements_candidate _ payload_candidate) as CD.
  pose proof (rolled_elements_intro _ _ Hu) as HIn.
  pose proof (full_SN_in _ (candidate_normalizing payload_candidate Hu)) as HSNIn.
  apply computability_by_head_expansion; [exact (result_candidate _ HIn)| | |].
  - cbn [term_children]; pack_normalizing_arguments.
  - intros t HT; inversion HT; exact I.
  - intros t v HT HV; inversion HT; subst.
    match goal with H : rtc reduction (TIn u) ?x |- _ =>
      destruct (in_reductions _ _ H) as [u' [-> Ru]] end.
    inversion HV; subst; cbn [root_step] in *.
    match goal with H : Some _ = Some _ |- _ => inversion H; subst end.
    assert (Hu' : Payload u') by (eapply candidate_reducts; eassumption).
    apply (proj2 (stable_family_reductions _ _ CD result_stable _ _ (red_star_TIn _ _ Ru) HIn _)).
    eapply case_method_reductions; [exact HM|eassumption|exact Hu'].
Qed.

Lemma case_parameter_normalizing : forall k IT F G i Q b,
  Forall full_SN [IT;F;G;i;Q;b] -> full_SN (TCloseCase k IT F G i Q b (TVar 0)).
Proof.
  intros k IT F G i Q b HS; unpack_normalizing_arguments.
  apply normalization_by_head_expansion.
  - cbn [term_children]; repeat (apply Forall_cons; [first [assumption|exact (candidate_variable _ normalizing_candidate 0)]|]); constructor.
  - intros t v HT HV; inversion HT; subst.
    match goal with H : rtc reduction (TVar 0) ?x |- _ =>
      assert (HE : TVar 0 = x) by (apply normal_reductions_identity; [intros y HY; inversion HY; discriminate|exact H]);
      subst x end.
    inversion HV; subst; discriminate.
Qed.

Theorem close_case_computable : forall k IT F G i Q b,
  Forall full_SN [IT;F;G;i;Q;b] -> case_method b -> forall x,
  rolled_elements Payload x -> Result x (TCloseCase k IT F G i Q b x).
Proof.
  intros k IT F G i Q b HS HM x Hx.
  change (Result x (case_plug (TCloseCase k IT F G i Q b (TVar 0)) x)).
  eapply saturated_elimination with
    (parameter_step:=reduction) (valid_parameter:=case_parameter)
    (seed:=fun z => exists u, z = TIn u /\ Payload u).
  - intros z [u [-> Hu]]; apply full_SN_in; exact (candidate_normalizing payload_candidate Hu).
  - exact result_candidate.
  - exact result_stable.
  - exact case_parameter_reduct.
  - exact case_argument_reduction.
  - exact case_plug_neutral.
  - exact case_neutral_step.
  - intros p Hp z [u [-> Hu]]; now apply case_seed_computable.
  - now apply case_parameter_normalizing.
  - exists k,IT,F,G,i,Q,b; auto.
  - exact Hx.
Qed.
End CloseCaseCandidate.

Print Assumptions close_case_computable.
