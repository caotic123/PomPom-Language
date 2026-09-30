From Stdlib Require Import List Arith Bool Lia.
Require Export DecodeWork.
Import ListNotations.

Record context_encoding (Gamma : DB.ctx) (env : list nat) (Delta : ctx) : Prop := {
  ce_names : NoDup env;
  ce_length : List.length Gamma = List.length env;
  ce_wf : wf Delta;
  ce_domain : forall x, fresh_in Delta x <-> ~ In x env;
  ce_lookup : forall n A, nth_error Gamma n = Some A -> exists x B,
    nth_error env n = Some x /\ lookup Delta x = Some B /\
    encode env B = DB.lift (S n) 0 A
}.

Lemma context_encoding_cons : forall Gamma env Delta A T k,
  context_encoding Gamma env Delta -> encode env T = A -> typing Delta T (TSort k) ->
  context_encoding (A::Gamma) (fresh_id env::env) (extend Delta (fresh_id env) T).
Proof.
  intros Gamma env Delta A T k HC He HT. destruct HC as [Hnd Hlen Hwf Hdom Hlookup].
  assert (Hx : fresh_in Delta (fresh_id env)) by (apply Hdom, fresh_id_not_in).
  constructor.
  - constructor; auto using fresh_id_not_in.
  - cbn;now f_equal.
  - eapply wf_cons; eassumption.
  - intros y. destruct (Nat.eq_dec y (fresh_id env)) as [->|Hne].
    + unfold fresh_in; rewrite lookup_extend_same; cbn; split; [discriminate|tauto].
    + unfold fresh_in;rewrite lookup_extend_other by congruence. fold (fresh_in Delta y). rewrite Hdom; cbn; intuition congruence.
  - intros [|n] B HB; cbn [nth_error] in HB.
    + inversion HB; subst. exists (fresh_id env),T; split; [reflexivity|]. split;
        [apply lookup_extend_same|].
      rewrite encode_fresh; [reflexivity|eapply typing_fresh_not_free;eassumption].
    + destruct (Hlookup _ _ HB) as [x [U [Hname [HxU HU]]]].
      exists x,U; split; [exact Hname|]. split.
      * rewrite lookup_extend_other; [exact HxU|unfold fresh_in in Hx; congruence].
      * rewrite encode_fresh.
        -- rewrite HU, nameless.DBParallelBase.lift_fuse_zero by lia; reflexivity.
        -- eapply wf_type_fresh_not_free; eassumption.
Qed.

Lemma typing_encoded_cast : forall Gamma env t A B,
  typing Gamma t A -> type_wf Gamma A -> encode env A = encode env B -> typing Gamma t B.
Proof.
  intros Gamma env t A B Ht [k HA] HE.
  pose proof (encode_env_alpha _ _ _ HE) as Hab.
  eapply ty_conv; [exact Ht|eapply ty_alpha;[exact HA|exact Hab]|now apply cv_alpha].
Qed.
Lemma typing_encoded_result : forall Gamma env t A B,
  typing Gamma t A -> type_wf Gamma B -> encode env A = encode env B -> typing Gamma t B.
Proof.
  intros Gamma env t A B Ht [k HB] HE.
  eapply ty_conv; [exact Ht|exact HB|apply cv_alpha;now apply (encode_env_alpha env)].
Qed.

Local Ltac specialize_reflections := repeat match goal with
  | IH : forall (env : list nat) (Delta : ctx), context_encoding ?G env Delta -> _,
    HC : context_encoding ?G ?env ?Delta |- _ =>
      specialize (IH env Delta HC); destruct IH
  end.
Local Ltac scope_facts := repeat match goal with
  | H : SDTypingWork.typing ?G ?t ?A, HC : context_encoding ?G ?env ?Delta |- _ =>
    let Ht := fresh "Ht_scope" in let HA := fresh "HA_scope" in
    let Et := fresh "Et_code" in let EA := fresh "EA_code" in
    pose proof (sd_typing_scoped _ _ _ H) as Ht;
    pose proof (sd_type_scoped _ _ _ H) as HA;
    rewrite (ce_length _ _ _ HC) in Ht, HA;
    pose proof (encode_decode t env (ce_names _ _ _ HC) Ht) as Et;
    pose proof (encode_decode A env (ce_names _ _ _ HC) HA) as EA;
    clear H
  end.
Local Ltac encoded :=
  repeat first [
    match goal with E : encode ?env (decode ?env ?t) = ?t |- _ => rewrite E end |
    rewrite encode_arrow | rewrite encode_Def | rewrite encode_Family |
    rewrite encode_motive | rewrite encode_total | rewrite encode_recursive_method |
    rewrite encode_close_case_method | rewrite encode_close_motive |
    rewrite encode_mu_ind_method | rewrite encode_close_ind_method |
    progress cbn [encode MuAt CloseAt payload carrier DB.MuAt DB.CloseAt DB.payload DB.carrier]];
  try reflexivity.
Local Ltac cast_assumption :=
  fold decode; match goal with HC : context_encoding _ ?env ?G |- typing ?G ?t ?B =>
    match goal with HT : typing G t ?Source, HF : type_wf G ?Source |- _ =>
      eapply typing_encoded_cast with (env:=env) (A:=Source);[exact HT|exact HF|encoded]
    end
  end.

Theorem typing_reflection : forall Gamma t A, SDTypingWork.typing Gamma t A ->
  forall env Delta, context_encoding Gamma env Delta ->
  typing Delta (decode env t) (decode env A) /\ type_wf Delta (decode env A).
Proof.
  intros Gamma t A H; induction H; intros env Delta HC.
  all: specialize_reflections.
  all: pose proof (ce_wf _ _ _ HC) as Hwf.
  all: scope_facts.
  all: match goal with |- typing ?G ?t ?A /\ type_wf ?G ?A =>
    assert (Hform : type_wf G A) by (unfold type_wf;eauto using ty_sort);
    split;[|exact Hform]
  end.
  all: try solve [econstructor;eauto].
  all: try solve [econstructor; first [eassumption|cast_assumption]].
  all: try solve [
    (eapply ty_epi || eapply ty_switch || eapply ty_ipi || eapply ty_isig || eapply ty_ichoice ||
      eapply ty_interp || eapply ty_iall || eapply ty_hyps || eapply ty_ind ||
      eapply ty_in_mui || eapply ty_in_close || eapply ty_close_case || eapply ty_close_ind);
    first [eassumption|cast_assumption]].
Show.
Abort.
