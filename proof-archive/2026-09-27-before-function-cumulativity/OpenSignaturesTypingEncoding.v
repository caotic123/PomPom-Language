From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesTypingReflection.
Require nameless.DBDerivedTyping.
Import ListNotations.
Module ST := nameless.DBTyping.
Module SS := nameless.DBDerivedTyping.

Lemma context_encoding_extend : forall Gamma env Delta A T k x,
  context_encoding Gamma env Delta -> encode env T = A -> typing Delta T (TSort k) -> fresh_in Delta x ->
  context_encoding (A::Gamma) (x::env) (extend Delta x T).
Proof.
  intros Gamma env Delta A T k x HC He HT Hx. destruct HC as [Hnd Hlen Hwf Hdom Hlookup].
  assert (Hnot : ~ In x env) by now apply Hdom.
  constructor.
  - constructor; assumption.
  - cbn;now f_equal.
  - eapply wf_cons; eassumption.
  - intros y. destruct (Nat.eq_dec y x) as [->|Hne].
    + unfold fresh_in; rewrite lookup_extend_same; cbn; split; [discriminate|tauto].
    + unfold fresh_in;rewrite lookup_extend_other by congruence. fold (fresh_in Delta y).
      rewrite Hdom; cbn; intuition congruence.
  - intros [|n] B HB; cbn [nth_error] in HB.
    + inversion HB; subst. exists x,T; split; [reflexivity|]. split; [apply lookup_extend_same|].
      rewrite encode_fresh; [reflexivity|eapply typing_fresh_not_free;eassumption].
    + destruct (Hlookup _ _ HB) as [y [U [Hname [HyU HU]]]].
      exists y,U; split; [exact Hname|]. split.
      * rewrite lookup_extend_other; [exact HyU|unfold fresh_in in Hx; congruence].
      * rewrite encode_fresh.
        -- rewrite HU, nameless.DBParallelBase.lift_fuse_zero by lia; reflexivity.
        -- eapply wf_type_fresh_not_free; eassumption.
Qed.

Lemma context_encoding_lookup : forall Gamma env Delta x T,
  context_encoding Gamma env Delta -> lookup Delta x = Some T ->
  exists n A, encode_var env x = n /\ nth_error Gamma n = Some A /\ encode env T = DB.lift (S n) 0 A.
Proof.
  intros Gamma env Delta x T HC HT.
  assert (Hin : In x env).
  { destruct (in_dec Nat.eq_dec x env) as [H|H]; [exact H|].
    apply (ce_domain _ _ _ HC) in H. unfold fresh_in in H; congruence. }
  apply In_nth_error in Hin; destruct Hin as [n Hn].
  assert (Hlt : n < List.length env) by (apply nth_error_Some;rewrite Hn;discriminate).
  assert (Hlt' : n < List.length Gamma) by (rewrite (ce_length _ _ _ HC);exact Hlt).
  apply nth_error_Some in Hlt'. destruct (nth_error Gamma n) as [A|] eqn:HA; [|contradiction].
  destruct (ce_lookup _ _ _ HC _ _ HA) as [y [B [Hname [Hlook Hcode]]]].
  assert (x = y) by congruence; subst y. assert (T = B) by congruence; subst B.
  exists n,A; repeat split; try assumption.
  apply nth_error_nth with (d:=0) in Hn; rewrite <- Hn.
  apply encode_var_nth; [exact (ce_names _ _ _ HC)|exact Hlt].
Qed.

Local Ltac encode_types := repeat first
  [rewrite encode_subst in * | rewrite encode_arrow in * | rewrite encode_Def in * |
   rewrite encode_Family in * | rewrite encode_motive in * | rewrite encode_recursive_method in * |
   rewrite encode_close_case_method in * | rewrite encode_close_motive in * |
   rewrite encode_mu_ind_method in * | rewrite encode_close_ind_method in *].

Theorem typing_encoding : forall Delta t A, typing Delta t A ->
  forall Gamma env, context_encoding Gamma env Delta -> ST.wf Gamma ->
  ST.typing Gamma (encode env t) (encode env A).
Proof.
  intros Delta t A H; induction H; intros Genv env HC HG.
  all: repeat match goal with
    | IH : forall (G : DB.ctx) (e : list nat), context_encoding G e ?D -> ST.wf G -> _,
      HE : context_encoding ?G ?e ?D, HW : ST.wf ?G |- _ => specialize (IH G e HE HW)
    end.
  all: encode_types; cbn [encode MuAt CloseAt payload carrier] in *.
  all: try solve [eauto 7 using ST.ty_sort, ST.ty_pi, ST.ty_sigma, ST.ty_lam, ST.ty_pair,
    ST.ty_cumul, ST.ty_unitT, ST.ty_uid, ST.ty_enumu, ST.ty_enumt, ST.ty_epi, ST.ty_idesc,
    ST.ty_interp, ST.ty_iall, SS.smart_app, SS.smart_fst, SS.smart_snd,
    SS.smart_unit, SS.smart_tag, SS.smart_nile, SS.smart_conse, SS.smart_zero, SS.smart_succ,
    SS.smart_switch, SS.smart_ivar, SS.smart_i1, SS.smart_ibot, SS.smart_iprod, SS.smart_ipi,
    SS.smart_isig, SS.smart_ichoice, SS.smart_mui, SS.smart_in_mui, SS.smart_hyps, SS.smart_ind,
    SS.smart_close, SS.smart_in_close, SS.smart_close_case, SS.smart_close_ind].
  - destruct (context_encoding_lookup _ _ _ _ _ HC H0) as [n [B [Ex [Hn HE]]]].
    rewrite Ex,HE; now apply SS.smart_var.
  - eapply ST.ty_pi; [eassumption|].
    eapply IHtyping2.
    + eapply context_encoding_extend; [exact HC|reflexivity|eassumption|eassumption].
    + eapply ST.wf_cons; eassumption.
  - eapply ST.ty_sigma; [eassumption|].
    eapply IHtyping2.
    + eapply context_encoding_extend; [exact HC|reflexivity|eassumption|eassumption].
    + eapply ST.wf_cons; eassumption.
  - destruct (pi_domain_formation _ _ _ _ _ H0) as [j HA].
    destruct (nameless.DBWeakening.typing_pi_domain _ _ _ IHtyping1 _ _ eq_refl) as [l HA'].
    eapply ST.ty_lam; [exact IHtyping1|].
    eapply IHtyping2.
    + eapply context_encoding_extend; [exact HC|reflexivity|exact HA|eassumption].
    + eapply ST.wf_cons; eassumption.
  - assert (HE : encode env t = encode env u).
    { apply encode_alpha; [reflexivity|apply alpha_closed_context;exact H0]. }
    now rewrite <- HE.
  - eapply ST.ty_conv; [eassumption|eassumption|now apply encode_conversion].
Qed.

Theorem context_representation : forall Delta, wf Delta ->
  exists Gamma env, context_encoding Gamma env Delta /\ ST.wf Gamma.
Proof.
  intros Delta H; induction H.
  - exists [],[]; split; [|constructor]. constructor; cbn; auto using NoDup, wf_nil.
    + intros x; split; [cbn;tauto|reflexivity].
    + intros n A H; destruct n;discriminate.
  - destruct IHwf as [G [env [HC HG]]]. exists (encode env A::G),(x::env); split.
    + eapply context_encoding_extend; [exact HC|reflexivity|eassumption|eassumption].
    + eapply ST.wf_cons; [exact HG|]. exact (typing_encoding _ _ _ H0 _ _ HC HG).
Qed.

Theorem typing_reflection_given : forall Gamma t A, ST.typing Gamma t A ->
  forall env Delta nt nA, context_encoding Gamma env Delta -> encode env nt = t -> encode env nA = A ->
  typing Delta nt nA.
Proof.
  intros Gamma t A HT env Delta nt nA HC Ht HA.
  destruct (typing_reflection _ _ _ HT _ _ HC) as [HD HF].
  assert (Et : encode env (decode env t) = t).
  { apply encode_decode; [exact (ce_names _ _ _ HC)|]. rewrite <- (ce_length _ _ _ HC).
    exact (sd_typing_scoped _ _ _ HT). }
  assert (EA : encode env (decode env A) = A).
  { apply encode_decode; [exact (ce_names _ _ _ HC)|]. rewrite <- (ce_length _ _ _ HC).
    exact (sd_type_scoped _ _ _ HT). }
  eapply typing_encoded_cast with (env:=env) (A:=decode env A).
  - eapply ty_alpha; [exact HD|apply (encode_env_alpha env);congruence].
  - exact HF.
  - congruence.
Qed.

Theorem named_type_correctness : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Proof.
  intros Gamma t A Ht.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [G [env [HC HG]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HG) as HT.
  destruct (nameless.DBWeakening.type_correctness _ _ _ HT) as [k HA].
  exists k. eapply typing_reflection_given; [exact HA|exact HC|reflexivity|reflexivity].
Qed.

Theorem named_weakening : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Proof.
  intros Gamma x t A B k Hfresh Ht HB.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [G [env [HC HG]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HG) as HT.
  pose proof (typing_encoding _ _ _ HB _ _ HC HG) as HB'.
  pose proof (nameless.DBWeakening.weakening _ _ _ _ _ HT HB') as Hweak.
  assert (Hnew : context_encoding (encode env B::G) (x::env) (extend Gamma x B))
    by (eapply context_encoding_extend; eauto).
  eapply typing_reflection_given; [exact Hweak|exact Hnew| |].
  - apply encode_fresh; eapply typing_fresh_not_free; eassumption.
  - apply encode_fresh. destruct (named_type_correctness _ _ _ Ht) as [j HA].
    eapply typing_fresh_not_free; eassumption.
Qed.

Theorem named_substitution : forall Gamma x A t B u,
  fresh_in Gamma x -> typing (extend Gamma x A) t B -> typing Gamma u A ->
  typing Gamma (subst u x t) (subst u x B).
Proof.
  intros Gamma x A t B u Hfresh Ht Hu.
  destruct (context_representation _ (typing_context _ _ _ Hu)) as [G [env [HC HG]]].
  destruct (named_type_correctness _ _ _ Hu) as [k HA].
  pose proof (typing_encoding _ _ _ HA _ _ HC HG) as HA'.
  pose proof (typing_encoding _ _ _ Hu _ _ HC HG) as Hu'.
  assert (Hnew : context_encoding (encode env A::G) (x::env) (extend Gamma x A))
    by (eapply context_encoding_extend;eauto).
  assert (HG' : ST.wf (encode env A::G)) by (eapply ST.wf_cons;eassumption).
  pose proof (typing_encoding _ _ _ Ht _ _ Hnew HG') as HT.
  pose proof (nameless.DBSubstitution.substitution _ _ _ _ _ HT Hu') as Hsub.
  eapply typing_reflection_given; [exact Hsub|exact HC|apply encode_subst|apply encode_subst].
Qed.
