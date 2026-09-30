From Stdlib Require Import List Arith Bool Lia.
Require Export TypingReflectionWork.
Require SDSmartWork.
Import ListNotations.
Module ST := SDTypingWork.
Module SS := SDSmartWork.

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
Show.
Abort.
