(* Consistency stated with the empty signature (extended abstract,
   Theorem "Consistency": for every t, ∅ ⊬ t : ⟦T Δ* :: ()⟧).

   All three statements are proved and closed under the global context.
   This file is not imported by OpenSignatures.v or OpenSignaturesAudit.v
   and is not listed in _CoqProject, so the closed-assumption audit of the
   public claims is unaffected. Compile from progress/ with:
     rocq compile -Q . "" OpenSignaturesEmptySignature.v *)
From Stdlib Require Import List.
Require Import OpenSignaturesTheorems.
Import ListNotations.

(* The empty signature: the row with no constructors, under index binder x. *)
Definition empty_signature (x : nat) (IT : term) := signature x IT [].

(* ⟦T Δ* :: ()⟧: outermost constructors from the empty signature,
   recursive positions from the full definition G, at index i. *)
Definition empty_subset (IT G : term) (x : nat) (i : term) :=
  CloseAt IT (empty_signature x IT) G i.

(* Each type maps into the other, so the theorem below is equivalent to
   [consistency] (no closed term of type Bot = EnumT nilE). *)

Lemma bot_to_empty_subset : forall Gamma IT G x i,
  typing Gamma (empty_subset IT G x i) (TSort 0) ->
  exists c, typing Gamma c (arrow Bot (empty_subset IT G x i)).
Proof.
  (* c := λz. abort 0 (empty_subset IT G x i) z, using [abort_typing]. *)
  intros Gamma IT G x i HA. set (A := empty_subset IT G x i) in *.
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (Hbot : typing Gamma Bot (TSort 0)) by (apply ty_enumt, ty_nile; exact Hctx).
  destruct (exists_fresh_id Gamma []) as [z [Hz _]].
  exists (TLam z (abort 0 A (TVar z))).
  eapply arrow_intro; [exact weakening|exact Hbot|exact HA|exact Hz|].
  assert (Hctx' : wf (extend Gamma z Bot)) by (eapply wf_cons; eassumption).
  apply abort_typing.
  - eapply weakening; eassumption.
  - apply ty_var; [exact Hctx'|apply lookup_extend_same].
Qed.

Lemma empty_subset_to_bot : forall Gamma IT G x i,
  typing Gamma (empty_subset IT G x i) (TSort 0) ->
  exists c, typing Gamma c (arrow (empty_subset IT G x i) Bot).
Proof.
  (* c := λy. d (unroll IT (empty_signature x IT) G i y), where d is the
     [dead_nil] witness λz. TFst z: the description (empty_signature x IT) i
     beta-reduces to TIChoice TNilE _, whose interpretation is a Σ with
     first component of type EnumT (row_enum []) = Bot. *)
  intros Gamma IT G x i HA. set (A := empty_subset IT G x i) in *.
  set (F := empty_signature x IT).
  set (T := subst i x (row_branches IT [])).
  set (X := carrier IT G).
  set (d := let z := fresh [IT; TApp F i; X; T] in TLam z (TFst (TVar z))).
  destruct (exists_fresh_id Gamma []) as [y [Hy _]].
  exists (TLam y (TApp d (unroll IT F G i (TVar y)))).
  pose proof (typing_context _ _ _ HA) as Hctx.
  assert (Hbot : typing Gamma Bot (TSort 0)) by (apply ty_enumt, ty_nile; exact Hctx).
  eapply arrow_intro; [exact weakening|exact HA|exact Hbot|exact Hy|].
  set (Gamma' := extend Gamma y A).
  assert (Hctx' : wf Gamma') by (eapply wf_cons; eassumption).
  assert (HA' : typing Gamma' A (TSort 0)) by (eapply weakening; eassumption).
  pose proof (typing_close_application weakening _ _ _ HA' _ _ _ _ eq_refl)
    as Hinput.
  assert (Hdead : dead Gamma' IT (TApp F i) X d).
  { apply dead_nil.
    - destruct Hinput as [HIT [HF [HG Hi]]]. repeat split.
      + exact HIT.
      + eapply def_application; [exact weakening|eassumption..].
      + now apply ty_close.
    - apply cv_step, st_root. reflexivity. }
  eapply arrow_app with (A := payload IT F G i).
  - exact weakening.
  - eapply payload_formation; [exact weakening|exact Hinput].
  - apply ty_enumt, ty_nile; exact Hctx'.
  - now apply dead_sound.
  - apply unroll_typing; [exact Hinput|].
    apply ty_var; [exact Hctx'|apply lookup_extend_same].
Qed.

Theorem empty_subset_consistency : forall IT G x i t,
  ~ typing empty_ctx t (empty_subset IT G x i).
Proof.
  (* [type_correctness] and [typing_close_application] give a formation
     derivation in Type 0; applying [empty_subset_to_bot] yields a closed
     term of type Bot, contradicting [consistency]. *)
  intros IT G x i t Ht.
  destruct (type_correctness _ _ _ Ht) as [k Hk].
  destruct (typing_close_application weakening _ _ _ Hk _ _ _ _ eq_refl)
    as [HIT [HF [HG Hi]]].
  assert (HA : typing empty_ctx (empty_subset IT G x i) (TSort 0))
    by (now apply close_at_formation).
  destruct (empty_subset_to_bot _ _ _ _ _ HA) as [c Hc].
  apply (consistency (TApp c t)).
  eapply arrow_app; [exact weakening|exact HA|apply ty_enumt, ty_nile, wf_nil|exact Hc|exact Ht].
Qed.
