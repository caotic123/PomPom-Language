From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules.

Lemma sig_in_origin_literal : forall Sf i IT E c xs Phi,
    check [] IT (TSort 0) -> check [] E TEnumU ->
    check [] Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check [] i IT -> check [] c (Label E) ->
    eval (labels (TApp Sf i)) Phi -> spine_mem c Phi ->
    check [] xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) ->
    eval (labels (TApp Sf i)) Phi /\ spine_mem c Phi /\
    check [] xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)).
Proof. intros; repeat split; assumption. Qed.

Print Assumptions sig_in_origin_literal.
