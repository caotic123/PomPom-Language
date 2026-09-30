(* Constructor inversion uses conversion injectivity, independently of eta preservation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesBeta OpenSignaturesCanonical.
Require nameless.DBClosePayload.
Import ListNotations.

Theorem named_close_payload : forall Gamma IT F G i xs,
  typing Gamma (TIn xs) (CloseAt IT F G i) ->
  typing Gamma xs (payload IT F G i).
Proof.
  intros Gamma IT F G i xs Ht.
  destruct (named_type_correctness _ _ _ Ht) as [k HT].
  pose proof (typing_close_application named_weakening _ _ _ HT _ _ _ _ eq_refl) as Hinput.
  pose proof (payload_formation named_weakening _ _ _ _ _ Hinput) as HF.
  destruct (context_representation _ (typing_context _ _ _ Ht)) as [Delta [env [HC HD]]].
  pose proof (typing_encoding _ _ _ Ht _ _ HC HD) as Ht'.
  pose proof (typing_encoding _ _ _ HF _ _ HC HD) as HF'.
  assert (Hpayload : ST.type_wf Delta (encode env (payload IT F G i))) by (exists 0; exact HF').
  pose proof (nameless.DBClosePayload.close_payload_generation _ _ _ Ht'
    _ _ _ _ _ eq_refl (nameless.DBCore.cv_refl _) Hpayload) as Hxs.
  eapply typing_reflection_given; [exact Hxs|exact HC|reflexivity|reflexivity].
Qed.
