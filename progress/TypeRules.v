(* Public entry point for the declarative calculus and its metatheory.
   Progress, preservation, and type-side preservation are proved. Six other main
   statements remain conjectures in their respective theorem files.
   Proof files depend on TypeRulesCore, never on this export layer. *)
Require Export TypeRulesCore.
Require Export Progress.
Require Export Preservation.
Require Export PreservationEval.
Require Export PreservationType.
Require Export Normalization.
Require Export CanonicalFormsSig.
Require Export Consistency.
Require Export ConsistencyEnum.
Require Export ConsistencyEmptySig.
Require Export AgainstSound.
