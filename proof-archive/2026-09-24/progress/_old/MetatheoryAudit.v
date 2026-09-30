(* Public export and assumption audit. *)
Require Import TypeRules.
From Stdlib Require Import List.
Import ListNotations.

Check progress.
Check progress_proved.
Check preservation.
Check preservation_eval.
Check preservation_type.
Check normalization.
Check canonical_forms_sig.
Check consistency.
Check consistency_enum.
Check consistency_empty_sig.
Check against_sound.

(* These results must remain closed. *)
Print Assumptions progress.
Print Assumptions progress_proved.
Print Assumptions preservation.
Print Assumptions preservation_type.

(* Multi-step preservation is now closed through [preservation]. *)
Print Assumptions preservation_eval.
