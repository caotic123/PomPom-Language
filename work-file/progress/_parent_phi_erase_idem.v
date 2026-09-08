(* Erasure is a projection. *)

Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma phi_erase_idempotent_parent : forall t,
    phi_erase (phi_erase t) = phi_erase t.
Proof.
  apply (tsize_strong_ind
    (fun t => phi_erase (phi_erase t) = phi_erase t)).
  intros t IH. destruct t; cbn [phi_erase].
  all: try reflexivity.
  all: f_equal.
  all: try solve [apply IH;
    try (pose proof (tsize_pos t));
    try (pose proof (tsize_pos t1));
    try (pose proof (tsize_pos t2));
    try (pose proof (tsize_pos t3));
    try (pose proof (tsize_pos t4));
    try (pose proof (tsize_pos t5)); cbn [tsize]; lia].
  induction bs as [|[c b] rest IHrest]; cbn [map].
  - reflexivity.
  - rewrite (IH c ltac:(eapply tsize_case_bs; left; reflexivity)).
    rewrite (IH b ltac:(eapply tsize_case_bs_body; left; reflexivity)).
    rewrite IHrest.
    + reflexivity.
    + intros u Hu. apply IH. cbn [tsize bsizeF] in *. lia.
Qed.

Print Assumptions phi_erase_idempotent_parent.
