Require Import TypeRules Progress.
From Stdlib Require Import List.
Import ListNotations.

Lemma erase_conv_test : forall t u, conv t u ->
    fconv (phi_erase t) (phi_erase u).
Proof.
  intros t u H. induction H; cbn; eauto using fconv, fstep, phi_erase_step.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (rewrite phi_erase_lift; apply fc_step, fs_eta).
  all: try (repeat rewrite map_app; cbn;
    eapply fconv_map2; eauto using fstep).
  - eapply (fconv_map2
      (fun x y => TCase x y
        (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)));
      eauto using fstep.
  - repeat rewrite map_app. cbn.
    eapply (fconv_map2
      (fun x y => TCase (phi_erase M) (phi_erase Q)
        (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs1 ++
         (x,y) :: map (fun '(c,b) => (phi_erase c, phi_erase b)) bs2)));
      eauto using fstep.
Qed.
