(* Parallel computation preserves types, independently of eta. *)
Require Export nameless.DBComputationPreservation.

Ltac syntax_head t :=
  lazymatch t with ?f ?a => syntax_head f | _ => constr:(t) end.

(* Reject root computations before trying permutations of congruence steps. *)
Ltac comp_congruence_possible s t :=
  first [constr_eq s t |
    match goal with H : rtc computation ?a ?b |- _ =>
      constr_eq s a; constr_eq t b
    end |
    lazymatch s with ?f ?a => lazymatch t with ?g ?b =>
      comp_congruence_possible f g; comp_congruence_possible a b
    end end].

Ltac comp_star_congr :=
  first [eassumption | apply rtc_refl |
    match goal with |- rtc computation ?s ?t =>
      let hs := syntax_head s in let ht := syntax_head t in constr_eq hs ht;
      comp_congruence_possible s t
    end;
    match goal with
    | H : rtc computation ?a ?b |- rtc computation ?s ?t =>
      match s with context C [a] =>
        let middle := context C [b] in
        tryif constr_eq s middle then fail else
        let F := constr:(fun z : term => ltac:(let v := context C [z] in exact v)) in
        eapply rtc_trans with (y:=middle);
        [eapply (rtc_map_rel _ _ computation computation F);
          [intros; solve [eauto 4 using computation] | exact H]
        | comp_star_congr]
      end
    end].

Lemma pstep_computations : forall t u, pstep t u -> rtc computation t u.
Proof.
  intros t u H; induction H; try solve [comp_star_congr].
  - eapply rtc_trans with (y:=(TApp (TLam b') a'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TFst (TPair a' b)));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSnd (TPair a b')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TEPi k TNilE P));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TEPi k (TConsE tag E') P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSwitch k (TConsE tag E) P (TPair p' ps) TEZero));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TSwitch k (TConsE tag E') P' (TPair p ps') (TESucc n')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT (TIVar i') X'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT TI1 X));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT TIBot X));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIProd A' B') X'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIPi A' D') X'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TISig A' D') X'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInterp IT' (TIChoice E' D') X'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT (TIVar i') X x' P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT TI1 X TUnit P));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT TIBot X x P));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIProd A' B') X' (TPair a' b') P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIPi A' D') X' f' P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TISig A D') X' (TPair a' x') P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TIAll IT' (TIChoice E D') X' (TPair e' x') P'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT (TIVar i') X P h' x'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT TI1 X P h TUnit));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT TIBot X P h x));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIProd A' B') X' P' h' (TPair a' b')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIPi A D') X' P' h' f'));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TISig A D') X' P' h' (TPair a' x')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(THyps IT' (TIChoice E D') X' P' h' (TPair e' x')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TInd IT' D' P' st' i' (TIn xs')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TCloseCase k IT F G i Q b' (TIn xs')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].
  - eapply rtc_trans with (y:=(TCloseInd IT' G' P' st' F' i' (TIn xs')));
      [comp_star_congr|apply rtc_one; apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive; cbn; repeat rewrite lift_one_one_zero; reflexivity].

Qed.

Theorem pstep_preservation : forall t u, pstep t u ->
  forall Gamma T, typing Gamma t T -> typing Gamma u T.
Proof. intros; eapply computations_preservation; [apply pstep_computations; eassumption|eassumption]. Qed.

Theorem psteps_preservation : forall t u, rtc pstep t u ->
  forall Gamma T, typing Gamma t T -> typing Gamma u T.
Proof. intros t u H; induction H; eauto using pstep_preservation. Qed.

Lemma computation_pstep : forall t u, computation t u -> pstep t u.
Proof.
  intros t u H; induction H.
  all: try solve [apply root_pstep; assumption].
  all: solve [constructor; auto using pstep_refl].
Qed.

Lemma computations_lift : forall t u, rtc computation t u -> forall d c,
  rtc computation (lift d c t) (lift d c u).
Proof.
  intros t u H; induction H; intros; [constructor|].
  eapply rtc_trans; [|apply IHrtc].
  apply pstep_computations, pstep_lift, computation_pstep; assumption.
Qed.

Print Assumptions pstep_preservation.
