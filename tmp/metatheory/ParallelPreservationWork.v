(* Parallel computation preserves types, independently of eta. *)
Require Export nameless.DBComputationPreservation.

Ltac syntax_head t :=
  lazymatch t with ?f ?a => syntax_head f | _ => constr:(t) end.

Ltac comp_star_congr :=
  first [eassumption | apply rtc_refl |
    match goal with |- rtc computation ?s ?t =>
      let hs := syntax_head s in let ht := syntax_head t in constr_eq hs ht
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
  intros t u H; induction H.
  all: try (timeout 1 solve [comp_star_congr]).
  all: match goal with |- ?G => idtac G end.
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

Print Assumptions pstep_preservation.
