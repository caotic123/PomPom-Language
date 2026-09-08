(* Core pstep reflection through phi_erase. *)

Require Import Progress _glm_phi_erase_pstep_reflect_shapes _parent_phi_erase_sort_algebra.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Theorem phi_erase_pstep_reflect_parent :
  forall t u, pstep (phi_erase t) u ->
    exists t', pstep t t' /\ phi_erase t' = u.
Proof.
  apply (tsize_strong_ind (fun t => forall u,
    pstep (phi_erase t) u -> exists t', pstep t t' /\ phi_erase t' = u)).
  intros t IH u H.
  destruct t as [n|k|x1 x2|b|f a|s1 s2|p1 p2|p|q| | | |s| | |tg E|e| |n0|eE eP|e0 p0 q0 r0|it|iv| |a1 b1|sD tD|sD2 tD2|eC tC|d x|r|sf|xin|rP pP sP iP xP|dA xA xsA pA|dH xH pH hH xsH|la|ln|la2 a2 l2|m qq bs];
    cbn [phi_erase] in H.
  - inversion H; subst. exists (TVar n). split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists (TSort k). split; [apply pstep_refl | reflexivity].
  - inversion H; subst.
    destruct (IH x1 ltac:(cbn [tsize]; pose proof (tsize_pos x2); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH x2 ltac:(cbn [tsize]; pose proof (tsize_pos x1); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    exists (TPi a1' b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH b ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [b1' [Hb1' Heb1']].
    exists (TLam b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH f ltac:(cbn [tsize]; pose proof (tsize_pos a); lia) _ ltac:(eassumption))
        as [f1' [Hf1' Hef1']].
      destruct (IH a ltac:(cbn [tsize]; pose proof (tsize_pos f); lia) _ ltac:(eassumption))
        as [a1' [Ha1' Hea1']].
      exists (TApp f1' a1'). split; [constructor; assumption | cbn; congruence].
    + destruct (erase_shape_lam_glm f _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [b0 [Hf0 Heb0]].
      subst f.
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a); lia) _
        ltac:(rewrite Heb0; eassumption))
        as [b1' [Hb1' Heb1']].
      destruct (IH a ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); lia) _ ltac:(eassumption))
        as [a1' [Ha1' Hea1']].
      exists (subst a1' 0 b1'). split.
      * eapply ps_beta; eassumption.
      * rewrite phi_erase_subst. congruence.
  - inversion H; subst.
    destruct (IH s1 ltac:(cbn [tsize]; pose proof (tsize_pos s2); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH s2 ltac:(cbn [tsize]; pose proof (tsize_pos s1); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    exists (TSigma a1' b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH p1 ltac:(cbn [tsize]; pose proof (tsize_pos p2); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH p2 ltac:(cbn [tsize]; pose proof (tsize_pos p1); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    exists (TPair a1' b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH p ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [p1' [Hp1' Hep1']].
      exists (TFst p1'). split; [constructor; assumption | cbn; congruence].
    + destruct (erase_shape_pair_glm p _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [a0 [b0 [Ht [Hea Heb]]]].
      subst p.
      destruct (IH a0 ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); lia) _
        ltac:(rewrite Hea; eassumption))
        as [a1' [Ha1' Hea1']].
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); lia) _
        ltac:(rewrite Heb; eassumption))
        as [b1' [Hb1' Heb1']].
      exists a1'. split.
      * eapply ps_fst_pair; eassumption.
      * congruence.
  - inversion H; subst.
    + destruct (IH q ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [p1' [Hp1' Hep1']].
      exists (TSnd p1'). split; [constructor; assumption | cbn; congruence].
    + destruct (erase_shape_pair_glm q _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [a0 [b0 [Ht [Hea Heb]]]].
      subst q.
      destruct (IH a0 ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); lia) _
        ltac:(rewrite Hea; eassumption))
        as [a1' [Ha1' Hea1']].
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); lia) _
        ltac:(rewrite Heb; eassumption))
        as [b1' [Hb1' Heb1']].
      exists b1'. split.
      * eapply ps_snd_pair; eassumption.
      * congruence.
  - inversion H; subst. exists TUnitT. split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists TUnit. split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists TUId. split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists (TTag s). split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists TEnumU. split; [apply pstep_refl | reflexivity].
  - inversion H; subst. exists TNilE. split; [apply pstep_refl | reflexivity].
  - inversion H; subst.
    destruct (IH tg ltac:(cbn [tsize]; pose proof (tsize_pos E); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH E ltac:(cbn [tsize]; pose proof (tsize_pos tg); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    exists (TConsE a1' b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH e ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [e1' [He1' Hee1']].
    exists (TEnumT e1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst. exists TEZero. split; [apply pstep_refl | reflexivity].
  - inversion H; subst.
    destruct (IH n0 ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [n1' [Hn1' Hen1']].
    exists (TESucc n1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH eE ltac:(cbn [tsize]; pose proof (tsize_pos eP); lia) _ ltac:(eassumption))
        as [e1' [He1' Hee1']].
      destruct (IH eP ltac:(cbn [tsize]; pose proof (tsize_pos eE); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TEPi e1' p1'). split; [constructor; assumption | cbn; congruence].
    + pose proof (erase_shape_nile_glm eE ltac:(first [eassumption | (symmetry; eassumption)])) as Heq.
      subst eE.
      destruct (IH eP ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [p1' [Hp1' Hep1']].
      exists TUnitT. split.
      * eapply ps_epi_nil; eassumption.
      * cbn; reflexivity.
    + destruct (erase_shape_conse_glm eE _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [tg0 [e0 [Heq [Hetg Hee]]]].
      subst eE.
      destruct (IH tg0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos eP); lia) _
        ltac:(rewrite Hetg; eassumption))
        as [tg1' [Htg1' Hetg1']].
      destruct (IH e0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos eP); lia) _
        ltac:(rewrite Hee; eassumption))
        as [e1' [He1' Hee1']].
      destruct (IH eP ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TSigma (TApp p1' TEZero)
        (lift 1 0 (TEPi e1' (TLam (TApp (lift 1 0 p1') (TESucc (TVar 0))))))).
      split.
      * eapply ps_epi_cons; eassumption.
      * cbn [phi_erase]. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hep1', Hee1'. reflexivity.
  - inversion H; subst.
    + destruct (IH e0 ltac:(cbn [tsize]; pose proof (tsize_pos p0); pose proof (tsize_pos q0); pose proof (tsize_pos r0); lia) _ ltac:(eassumption))
        as [e1' [He1' Hee1']].
      destruct (IH p0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos q0); pose proof (tsize_pos r0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH q0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos p0); pose proof (tsize_pos r0); lia) _ ltac:(eassumption))
        as [q1' [Hq1' Heq1']].
      destruct (IH r0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos p0); pose proof (tsize_pos q0); lia) _ ltac:(eassumption))
        as [r1' [Hr1' Her1']].
      exists (TSwitch e1' p1' q1' r1'). split; [repeat constructor; assumption | cbn; congruence].
    + destruct (erase_shape_conse_glm e0 _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [tg0 [e0' [Heq0 [Hetg Hee]]]].
      destruct (erase_shape_pair_glm q0 _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [pa0 [ps0 [Heqq [Hepa Heps]]]].
      pose proof (erase_shape_ezero_glm r0 ltac:(first [eassumption | (symmetry; eassumption)])) as Heqr.
      subst e0 q0 r0.
      destruct (IH tg0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); lia) _
        ltac:(rewrite Hetg; eassumption)) as [tg1' [Htg1' Hetg1']].
      destruct (IH e0' ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); lia) _
        ltac:(rewrite Hee; eassumption)) as [e1' [He1' Hee1']].
      destruct (IH p0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH pa0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos ps0); lia) _
        ltac:(rewrite Hepa; eassumption)) as [pa1' [Hpa1' Hepa1']].
      destruct (IH ps0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); lia) _
        ltac:(rewrite Heps; eassumption)) as [ps1' [Hps1' Heps1']].
      exists pa1'. split.
      * eapply ps_switch_zero; eassumption.
      * congruence.
    + destruct (erase_shape_conse_glm e0 _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [tg0 [e0' [Heq0 [Hetg Hee]]]].
      destruct (erase_shape_pair_glm q0 _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [pa0 [ps0 [Heqq [Hepa Heps]]]].
      destruct (erase_shape_esucc_glm r0 _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [n0 [Hrn Hemn]].
      subst e0 q0 r0.
      destruct (IH tg0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); pose proof (tsize_pos n0); lia) _
        ltac:(rewrite Hetg; eassumption)) as [tg1' [Htg1' Hetg1']].
      destruct (IH e0' ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); pose proof (tsize_pos n0); lia) _
        ltac:(rewrite Hee; eassumption)) as [e1' [He1' Hee1']].
      destruct (IH p0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); pose proof (tsize_pos n0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH pa0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos ps0); pose proof (tsize_pos n0); lia) _
        ltac:(rewrite Hepa; eassumption)) as [pa1' [Hpa1' Hepa1']].
      destruct (IH ps0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos n0); lia) _
        ltac:(rewrite Heps; eassumption)) as [ps1' [Hps1' Heps1']].
      destruct (IH n0 ltac:(cbn [tsize] in *; pose proof (tsize_pos tg0); pose proof (tsize_pos e0'); pose proof (tsize_pos p0); pose proof (tsize_pos pa0); pose proof (tsize_pos ps0); lia) _
        ltac:(rewrite Hemn; eassumption)) as [n1' [Hn1' Hen1']].
      exists (TSwitch e1' (TLam (TApp (lift 1 0 p1') (TESucc (TVar 0)))) ps1' n1').
      split.
      * eapply ps_switch_succ; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hee1', Hep1', Heps1', Hen1'. reflexivity.
  - inversion H; subst.
    destruct (IH it ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [i1' [Hi1' Hei1']].
    exists (TIDesc i1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH iv ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [i1' [Hi1' Hei1']].
    exists (TIVar i1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst. exists TI1. split; [apply pstep_refl | reflexivity].
  - inversion H; subst.
    destruct (IH a1 ltac:(cbn [tsize]; pose proof (tsize_pos b1); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH b1 ltac:(cbn [tsize]; pose proof (tsize_pos a1); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    exists (TIProd a1' b1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH sD ltac:(cbn [tsize]; pose proof (tsize_pos tD); lia) _ ltac:(eassumption))
      as [s1' [Hs1' Hes1']].
    destruct (IH tD ltac:(cbn [tsize]; pose proof (tsize_pos sD); lia) _ ltac:(eassumption))
      as [t1' [Ht1' Het1']].
    exists (TIPi s1' t1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH sD2 ltac:(cbn [tsize]; pose proof (tsize_pos tD2); lia) _ ltac:(eassumption))
      as [s1' [Hs1' Hes1']].
    destruct (IH tD2 ltac:(cbn [tsize]; pose proof (tsize_pos sD2); lia) _ ltac:(eassumption))
      as [t1' [Ht1' Het1']].
    exists (TISig s1' t1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH eC ltac:(cbn [tsize]; pose proof (tsize_pos tC); lia) _ ltac:(eassumption))
      as [e1' [He1' Hee1']].
    destruct (IH tC ltac:(cbn [tsize]; pose proof (tsize_pos eC); lia) _ ltac:(eassumption))
      as [t1' [Ht1' Het1']].
    exists (TIChoice e1' t1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH d ltac:(cbn [tsize]; pose proof (tsize_pos x); lia) _ ltac:(eassumption))
        as [d1' [Hd1' Hed1']].
      destruct (IH x ltac:(cbn [tsize]; pose proof (tsize_pos d); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TInterp d1' x1'). split; [constructor; assumption | cbn; congruence].
    + destruct (erase_shape_ivar_glm d _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [i0 [Hd0 Hei0]].
      subst d.
      destruct (IH i0 ltac:(cbn [tsize] in *; pose proof (tsize_pos x); lia) _
        ltac:(rewrite Hei0; eassumption)) as [i1' [Hi1' Hei1']].
      destruct (IH x ltac:(cbn [tsize] in *; pose proof (tsize_pos i0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TApp x1' i1'). split.
      * eapply ps_interp_var; eassumption.
      * cbn; congruence.
    + pose proof (erase_shape_i1_glm d ltac:(first [eassumption | (symmetry; eassumption)])) as Hd0.
      subst d.
      destruct (IH x ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [x1' [Hx1' Hex1']].
      exists TUnitT. split.
      * eapply ps_interp_one; eassumption.
      * cbn; reflexivity.
    + destruct (erase_shape_iprod_glm d _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [a0 [b0 [Hd0 [Hea Heb]]]].
      subst d.
      destruct (IH a0 ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Hea; eassumption)) as [a1' [Ha1' Hea1']].
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Heb; eassumption)) as [b1' [Hb1' Heb1']].
      destruct (IH x ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TSigma (TInterp a1' x1') (lift 1 0 (TInterp b1' x1'))).
      split.
      * eapply ps_interp_prod; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hea1', Heb1', Hex1'. reflexivity.
    + destruct (erase_shape_ipi_glm d _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      subst d.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH x ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TPi s1' (TInterp (TApp (lift 1 0 u1') (TVar 0)) (lift 1 0 x1'))).
      split.
      * eapply ps_interp_pi; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hes1', Heu1', Hex1'. reflexivity.
    + destruct (erase_shape_isig_glm d _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      subst d.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH x ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TSigma s1' (TInterp (TApp (lift 1 0 u1') (TVar 0)) (lift 1 0 x1'))).
      split.
      * eapply ps_interp_sig; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hes1', Heu1', Hex1'. reflexivity.
    + destruct (erase_shape_ichoice_glm d _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [e0 [u0 [Hd0 [Hee Heu]]]].
      subst d.
      destruct (IH e0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Hee; eassumption)) as [e1' [He1' Hee1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos x); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH x ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TSigma (TEnumT e1') (TInterp (TApp (lift 1 0 u1') (TVar 0)) (lift 1 0 x1'))).
      split.
      * eapply ps_interp_choice; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hee1', Heu1', Hex1'. reflexivity.
  - inversion H; subst.
    destruct (IH r ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [r1' [Hr1' Her1']].
    exists (TMuI r1'). split; [constructor; assumption | cbn; congruence].
  - cbn [phi_erase] in H.
    inversion H; subst.
    assert (HS' : S' = TUnit) by (inversion H1; reflexivity).
    subst S'. exists (TMuS sf). split; [apply pstep_refl | cbn; reflexivity].
  - inversion H; subst.
    destruct (IH xin ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [x1' [Hx1' Hex1']].
    exists (TIn x1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH rP ltac:(cbn [tsize]; pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia) _ ltac:(eassumption))
        as [r1' [Hr1' Her1']].
      destruct (IH pP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH sP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia) _ ltac:(eassumption))
        as [s1' [Hs1' Hes1']].
      destruct (IH iP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos xP); lia) _ ltac:(eassumption))
        as [i1' [Hi1' Hei1']].
      destruct (IH xP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      exists (TInd r1' p1' s1' i1' x1'). split; [repeat constructor; assumption | cbn; congruence].
    + destruct (erase_shape_tin_glm xP _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [xs0 [Hx0 Hexs]].
      subst xP.
      destruct (IH rP ltac:(cbn [tsize] in *; pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xs0); lia) _ ltac:(eassumption))
        as [r1' [Hr1' Her1']].
      destruct (IH pP ltac:(cbn [tsize] in *; pose proof (tsize_pos rP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xs0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH sP ltac:(cbn [tsize] in *; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos iP); pose proof (tsize_pos xs0); lia) _ ltac:(eassumption))
        as [s1' [Hs1' Hes1']].
      destruct (IH iP ltac:(cbn [tsize] in *; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos xs0); lia) _ ltac:(eassumption))
        as [i1' [Hi1' Hei1']].
      destruct (IH xs0 ltac:(cbn [tsize] in *; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); lia) _
        ltac:(rewrite Hexs; eassumption)) as [xs1' [Hxs1' Hexs1']].
      exists (TApp (TApp (TApp s1' i1') xs1')
        (THyps (TApp r1' i1') (TMuI r1') p1'
          (TLam (TLam (TInd (lift 2 0 r1') (lift 2 0 p1') (lift 2 0 s1') (TVar 1) (TVar 0)))) xs1')).
      split.
      * eapply ps_ind_red; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Her1', Hep1', Hes1', Hei1', Hexs1'. reflexivity.
  - inversion H; subst.
    + destruct (IH dA ltac:(cbn [tsize]; pose proof (tsize_pos xA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [d1' [Hd1' Hed1']].
      destruct (IH xA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH xsA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      destruct (IH pA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TIAll d1' x1' xs1' p1'). split; [repeat constructor; assumption | cbn; congruence].
    + destruct (erase_shape_ivar_glm dA _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [j0 [Hd0 Hej0]].
      subst dA.
      destruct (IH j0 ltac:(cbn [tsize] in *; pose proof (tsize_pos xA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hej0; eassumption)) as [j1' [Hj1' Hej1']].
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH xsA ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TApp p1' (TPair j1' xs1')). split.
      * eapply ps_iall_var; eassumption.
      * cbn; congruence.
    + pose proof (erase_shape_i1_glm dA ltac:(first [eassumption | (symmetry; eassumption)])) as Hd0.
      pose proof (erase_shape_unit_glm xsA ltac:(first [eassumption | (symmetry; eassumption)])) as Hxs0.
      subst dA xsA.
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos xA); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists TUnitT. split.
      * eapply ps_iall_one; eassumption.
      * cbn; reflexivity.
    + destruct (erase_shape_iprod_glm dA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [a0 [b0 [Hd0 [Hea Heb]]]].
      destruct (erase_shape_pair_glm xsA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [xa0 [xb0 [Hxs0 [Hexa Hexb]]]].
      subst dA xsA.
      destruct (IH a0 ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); pose proof (tsize_pos xA); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hea; eassumption)) as [a1' [Ha1' Hea1']].
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos xA); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Heb; eassumption)) as [b1' [Hb1' Heb1']].
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH xa0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xA); pose proof (tsize_pos xb0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hexa; eassumption)) as [xa1' [Hxa1' Hexa1']].
      destruct (IH xb0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xA); pose proof (tsize_pos xa0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hexb; eassumption)) as [xb1' [Hxb1' Hexb1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xA); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TSigma (TIAll a1' x1' xa1' p1') (lift 1 0 (TIAll b1' x1' xb1' p1'))).
      split.
      * eapply ps_iall_prod; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hea1', Heb1', Hex1', Hexa1', Hexb1', Hep1'. reflexivity.
    + destruct (erase_shape_ipi_glm dA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      subst dA.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH xsA ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TPi s1' (TIAll (TApp (lift 1 0 u1') (TVar 0)) (lift 1 0 x1') (TApp (lift 1 0 xs1') (TVar 0)) (lift 1 0 p1'))).
      split.
      * eapply ps_iall_pi; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Hes1', Heu1', Hex1', Hexs1', Hep1'. reflexivity.
    + destruct (erase_shape_isig_glm dA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      destruct (erase_shape_pair_glm xsA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [ss0 [xx0 [Hxs0 [Hess Hexx]]]].
      subst dA xsA.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos xA); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH ss0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hess; eassumption)) as [ss1' [Hss1' Hess1']].
      destruct (IH xx0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ss0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hexx; eassumption)) as [xx1' [Hxx1' Hexx1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TIAll (TApp u1' ss1') x1' xx1' p1').
      split.
      * eapply ps_iall_sig; eassumption.
      * cbn; congruence.
    + destruct (erase_shape_ichoice_glm dA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [e0 [u0 [Hd0 [Hee Heu]]]].
      destruct (erase_shape_pair_glm xsA _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [ee0 [xx0 [Hxs0 [Heee Hexx]]]].
      subst dA xsA.
      destruct (IH e0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hee; eassumption)) as [e1' [He1' Hee1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos xA); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xA ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH ee0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos xx0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Heee; eassumption)) as [ee1' [Hee2' Heee1']].
      destruct (IH xx0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ee0); pose proof (tsize_pos pA); lia) _
        ltac:(rewrite Hexx; eassumption)) as [xx1' [Hxx1' Hexx1']].
      destruct (IH pA ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xA); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      exists (TIAll (TApp u1' ee1') x1' xx1' p1').
      split.
      * eapply ps_iall_choice; eassumption.
      * cbn; congruence.
  - inversion H; subst.
    + destruct (IH dH ltac:(cbn [tsize]; pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [d1' [Hd1' Hed1']].
      destruct (IH xH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH xsH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      exists (THyps d1' x1' p1' h1' xs1'). split; [repeat constructor; assumption | cbn; congruence].
    + destruct (erase_shape_ivar_glm dH _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [j0 [Hd0 Hej0]].
      subst dH.
      destruct (IH j0 ltac:(cbn [tsize] in *; pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _
        ltac:(rewrite Hej0; eassumption)) as [j1' [Hj1' Hej1']].
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH xsH ltac:(cbn [tsize] in *; pose proof (tsize_pos j0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      exists (TApp (TApp h1' j1') xs1'). split.
      * eapply ps_hyps_var; eassumption.
      * cbn; congruence.
    + pose proof (erase_shape_i1_glm dH ltac:(first [eassumption | (symmetry; eassumption)])) as Hd0.
      pose proof (erase_shape_unit_glm xsH ltac:(first [eassumption | (symmetry; eassumption)])) as Hxs0.
      subst dH xsH.
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos pH); pose proof (tsize_pos hH); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos xH); pose proof (tsize_pos hH); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos xH); pose proof (tsize_pos pH); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      exists TUnit. split.
      * eapply ps_hyps_one; eassumption.
      * cbn; reflexivity.
    + destruct (erase_shape_iprod_glm dH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [a0 [b0 [Hd0 [Hea Heb]]]].
      destruct (erase_shape_pair_glm xsH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [xa0 [xb0 [Hxs0 [Hexa Hexb]]]].
      subst dH xsH.
      destruct (IH a0 ltac:(cbn [tsize] in *; pose proof (tsize_pos b0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _
        ltac:(rewrite Hea; eassumption)) as [a1' [Ha1' Hea1']].
      destruct (IH b0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _
        ltac:(rewrite Heb; eassumption)) as [b1' [Hb1' Heb1']].
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos xa0); pose proof (tsize_pos xb0); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH xa0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xb0); lia) _
        ltac:(rewrite Hexa; eassumption)) as [xa1' [Hxa1' Hexa1']].
      destruct (IH xb0 ltac:(cbn [tsize] in *; pose proof (tsize_pos a0); pose proof (tsize_pos b0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xa0); lia) _
        ltac:(rewrite Hexb; eassumption)) as [xb1' [Hxb1' Hexb1']].
      exists (TPair (THyps a1' x1' p1' h1' xa1') (THyps b1' x1' p1' h1' xb1')).
      split.
      * eapply ps_hyps_prod; eassumption.
      * cbn; congruence.
    + destruct (erase_shape_ipi_glm dH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      subst dH.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos xsH); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH xsH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); lia) _ ltac:(eassumption))
        as [xs1' [Hxs1' Hexs1']].
      exists (TLam (THyps (TApp (lift 1 0 u1') (TVar 0)) (lift 1 0 x1') (lift 1 0 p1') (lift 1 0 h1') (TApp (lift 1 0 xs1') (TVar 0)))).
      split.
      * eapply ps_hyps_pi; eassumption.
      * cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. cbn [phi_erase] in *. repeat rewrite phi_erase_lift in *. rewrite Heu1', Hex1', Hep1', Heh1', Hexs1'. reflexivity.
    + destruct (erase_shape_isig_glm dH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [s0 [u0 [Hd0 [Hes Heu]]]].
      destruct (erase_shape_pair_glm xsH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [ss0 [xx0 [Hxs0 [Hess Hexx]]]].
      subst dH xsH.
      destruct (IH s0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Hes; eassumption)) as [s1' [Hs1' Hes1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos ss0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH ss0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Hess; eassumption)) as [ss1' [Hss1' Hess1']].
      destruct (IH xx0 ltac:(cbn [tsize] in *; pose proof (tsize_pos s0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ss0); lia) _
        ltac:(rewrite Hexx; eassumption)) as [xx1' [Hxx1' Hexx1']].
      exists (THyps (TApp u1' ss1') x1' p1' h1' xx1').
      split.
      * eapply ps_hyps_sig; eassumption.
      * cbn; congruence.
    + destruct (erase_shape_ichoice_glm dH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [e0 [u0 [Hd0 [Hee Heu]]]].
      destruct (erase_shape_pair_glm xsH _ _ ltac:(first [eassumption | (symmetry; eassumption)]))
        as [ee0 [xx0 [Hxs0 [Heee Hexx]]]].
      subst dH xsH.
      destruct (IH e0 ltac:(cbn [tsize] in *; pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Hee; eassumption)) as [e1' [He1' Hee1']].
      destruct (IH u0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Heu; eassumption)) as [u1' [Hu1' Heu1']].
      destruct (IH xH ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [x1' [Hx1' Hex1']].
      destruct (IH pH ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [p1' [Hp1' Hep1']].
      destruct (IH hH ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos ee0); pose proof (tsize_pos xx0); lia) _ ltac:(eassumption))
        as [h1' [Hh1' Heh1']].
      destruct (IH ee0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xx0); lia) _
        ltac:(rewrite Heee; eassumption)) as [ee1' [Hee2' Heee1']].
      destruct (IH xx0 ltac:(cbn [tsize] in *; pose proof (tsize_pos e0); pose proof (tsize_pos u0); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos ee0); lia) _
        ltac:(rewrite Hexx; eassumption)) as [xx1' [Hxx1' Hexx1']].
      exists (THyps (TApp u1' ee1') x1' p1' h1' xx1').
      split.
      * eapply ps_hyps_choice; eassumption.
      * cbn; congruence.
  - inversion H; subst.
    destruct (IH la ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [a1' [Ha1' Hea1']].
    exists (TList a1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH ln ltac:(cbn [tsize]; lia) _ ltac:(eassumption)) as [a1' [Ha1' Hea1']].
    exists (TLNil a1'). split; [constructor; assumption | cbn; congruence].
  - inversion H; subst.
    destruct (IH la2 ltac:(cbn [tsize]; pose proof (tsize_pos a2); pose proof (tsize_pos l2); lia) _ ltac:(eassumption))
      as [a1' [Ha1' Hea1']].
    destruct (IH a2 ltac:(cbn [tsize]; pose proof (tsize_pos la2); pose proof (tsize_pos l2); lia) _ ltac:(eassumption))
      as [b1' [Hb1' Heb1']].
    destruct (IH l2 ltac:(cbn [tsize]; pose proof (tsize_pos la2); pose proof (tsize_pos a2); lia) _ ltac:(eassumption))
      as [l1' [Hl1' Hel1']].
    exists (TLCons a1' b1' l1'). split; [repeat constructor; assumption | cbn; congruence].
  - inversion H; subst.
    + destruct (IH m ltac:(cbn [tsize]; pose proof (tsize_pos qq); lia) _ ltac:(eassumption))
        as [m1' [Hm1' Hem1']].
      destruct (IH qq ltac:(cbn [tsize]; pose proof (tsize_pos m); lia) _ ltac:(eassumption))
        as [q1' [Hq1' Heq1']].
      clear H.
      assert (Hbr : exists bs1', pbranches bs bs1' /\ map (fun '(c,b) => (phi_erase c, phi_erase b)) bs1' = bs').
      { revert bs' H6.
        Show.
        induction bs as [|[c0 b0] rest IHrest]; intros bs' Hpb.
        * cbn [map] in Hpb.
          Show.
          inversion Hpb; subst.
          Show.
          exists [].
          Show.
          split.
          Show.
          { constructor.
            Show. }
          { Show.
            reflexivity. }
        * cbn [map] in Hpb.
          Show.
          inversion Hpb; subst.
          Show.
          assert (Hc0size : tsize c0 < tsize (TCase m qq ((c0, b0) :: rest))).
          { Show.
            cbn [tsize bsize bsizeF] in *.
            Show.
            pose proof (tsize_pos b0).
            Show.
            pose proof (tsize_pos m).
            Show.
            pose proof (tsize_pos qq).
            Show.
            lia. }
          Show.
          destruct (IH c0 Hc0size _ H2)
            as [c1' [Hc1' Hec1']].
          Show.
          assert (Hb0size : tsize b0 < tsize (TCase m qq ((c0, b0) :: rest))).
          { Show.
            cbn [tsize bsize bsizeF] in *.
            Show.
            pose proof (tsize_pos c0).
            Show.
            pose proof (tsize_pos m).
            Show.
            pose proof (tsize_pos qq).
            Show.
            lia. }
          Show.
          destruct (IH b0 Hb0size _ H6)
            as [b1' [Hb1' Heb1']].
          Show.
          assert (HrestSize : tsize (TCase m qq rest) < tsize (TCase m qq ((c0, b0) :: rest))).
          { Show.
            cbn [tsize bsize bsizeF] in *.
            Show.
            pose proof (tsize_pos c0).
            Show.
            pose proof (tsize_pos b0).
            Show.
            lia. }
          Show.
        assert (HrestPrem : forall u, tsize u < tsize (TCase m qq rest) -> forall u0, pstep (phi_erase u) u0 -> exists t', pstep u t' /\ phi_erase t' = u0).
        { Show.
          intros u Hu u0 Hu0.
          Show.
          apply IH.
          Show.
          - lia.
            Show.
          - exact Hu0.
            Show. }
          Show.
          destruct (IHrest HrestPrem bs'0 H7)
            as [rest1' [Hrest1 Herest1]].
          Show.
          exists ((c1', b1') :: rest1').
          Show.
          split.
          Show.
          { constructor; assumption.
            Show. }
          { Show.
            cbn [map].
            Show.
            congruence. } }
      Show.
      destruct Hbr as [bs1' [Hbr1 Hbr2]].
      Show.
      exists (TCase m1' q1' bs1').
      Show.
      split.
      Show.
      { constructor; assumption.
        Show. }
      { Show.
        cbn [phi_erase map].
        Show.
        congruence. }
    + destruct (erase_shape_tin_glm m _ (eq_sym H0)) as [px0 [Hm0 Hex0]].
      Show.
      subst m.
      Show.
      destruct (erase_shape_pair_glm px0 _ _ Hex0) as [a0 [xs0 [Hpx [Hea Hexs]]]].
      Show.
      subst px0.
      Show.
      destruct (phi_erase_nth_inv _ _ _ _ H3) as [c0 [b0 [Hnth [Hec Heb]]]].
      Show.
      assert (Hcpos : enum_pos c0 n).
      { Show.
        rewrite <- Hec in H4.
        Show.
        eapply phi_erase_enum_pos_reflect_parent.
        Show.
        exact H4. }
      Show.
      assert (Hapos : enum_pos a0 n).
      { Show.
        rewrite <- Hea in H5.
        Show.
        eapply phi_erase_enum_pos_reflect_parent.
        Show.
        exact H5. }
      Show.
      assert (Hpref : forall j cj0 bj0, j < k -> nth_error bs j = Some (cj0, bj0) -> exists nj, enum_pos cj0 nj /\ nj <> n).
      { Show.
        intros j cj0 bj0 Hj Hnthj.
        Show.
        pose proof (phi_erase_nth_error _ _ _ _ Hnthj) as HnthE.
        Show.
        destruct (H6 j _ _ Hj HnthE) as [nj [Hpos Hneq]].
        Show.
        exists nj.
        Show.
        split.
        Show.
        { eapply phi_erase_enum_pos_reflect_parent.
          Show.
          exact Hpos. }
        { Show.
          exact Hneq. } }
      Show.
      assert (HxsSize : tsize xs0 < tsize (TCase (TIn (TPair a0 xs0)) qq bs)).
      { Show.
        cbn [tsize bsize bsizeF] in *.
        Show.
        pose proof (tsize_pos a0).
        Show.
        pose proof (tsize_pos qq).
        Show.
        lia. }
      Show.
      assert (HxsP : pstep (phi_erase xs0) xs').
      { Show.
        rewrite Hexs.
        Show.
        exact H8. }
      Show.
      destruct (IH xs0 HxsSize _ HxsP)
        as [xs1' [Hxs1' Hexs1']].
      Show.
      assert (HbIn : In (c0, b0) bs).
      { Show.
        eapply nth_error_In.
        Show.
        exact Hnth. }
      Show.
      assert (Hb0size : tsize b0 < tsize (TCase (TIn (TPair a0 xs0)) qq bs)).
      { Show.
        eapply tsize_case_bs_body.
        Show.
        exact HbIn. }
      Show.
      assert (HbP : pstep (phi_erase b0) b').
      { Show.
        rewrite Heb.
        Show.
        exact H9. }
      Show.
      destruct (IH b0 Hb0size _ HbP)
        as [b1' [Hb1' Heb1']].
      Show.
      exists (subst xs1' 0 b1').
      Show.
      split.
      Show.
      { eapply ps_case_red.
        Show.
        - exact Hnth.
          Show.
        - exact Hcpos.
          Show.
        - exact Hapos.
          Show.
        - exact Hpref.
          Show.
        - exact Hxs1'.
          Show.
        - exact Hb1'.
          Show. }
      { Show.
        rewrite phi_erase_subst.
        Show.
        rewrite Hexs1', Heb1'.
        Show.
        reflexivity. }
Qed.

Print Assumptions phi_erase_pstep_reflect_parent.
