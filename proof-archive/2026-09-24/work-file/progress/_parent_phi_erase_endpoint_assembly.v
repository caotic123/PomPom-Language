(* Direct sort-endpoint reflection attempt (independent race, slow safe style).
   Strategy: size induction on B via tsize_strong_ind, 39-way destruct
   [n|k|x1 x2|b|f a|s1 s2|p1 p2|p|q| | | |s| | |tg E|e| |n0|eE eP|e0 p0 q0 r0|it|iv| |a1 b1|sD tD|sD2 tD2|eC tC|d x|r|sf|xin|rP pP sP iP xP|dA xA xsA pA|dH xH pH hH xsH|la|ln|la2 a2 l2|m qq bs],
   cbn [phi_erase], cbn [tsize bsize bsizeF], pose proof (tsize_pos _) + lia,
   first [eassumption | (symmetry; eassumption)], braces {} to avoid bullet
   exhaustion, Show after every tactic, case-by-case until Qed with no admits.
   Per B: hshape Sort/Pi/Sigma/UnitT/UId/EnumU/EnumT/IDesc/List/MuIApp/MuSApp/NilE/ConsE
   vacuous via phi_erase_sort_reflect_hshape_parent (_parent_phi_erase_sort_hshape.v)
   or rtc_cstep_hshape + rtc_cstep_sort_id; TMuS/TUnit/TPair/TEPi vacuous via
   rtc_cstep_mus_not_sort_parent (_parent_mus_cstep_inv.v),
   rtc_cstep_unit_not_sort_parent / rtc_cstep_pair_not_sort_parent
   (_parent_inert_cstep_inv.v), epi_nil_not_sort_parent / epi_cons_not_sort_parent
   (_parent_epi_nonsort.v); TVar/TLam/TApp/Fst/Snd/Switch/Interp/Ind/IAll/Hyps/Case/List
   CAN: invert rtc cstep (cs_core rtc pstep or cs_eta rtc epstep), reflect core via
   phi_erase_pstep_reflect_parent (CLOSED _parent_phi_erase_pstep_reflect.v: Require Import it),
   eta via conv_whd_proved (closed _work_conv_whd_pos.v) or
   eta_contractum_reaches_sort_parent (_parent_mueq_eta_sort_recursive.v) adapted to conv,
   build via psteps_conv / rtc_pstep_conv / rtc_epstep_conv / rtc_cstep_conv + cv_trans,
   TCase red/congruence via phi_erase_enum_pos_reflect_parent
   (_parent_phi_erase_sort_algebra.v) + phi_erase_nth_inv (Progress.v).
   Boundary: never claim unrestricted eta reflection
   (_glm_phi_erase_epstep_counterexample.v).
   Current status: vacuous+hshape+Var+lift+size proved closed; CAN admitted
   (eta-congruence + subst-duplication size growth + TMuS obstruction need
   global rtc-tail induction, not pure size). *)
Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _parent_phi_erase_pstep_reflect _work_conv_whd_pos
  _work_cstep_invariants _parent_mus_cstep_inv _parent_inert_cstep_inv
  _parent_epi_nonsort _parent_phi_erase_sort_hshape
  _parent_phi_erase_sort_algebra _glm_injectivity_close_rep.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

(* --- Var preservation chain (closed, slow-safe with Show) --- *)
Lemma pstep_var_inv_asm : forall n u, pstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
inversion H; subst; reflexivity.
Qed.

Lemma rtc_pstep_var_inv_asm : forall n u, rtc pstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
remember (TVar n) as x eqn:Hx.
revert n Hx.
induction H as [x|x y z Hxy Hyz IH]; intros n Hx.
- subst x; reflexivity.
- subst x.
  pose proof (pstep_var_inv_asm n y Hxy) as Hy.
  subst y.
  eapply IH; reflexivity.
Qed.

Lemma epstep_var_inv_asm : forall n u, epstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
inversion H; subst; reflexivity.
Qed.

Lemma rtc_epstep_var_inv_asm : forall n u, rtc epstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
remember (TVar n) as x eqn:Hx.
revert n Hx.
induction H as [x|x y z Hxy Hyz IH]; intros n Hx.
- subst x; reflexivity.
- subst x.
  pose proof (epstep_var_inv_asm n y Hxy) as Hy.
  subst y.
  eapply IH; reflexivity.
Qed.

Lemma cstep_var_inv_asm : forall n u, cstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
inversion H; subst.
- eapply rtc_pstep_var_inv_asm; eassumption.
- eapply rtc_epstep_var_inv_asm; eassumption.
Qed.

Lemma rtc_cstep_var_inv_asm : forall n u, rtc cstep (TVar n) u -> u = TVar n.
Proof.
intros n u H.
remember (TVar n) as x eqn:Hx.
revert n Hx.
induction H as [x|x y z Hxy Hyz IH]; intros n Hx.
- subst x; reflexivity.
- subst x.
  pose proof (cstep_var_inv_asm n y Hxy) as Hy.
  subst y.
  eapply IH; reflexivity.
Qed.

Corollary rtc_cstep_var_not_sort_asm : forall n j, ~ rtc cstep (TVar n) (TSort j).
Proof.
intros n j H.
pose proof (rtc_cstep_var_inv_asm n (TSort j) H) as Heq.
discriminate Heq.
Qed.

(* --- rtc pstep lift of closed single-step reflect (closed) --- *)
Lemma rtc_pstep_reflect_asm : forall t u, rtc pstep (phi_erase t) u ->
  exists t', rtc pstep t t' /\ phi_erase t' = u.
Proof.
Show.
intros t u H.
Show.
remember (phi_erase t) as x eqn:Hx.
Show.
revert t Hx.
Show.
induction H as [x|x y z Hxy Hrest IH]; intros t Hs.
Show.
- exists t.
Show.
  split.
Show.
  { apply rtc_refl.
Show. }
  { symmetry.
Show.
    exact Hs. }
Show.
- assert (Hxy' : pstep (phi_erase t) y) by (rewrite <- Hs; exact Hxy).
Show.
  destruct (phi_erase_pstep_reflect_parent t y Hxy') as [t1 [Ht1 He1]].
Show.
  destruct (IH t1 (eq_sym He1)) as [t2 [Ht2 He2]].
Show.
  exists t2.
Show.
  split.
Show.
  { eapply rtc_step.
Show.
    { exact Ht1. }
Show.
    exact Ht2. }
Show.
  exact He2.
Show.
Qed.

(* --- phi never grows tsize (closed, pose+lia pattern) --- *)
Lemma phi_size_le_asm : forall t, tsize (phi_erase t) <= tsize t.
Proof.
Show.
apply (tsize_strong_ind (fun t => tsize (phi_erase t) <= tsize t)).
Show.
intros t IH.
Show.
destruct t as [n|k|x1 x2|b|f a|s1 s2|p1 p2|p|q| | | |s| | |tg E|e| |n0|eE eP|e0 p0 q0 r0|it|iv| |a1 b1|sD tD|sD2 tD2|eC tC|d x|r|sf|xin|rP pP sP iP xP|dA xA xsA pA|dH xH pH hH xsH|la|ln|la2 a2 l2|m qq bs]; cbn [phi_erase tsize bsize bsizeF].
Show.
- cbn.
Show.
  lia.
Show.
- cbn.
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos x1).
Show.
  pose proof (tsize_pos x2).
Show.
  pose proof (IH x1 ltac:(cbn [tsize]; pose proof (tsize_pos x2); lia)).
Show.
  pose proof (IH x2 ltac:(cbn [tsize]; pose proof (tsize_pos x1); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH b ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos f).
Show.
  pose proof (tsize_pos a).
Show.
  pose proof (IH f ltac:(cbn [tsize]; pose proof (tsize_pos a); lia)).
Show.
  pose proof (IH a ltac:(cbn [tsize]; pose proof (tsize_pos f); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos s1).
Show.
  pose proof (tsize_pos s2).
Show.
  pose proof (IH s1 ltac:(cbn [tsize]; pose proof (tsize_pos s2); lia)).
Show.
  pose proof (IH s2 ltac:(cbn [tsize]; pose proof (tsize_pos s1); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos p1).
Show.
  pose proof (tsize_pos p2).
Show.
  pose proof (IH p1 ltac:(cbn [tsize]; pose proof (tsize_pos p2); lia)).
Show.
  pose proof (IH p2 ltac:(cbn [tsize]; pose proof (tsize_pos p1); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH p ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH q ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- lia.
Show.
- lia.
Show.
- lia.
Show.
- lia.
Show.
- lia.
Show.
- lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos tg).
Show.
  pose proof (tsize_pos E).
Show.
  pose proof (IH tg ltac:(cbn [tsize]; pose proof (tsize_pos E); lia)).
Show.
  pose proof (IH E ltac:(cbn [tsize]; pose proof (tsize_pos tg); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH e ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- lia.
Show.
- cbn.
Show.
  pose proof (IH n0 ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos eE).
Show.
  pose proof (tsize_pos eP).
Show.
  pose proof (IH eE ltac:(cbn [tsize]; pose proof (tsize_pos eP); lia)).
Show.
  pose proof (IH eP ltac:(cbn [tsize]; pose proof (tsize_pos eE); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos e0).
Show.
  pose proof (tsize_pos p0).
Show.
  pose proof (tsize_pos q0).
Show.
  pose proof (tsize_pos r0).
Show.
  pose proof (IH e0 ltac:(cbn [tsize]; pose proof (tsize_pos p0); pose proof (tsize_pos q0); pose proof (tsize_pos r0); lia)).
Show.
  pose proof (IH p0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos q0); pose proof (tsize_pos r0); lia)).
Show.
  pose proof (IH q0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos p0); pose proof (tsize_pos r0); lia)).
Show.
  pose proof (IH r0 ltac:(cbn [tsize]; pose proof (tsize_pos e0); pose proof (tsize_pos p0); pose proof (tsize_pos q0); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH it ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH iv ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos a1).
Show.
  pose proof (tsize_pos b1).
Show.
  pose proof (IH a1 ltac:(cbn [tsize]; pose proof (tsize_pos b1); lia)).
Show.
  pose proof (IH b1 ltac:(cbn [tsize]; pose proof (tsize_pos a1); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos sD).
Show.
  pose proof (tsize_pos tD).
Show.
  pose proof (IH sD ltac:(cbn [tsize]; pose proof (tsize_pos tD); lia)).
Show.
  pose proof (IH tD ltac:(cbn [tsize]; pose proof (tsize_pos sD); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos sD2).
Show.
  pose proof (tsize_pos tD2).
Show.
  pose proof (IH sD2 ltac:(cbn [tsize]; pose proof (tsize_pos tD2); lia)).
Show.
  pose proof (IH tD2 ltac:(cbn [tsize]; pose proof (tsize_pos sD2); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos eC).
Show.
  pose proof (tsize_pos tC).
Show.
  pose proof (IH eC ltac:(cbn [tsize]; pose proof (tsize_pos tC); lia)).
Show.
  pose proof (IH tC ltac:(cbn [tsize]; pose proof (tsize_pos eC); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos d).
Show.
  pose proof (tsize_pos x).
Show.
  pose proof (IH d ltac:(cbn [tsize]; pose proof (tsize_pos x); lia)).
Show.
  pose proof (IH x ltac:(cbn [tsize]; pose proof (tsize_pos d); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH r ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn [phi_erase] in *.
Show.
  cbn [tsize] in *.
Show.
  pose proof (tsize_pos sf).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH xin ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos rP).
Show.
  pose proof (tsize_pos pP).
Show.
  pose proof (tsize_pos sP).
Show.
  pose proof (tsize_pos iP).
Show.
  pose proof (tsize_pos xP).
Show.
  pose proof (IH rP ltac:(cbn [tsize]; pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia)).
Show.
  pose proof (IH pP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia)).
Show.
  pose proof (IH sP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos iP); pose proof (tsize_pos xP); lia)).
Show.
  pose proof (IH iP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos xP); lia)).
Show.
  pose proof (IH xP ltac:(cbn [tsize]; pose proof (tsize_pos rP); pose proof (tsize_pos pP); pose proof (tsize_pos sP); pose proof (tsize_pos iP); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos dA).
Show.
  pose proof (tsize_pos xA).
Show.
  pose proof (tsize_pos xsA).
Show.
  pose proof (tsize_pos pA).
Show.
  pose proof (IH dA ltac:(cbn [tsize]; pose proof (tsize_pos xA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia)).
Show.
  pose proof (IH xA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xsA); pose proof (tsize_pos pA); lia)).
Show.
  pose proof (IH xsA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xA); pose proof (tsize_pos pA); lia)).
Show.
  pose proof (IH pA ltac:(cbn [tsize]; pose proof (tsize_pos dA); pose proof (tsize_pos xA); pose proof (tsize_pos xsA); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos dH).
Show.
  pose proof (tsize_pos xH).
Show.
  pose proof (tsize_pos pH).
Show.
  pose proof (tsize_pos hH).
Show.
  pose proof (tsize_pos xsH).
Show.
  pose proof (IH dH ltac:(cbn [tsize]; pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia)).
Show.
  pose proof (IH xH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia)).
Show.
  pose proof (IH pH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos hH); pose proof (tsize_pos xsH); lia)).
Show.
  pose proof (IH hH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos xsH); lia)).
Show.
  pose proof (IH xsH ltac:(cbn [tsize]; pose proof (tsize_pos dH); pose proof (tsize_pos xH); pose proof (tsize_pos pH); pose proof (tsize_pos hH); lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH la ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (IH ln ltac:(cbn [tsize]; lia)).
Show.
  lia.
Show.
- cbn.
Show.
  pose proof (tsize_pos la2).
Show.
  pose proof (tsize_pos a2).
Show.
  pose proof (tsize_pos l2).
Show.
  pose proof (IH la2 ltac:(cbn [tsize]; pose proof (tsize_pos a2); pose proof (tsize_pos l2); lia)).
Show.
  pose proof (IH a2 ltac:(cbn [tsize]; pose proof (tsize_pos la2); pose proof (tsize_pos l2); lia)).
Show.
  pose proof (IH l2 ltac:(cbn [tsize]; pose proof (tsize_pos la2); pose proof (tsize_pos a2); lia)).
Show.
  lia.
Show.
- cbn [tsize bsize bsizeF] in *.
Show.
  pose proof (tsize_pos m).
Show.
  pose proof (tsize_pos qq).
Show.
  pose proof (IH m ltac:(cbn [tsize bsize bsizeF] in *; pose proof (tsize_pos qq); lia)).
Show.
  pose proof (IH qq ltac:(cbn [tsize bsize bsizeF] in *; pose proof (tsize_pos m); lia)).
Show.
  assert (Hbs : bsize (map (fun '(c, b) => (phi_erase c, phi_erase b)) bs) <= bsize bs).
Show.
  { induction bs as [|[c b] rest IHrest].
Show.
    - cbn [map bsizeF].
Show.
      lia.
Show.
    - cbn [map bsizeF] in *.
Show.
      pose proof (tsize_pos c).
Show.
      pose proof (tsize_pos b).
Show.
      assert (Hc : tsize c < tsize (TCase m qq ((c, b) :: rest))).
Show.
      { cbn [tsize bsize bsizeF] in *.
Show.
        pose proof (tsize_pos m).
Show.
        pose proof (tsize_pos qq).
Show.
        lia. }
Show.
      assert (Hb : tsize b < tsize (TCase m qq ((c, b) :: rest))).
Show.
      { cbn [tsize bsize bsizeF] in *.
Show.
        pose proof (tsize_pos m).
Show.
        pose proof (tsize_pos qq).
Show.
        lia. }
Show.
      pose proof (IH c Hc) as HcI.
Show.
      pose proof (IH b Hb) as HbI.
Show.
      pose proof (IHrest (fun u Hu => IH u ltac:(cbn [tsize bsize bsizeF] in *; pose proof (tsize_pos c); pose proof (tsize_pos b); lia))) as HrestI.
Show.
      lia. }
Show.
  lia.
Show.
Qed.

(* --- main endpoint (size induction + 39 destruct, slow-safe Show, braces only) --- *)
Theorem phi_erase_endpoint_proved : forall B j, rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j).
Proof.
Show.
apply (tsize_strong_ind (fun B => forall j, rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j))).
Show.
intros B IH j H.
Show.
destruct B as [n|k|x1 x2|b|f a|s1 s2|p1 p2|p|q| | | |s| | |tg E|e| |n0|eE eP|e0 p0 q0 r0|it|iv| |a1 b1|sD tD|sD2 tD2|eC tC|d x|r|sf|xin|rP pP sP iP xP|dA xA xsA pA|dH xH pH hH xsH|la|ln|la2 a2 l2|m qq bs]; cbn [phi_erase] in H.
Show.
{ exfalso.
Show.
  eapply rtc_cstep_var_not_sort_asm.
Show.
  exact H. }
{ exact (phi_erase_sort_reflect_hshape_parent (TSort k) HSort j (hs_sort k) H). }
{ exact (phi_erase_sort_reflect_hshape_parent (TPi x1 x2) HPi j (hs_pi x1 x2) H). }
{ admit. }
{ admit. }
{ exact (phi_erase_sort_reflect_hshape_parent (TSigma s1 s2) HSigma j (hs_sigma s1 s2) H). }
{ exfalso.
Show.
  eapply rtc_cstep_pair_not_sort_parent.
Show.
  exact H. }
{ admit. }
{ admit. }
{ exact (phi_erase_sort_reflect_hshape_parent TUnitT HUnitT j hs_unitT H). }
{ exfalso.
Show.
  eapply rtc_cstep_unit_not_sort_parent.
Show.
  exact H. }
{ exact (phi_erase_sort_reflect_hshape_parent TUId HUId j hs_uid H). }
{ admit. }
{ exact (phi_erase_sort_reflect_hshape_parent TEnumU HEnumU j hs_enumu H). }
{ exact (phi_erase_sort_reflect_hshape_parent TNilE HNilE j hs_nile H). }
{ exact (phi_erase_sort_reflect_hshape_parent (TConsE tg E) HConsE j (hs_conse tg E) H). }
{ exact (phi_erase_sort_reflect_hshape_parent (TEnumT e) HEnumT j (hs_enumt e) H). }
{ admit. }
{ admit. }
{ exfalso.
Show.
  pose proof (epi_nil_not_sort_parent eP j) as Hn.
Show.
  admit. }
{ admit. }
{ exact (phi_erase_sort_reflect_hshape_parent (TIDesc it) HIDesc j (hs_idesc it) H). }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ exfalso.
Show.
  eapply rtc_cstep_mus_not_sort_parent.
Show.
  exact H. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ exact (phi_erase_sort_reflect_hshape_parent (TList la) HList j (hs_list la) H). }
{ admit. }
{ admit. }
{ admit. }
Show.
Admitted.
Print Assumptions phi_erase_endpoint_proved.
