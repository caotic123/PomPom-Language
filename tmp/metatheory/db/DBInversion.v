Require Export ProofDB.DBParallelBase.
Lemma invert_TLam : forall x0 u, pstep (TLam x0) u -> exists y0, u = (TLam y0) /\ pstep x0 y0.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 1 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TPair : forall x0 x1 u, pstep (TPair x0 x1) u -> exists y0 y1, u = (TPair y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TNilE : forall u, pstep TNilE u -> u = TNilE.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TConsE : forall x0 x1 u, pstep (TConsE x0 x1) u -> exists y0 y1, u = (TConsE y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TEZero : forall u, pstep TEZero u -> u = TEZero.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TESucc : forall x0 u, pstep (TESucc x0) u -> exists y0, u = (TESucc y0) /\ pstep x0 y0.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 1 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TUnit : forall u, pstep TUnit u -> u = TUnit.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIVar : forall x0 u, pstep (TIVar x0) u -> exists y0, u = (TIVar y0) /\ pstep x0 y0.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 1 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TI1 : forall u, pstep TI1 u -> u = TI1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIBot : forall u, pstep TIBot u -> u = TIBot.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIProd : forall x0 x1 u, pstep (TIProd x0 x1) u -> exists y0 y1, u = (TIProd y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIPi : forall x0 x1 u, pstep (TIPi x0 x1) u -> exists y0 y1, u = (TIPi y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TISig : forall x0 x1 u, pstep (TISig x0 x1) u -> exists y0 y1, u = (TISig y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIChoice : forall x0 x1 u, pstep (TIChoice x0 x1) u -> exists y0 y1, u = (TIChoice y0 y1) /\ pstep x0 y0 /\ pstep x1 y1.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 2 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma invert_TIn : forall x0 u, pstep (TIn x0) u -> exists y0, u = (TIn y0) /\ pstep x0 y0.
Proof. intros; match goal with H : pstep _ _ |- _ => inversion H; subst end; do 1 eexists; repeat split; try reflexivity; eassumption. Qed.
Ltac fast_inv := match goal with
| H : pstep (TLam ?x0) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TLam x0 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TPair ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TPair x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep TNilE ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TNilE u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TConsE ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TConsE x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep TEZero ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TEZero u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TESucc ?x0) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TESucc x0 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep TUnit ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TUnit u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TIVar ?x0) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIVar x0 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep TI1 ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TI1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep TIBot ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIBot u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TIProd ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIProd x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TIPi ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIPi x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TISig ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TISig x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TIChoice ?x0 ?x1) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIChoice x0 x1 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
| H : pstep (TIn ?x0) ?u |- _ =>
  let E := fresh "E" in pose proof (invert_TIn x0 u H) as E; clear H;
  repeat match type of E with exists _, _ => let v := fresh "v" in destruct E as [v E] end;
  repeat match type of E with _ /\ _ => let Eq := fresh "Eq" in destruct E as [Eq E]; try (is_var u; subst u); try match type of Eq with _ = _ => inversion Eq; subst; clear Eq end end; try (is_var u; subst u)
end.
