(* Fundamental lemma: base types, enumerations and description codes. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelFundCore.
Import ListNotations.

Ltac inst_consts := repeat first
  [ rewrite (inst_const _ TUnitT) in * by reflexivity
  | rewrite (inst_const _ TUnit) in * by reflexivity
  | rewrite (inst_const _ TUId) in * by reflexivity
  | rewrite (inst_const _ TEnumU) in * by reflexivity
  | rewrite (inst_const _ TNilE) in * by reflexivity
  | rewrite (inst_const _ TEZero) in * by reflexivity
  | rewrite (inst_const _ TI1) in * by reflexivity
  | rewrite (inst_const _ TIBot) in * by reflexivity
  | match goal with |- context [instantiate ?g (TTag ?s)] => rewrite (inst_const g (TTag s)) in * by reflexivity end
  | rewrite instantiate_sort in * ].

Lemma fund_unitT : forall Gamma k, FP Gamma TUnitT (TSort k).
Proof. intros Gamma k g1 g2 _; inst_consts; apply rel_at_sort, sem_unitT. Qed.
Lemma fund_unit : forall Gamma, FP Gamma TUnit TUnitT.
Proof. intros Gamma g1 g2 _; inst_consts; apply sem_unit. Qed.
Lemma fund_uid : forall Gamma, FP Gamma TUId (TSort 0).
Proof. intros Gamma g1 g2 _; inst_consts; apply rel_at_sort, sem_uid. Qed.
Lemma fund_tag : forall Gamma s, FP Gamma (TTag s) TUId.
Proof. intros Gamma s g1 g2 _; inst_consts; apply sem_tag. Qed.
Lemma fund_enumu : forall Gamma, FP Gamma TEnumU (TSort 0).
Proof. intros Gamma g1 g2 _; inst_consts; apply rel_at_sort, sem_enumu. Qed.
Lemma fund_nile : forall Gamma, FP Gamma TNilE TEnumU.
Proof. intros Gamma g1 g2 _; inst_consts; apply sem_nile. Qed.

Lemma fund_conse : forall Gamma tag E, FP Gamma tag TUId -> FP Gamma E TEnumU ->
  FP Gamma (TConsE tag E) TEnumU.
Proof.
  intros Gamma tag E It IE g1 g2 Hc; pose proof (It _ _ Hc) as Ht; pose proof (IE _ _ Hc) as HE.
  inst_consts; rewrite !inst_conse in *. apply sem_conse; assumption.
Qed.
Lemma fund_enumt : forall Gamma E, FP Gamma E TEnumU -> FP Gamma (TEnumT E) (TSort 0).
Proof.
  intros Gamma E IE g1 g2 Hc; pose proof (IE _ _ Hc) as HE; inst_consts.
  rewrite !inst_enumt. apply rel_at_sort, sem_enumt, HE.
Qed.
Lemma fund_zero : forall Gamma tag E, FP Gamma tag TUId -> FP Gamma E TEnumU ->
  FP Gamma TEZero (TEnumT (TConsE tag E)).
Proof.
  intros Gamma tag E It IE g1 g2 Hc; pose proof (It _ _ Hc) as Ht; pose proof (IE _ _ Hc) as HE.
  inst_consts; rewrite !inst_enumt, !inst_conse. apply sem_zero; assumption.
Qed.
Lemma fund_succ : forall Gamma tag E n, FP Gamma tag TUId -> FP Gamma E TEnumU ->
  FP Gamma n (TEnumT E) -> FP Gamma (TESucc n) (TEnumT (TConsE tag E)).
Proof.
  intros Gamma tag E n It IE In g1 g2 Hc.
  pose proof (It _ _ Hc) as Ht; pose proof (IE _ _ Hc) as HE; pose proof (In _ _ Hc) as Hn.
  inst_consts; rewrite !inst_enumt, !inst_conse, !inst_succ in *. apply sem_succ; assumption.
Qed.

(* Function-typed premises with derived arrow types. *)
Lemma FP_arrow : forall Gamma f A B g1 g2, FP Gamma f (arrow A B) -> closing2 Gamma g1 g2 ->
  scoped Gamma A -> scoped Gamma B ->
  rel_at (instantiate g1 f) (instantiate g2 f)
    (arrow (instantiate g1 A) (instantiate g1 B)) (arrow (instantiate g2 A) (instantiate g2 B)).
Proof.
  intros Gamma f A B g1 g2 If Hc HA HB. envs Hc.
  destruct (inst_closed _ _ _ _ Hc HA) as [HA1 HA2]; destruct (inst_closed _ _ _ _ Hc HB) as [HB1 HB2].
  eapply rel_at_conv; [exact (If _ _ Hc)|apply cv_refl|apply cv_refl| |]; apply inst_arrow; assumption.
Qed.

Lemma scoped_of_typing : forall Gamma t A, typing Gamma t A -> scoped Gamma t.
Proof. exact typing_scoped. Qed.
Lemma scoped_sort : forall Gamma k, scoped Gamma (TSort k).
Proof. intros Gamma k x H; cbn in H; contradiction. Qed.
Lemma scoped_idesc : forall Gamma IT, scoped Gamma IT -> scoped Gamma (TIDesc IT).
Proof. intros Gamma IT H x Hx; apply H, Hx. Qed.
Lemma scoped_enumt : forall Gamma E, scoped Gamma E -> scoped Gamma (TEnumT E).
Proof. intros Gamma E H x Hx; apply H, Hx. Qed.

Lemma fund_epi : forall Gamma k E P, typing Gamma E TEnumU -> FP Gamma E TEnumU ->
  typing Gamma P (arrow (TEnumT E) (TSort k)) -> FP Gamma P (arrow (TEnumT E) (TSort k)) ->
  FP Gamma (TEPi k E P) (TSort k).
Proof.
  intros Gamma k E P HE IE HP IP g1 g2 Hc.
  pose proof (IE _ _ Hc) as HE'; inst_consts; destruct (rel_at_code _ _ HE') as [L [HL1 HL2]].
  pose proof (FP_arrow _ _ _ _ _ _ IP Hc (scoped_enumt _ _ (typing_scoped _ _ _ HE)) (scoped_sort _ _)) as HP'.
  rewrite ?inst_enumt, ?instantiate_sort in HP'.
  rewrite !inst_epi, ?instantiate_sort. apply rel_at_sort.
  eapply sem_epi; [exact HL1|exact HL2|]. intros m Hm.
  apply rel_at_sort. eapply sem_arrow_app; [exact HP'|apply (sem_position _ _ L); assumption
    |apply closed_position|apply closed_position].
Qed.

Lemma fund_switch : forall Gamma k E P p e, typing Gamma E TEnumU -> FP Gamma E TEnumU ->
  typing Gamma P (arrow (TEnumT E) (TSort k)) -> FP Gamma p (TEPi k E P) -> FP Gamma e (TEnumT E) ->
  FP Gamma (TSwitch k E P p e) (TApp P e).
Proof.
  intros Gamma k E P p e HE IE HP Ip Ie g1 g2 Hc.
  pose proof (IE _ _ Hc) as HE'; inst_consts; destruct (rel_at_code _ _ HE') as [L [HL1 HL2]].
  destruct (inst_closed_typed _ _ _ _ _ Hc HP) as [HP1 HP2].
  pose proof (Ip _ _ Hc) as Hp; pose proof (Ie _ _ Hc) as He.
  rewrite !inst_epi in Hp; rewrite !inst_enumt in He.
  rewrite !inst_switch, !instantiate_app. eapply sem_switch; eassumption.
Qed.

(* Description codes *)
Lemma fund_small : forall Gamma IT g1 g2, FP Gamma IT (TSort 0) -> closing2 Gamma g1 g2 ->
  exists RI, S2 (instantiate g1 IT) (instantiate g2 IT) RI.
Proof.
  intros Gamma IT g1 g2 I Hc; pose proof (I _ _ Hc) as H; rewrite ?instantiate_sort in H.
  apply small_of_rel, H.
Qed.

Lemma fund_idesc : forall Gamma IT, FP Gamma IT (TSort 0) -> FP Gamma (TIDesc IT) (TSort 1).
Proof.
  intros Gamma IT I g1 g2 Hc; pose proof (I _ _ Hc) as H; rewrite ?instantiate_sort in *.
  rewrite !inst_idesc. apply rel_at_sort, sem_idesc, H.
Qed.
Lemma fund_ivar : forall Gamma IT i, FP Gamma IT (TSort 0) -> typing Gamma i IT -> FP Gamma i IT ->
  FP Gamma (TIVar i) (TIDesc IT).
Proof.
  intros Gamma IT i IIT Hi Ii g1 g2 Hc; destruct (fund_small _ _ _ _ IIT Hc) as [RI HI].
  destruct (inst_closed_typed _ _ _ _ _ Hc Hi) as [H1 H2].
  rewrite !inst_ivar, !inst_idesc. eapply sem_ivar; [exact HI|exact (Ii _ _ Hc)|exact H1|exact H2].
Qed.
Lemma fund_i1 : forall Gamma IT, FP Gamma IT (TSort 0) -> FP Gamma TI1 (TIDesc IT).
Proof.
  intros Gamma IT I g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  inst_consts; rewrite !inst_idesc; eapply sem_i1; exact HI.
Qed.
Lemma fund_ibot : forall Gamma IT, FP Gamma IT (TSort 0) -> FP Gamma TIBot (TIDesc IT).
Proof.
  intros Gamma IT I g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  inst_consts; rewrite !inst_idesc; eapply sem_ibot; exact HI.
Qed.
Lemma fund_iprod : forall Gamma IT A B, FP Gamma IT (TSort 0) ->
  typing Gamma A (TIDesc IT) -> FP Gamma A (TIDesc IT) ->
  typing Gamma B (TIDesc IT) -> FP Gamma B (TIDesc IT) -> FP Gamma (TIProd A B) (TIDesc IT).
Proof.
  intros Gamma IT A B I HA IA HB IB g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  destruct (inst_closed_typed _ _ _ _ _ Hc HA) as [HA1 HA2].
  destruct (inst_closed_typed _ _ _ _ _ Hc HB) as [HB1 HB2].
  pose proof (IA _ _ Hc) as HA'; pose proof (IB _ _ Hc) as HB'.
  rewrite !inst_idesc in *; rewrite !inst_iprod. eapply sem_iprod; eassumption.
Qed.
Lemma fund_ipi : forall Gamma IT A D, FP Gamma IT (TSort 0) ->
  typing Gamma A (TSort 0) -> FP Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> FP Gamma D (arrow A (TIDesc IT)) ->
  typing Gamma IT (TSort 0) -> FP Gamma (TIPi A D) (TIDesc IT).
Proof.
  intros Gamma IT A D I HA IA HD ID HIT g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  destruct (inst_closed_typed _ _ _ _ _ Hc HA) as [HA1 HA2].
  destruct (inst_closed_typed _ _ _ _ _ Hc HD) as [HD1 HD2].
  pose proof (IA _ _ Hc) as HA'; rewrite ?instantiate_sort in HA'.
  pose proof (FP_arrow _ _ _ _ _ _ ID Hc (typing_scoped _ _ _ HA)
    (scoped_idesc _ _ (typing_scoped _ _ _ HIT))) as HD'.
  rewrite !inst_idesc in *; rewrite !inst_ipi. eapply sem_ipi; eassumption.
Qed.
Lemma fund_isig : forall Gamma IT A D, FP Gamma IT (TSort 0) ->
  typing Gamma A (TSort 0) -> FP Gamma A (TSort 0) ->
  typing Gamma D (arrow A (TIDesc IT)) -> FP Gamma D (arrow A (TIDesc IT)) ->
  typing Gamma IT (TSort 0) -> FP Gamma (TISig A D) (TIDesc IT).
Proof.
  intros Gamma IT A D I HA IA HD ID HIT g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  destruct (inst_closed_typed _ _ _ _ _ Hc HA) as [HA1 HA2].
  destruct (inst_closed_typed _ _ _ _ _ Hc HD) as [HD1 HD2].
  pose proof (IA _ _ Hc) as HA'; rewrite ?instantiate_sort in HA'.
  pose proof (FP_arrow _ _ _ _ _ _ ID Hc (typing_scoped _ _ _ HA)
    (scoped_idesc _ _ (typing_scoped _ _ _ HIT))) as HD'.
  rewrite !inst_idesc in *; rewrite !inst_isig. eapply sem_isig; eassumption.
Qed.
Lemma fund_ichoice : forall Gamma IT E D, FP Gamma IT (TSort 0) ->
  typing Gamma E TEnumU -> FP Gamma E TEnumU ->
  typing Gamma D (arrow (TEnumT E) (TIDesc IT)) -> FP Gamma D (arrow (TEnumT E) (TIDesc IT)) ->
  typing Gamma IT (TSort 0) -> FP Gamma (TIChoice E D) (TIDesc IT).
Proof.
  intros Gamma IT E D I HE IE HD ID HIT g1 g2 Hc; destruct (fund_small _ _ _ _ I Hc) as [RI HI].
  destruct (inst_closed_typed _ _ _ _ _ Hc HD) as [HD1 HD2].
  pose proof (IE _ _ Hc) as HE'; inst_consts.
  pose proof (FP_arrow _ _ _ _ _ _ ID Hc (scoped_enumt _ _ (typing_scoped _ _ _ HE))
    (scoped_idesc _ _ (typing_scoped _ _ _ HIT))) as HD'.
  rewrite !inst_idesc, !inst_enumt in *; rewrite !inst_ichoice. eapply sem_ichoice; eassumption.
Qed.
