(* Confluence of annotated reduction modulo annotations.

   Annotated reduction is not confluent on the nose (ACriticalPair.v).
   Two reducts of a typed term nevertheless reach normal forms with the
   same erasure: typed normal forms erase to raw normal forms
   (ACfNormal.typed_normal_erasure), and raw reduction is confluent.
   The results are stated over strong normalization of typed terms, which
   ANormalization.annotated_normalization discharges. *)
From Stdlib Require Import List Arith.
Require Export annotated.ACfNormal.
Import ListNotations.

Lemma raw_reduces_rtc : forall r s, RCore.reduces r s -> RB.rtc RCore.reduction r s.
Proof. intros r s H; induction H; [constructor|econstructor; eassumption]. Qed.

Lemma reduces_trans : forall t u v, reduces t u -> reduces u v -> reduces t v.
Proof. intros t u v H; induction H; eauto using reduces. Qed.

Definition strongly_normalizing t := Acc (fun u v => reduction v u) t.

Lemma normal_form_exists : forall t, strongly_normalizing t ->
  exists n, reduces t n /\ anormal n.
Proof.
  intros t H; induction H as [t _ IH].
  destruct (reduction_decidable t) as [[u Hu]|Hn].
  - destruct (IH u Hu) as [n [Hr Hn]]; exists n; split; [econstructor; eassumption|exact Hn].
  - exists t; split; [constructor|exact Hn].
Qed.

Lemma reduces_normal_erasure : forall Gamma t A n, typing Gamma t A ->
  reduces t n -> anormal n -> RB.rtc RCore.reduction (erase t) (erase n) /\ raw_normal (erase n).
Proof.
  intros Gamma t A n HT Hr Hn; split.
  - exact (raw_reduces_rtc _ _ (reduces_erasure _ _ Hr)).
  - exact (typed_normal_erasure _ _ _ (full_preservation_reduces _ _ _ _ HT Hr) Hn).
Qed.

(* Raw normal forms of convertible terms coincide. *)
Lemma raw_normal_conversion_eq : forall r s, raw_normal r -> raw_normal s ->
  RCore.conv r s -> r = s.
Proof.
  intros r s Hr Hs HC; destruct (RCf.conversion_joinable _ _ HC) as [w [Hrw Hsw]].
  rewrite (raw_normal_reductions _ _ Hr Hrw) in Hsw.
  exact (raw_normal_reductions _ _ Hs Hsw).
Qed.

Section ModuloAnnotations.
Hypothesis typed_SN : forall Gamma t A, typing Gamma t A -> strongly_normalizing t.

(* Every typed term has a normal form, and all of its normal forms have the
   same erasure. *)
Theorem normal_forms_unique_modulo_annotations : forall Gamma t A n m,
  typing Gamma t A -> reduces t n -> anormal n -> reduces t m -> anormal m ->
  erase n = erase m.
Proof.
  intros Gamma t A n m HT Hn HNn Hm HNm.
  destruct (reduces_normal_erasure _ _ _ _ HT Hn HNn) as [Hrn Hnn].
  destruct (reduces_normal_erasure _ _ _ _ HT Hm HNm) as [Hrm Hnm].
  destruct (RCf.reduction_confluent _ _ _ Hrn Hrm) as [w [Hnw Hmw]].
  rewrite (raw_normal_reductions _ _ Hnn Hnw) in Hmw.
  exact (raw_normal_reductions _ _ Hnm Hmw).
Qed.

Theorem confluence_modulo_annotations : forall Gamma t A u v,
  typing Gamma t A -> reduces t u -> reduces t v ->
  exists w w', reduces u w /\ reduces v w' /\ erase w = erase w'.
Proof.
  intros Gamma t A u v HT Hu Hv.
  pose proof (full_preservation_reduces _ _ _ _ HT Hu) as HTu.
  pose proof (full_preservation_reduces _ _ _ _ HT Hv) as HTv.
  destruct (normal_form_exists _ (typed_SN _ _ _ HTu)) as [n [Hun Hn]].
  destruct (normal_form_exists _ (typed_SN _ _ _ HTv)) as [m [Hvm Hm]].
  exists n, m; split; [exact Hun|split; [exact Hvm|]].
  exact (normal_forms_unique_modulo_annotations _ _ _ _ _ HT
    (reduces_trans _ _ _ Hu Hun) Hn (reduces_trans _ _ _ Hv Hvm) Hm).
Qed.

(* Judgmental conversion is raw conversion of erasures. Convertible typed
   terms reduce to terms with equal erasure. *)
Theorem conversion_joinability_modulo_annotations : forall Gamma t u A B,
  typing Gamma t A -> typing Gamma u B -> RCore.conv (erase t) (erase u) ->
  exists w w', reduces t w /\ reduces u w' /\ erase w = erase w'.
Proof.
  intros Gamma t u A B Ht Hu HC.
  destruct (normal_form_exists _ (typed_SN _ _ _ Ht)) as [n [Htn Hn]].
  destruct (normal_form_exists _ (typed_SN _ _ _ Hu)) as [m [Hum Hm]].
  exists n, m; split; [exact Htn|split; [exact Hum|]].
  destruct (reduces_normal_erasure _ _ _ _ Ht Htn Hn) as [Hrn Hnn].
  destruct (reduces_normal_erasure _ _ _ _ Hu Hum Hm) as [Hrm Hnm].
  apply raw_normal_conversion_eq; [exact Hnn|exact Hnm|].
  eapply RCore.cv_trans; [apply RCore.cv_sym, nameless.DBWeakening.reductions_conversion; exact Hrn|].
  eapply RCore.cv_trans; [exact HC|].
  apply nameless.DBWeakening.reductions_conversion; exact Hrm.
Qed.
End ModuloAnnotations.

Print Assumptions confluence_modulo_annotations.
Print Assumptions conversion_joinability_modulo_annotations.
