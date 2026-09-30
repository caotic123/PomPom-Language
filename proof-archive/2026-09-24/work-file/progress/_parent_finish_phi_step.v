Require Import Progress SignatureLemmas
 _parent_finish_cjoin_context _parent_finish_against_step
 _luna_finish_mus_branch_transport _luna_finish_prune_mem_or
 _luna_finish_pruned_coverage _luna_finish_erased_coverage.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._work_cjoin Progress._work_cstep_invariants.

Lemma converted_branch_dead_payload_steps_parent : forall N S0 i0 S1 i1 c d xs X,
 bounded_progress_parent N ->tsize xs<=N ->
 check [] xs(TInterp(TApp(branches(TApp S0 i0))c)X) ->
 conv(TApp(TMuS S0)i0)(TApp(TMuS S1)i1) ->
 cjoin(phi_erase c)(phi_erase d) ->
 desc_against(TApp(branches(TApp S1 i1))d) ->
 exists xs',step xs xs'.
Proof.
 intros N S0 i0 S1 i1 c d xs X HP Hsz HC Hconv Hcd HD.
 eapply(desc_against_erased_step_parent N HP _ HD xs _ X Hsz HC).
 cbn[phi_erase]. apply cjoin_interp_parent;[|apply cjoin_refl].
 eapply cjoin_trans.
 - exact(mus_branch_transport_luna S0 S1 i0 i1 c Hconv).
 - apply cjoin_app_parent;[apply cjoin_refl|exact Hcd].
Qed.

Theorem direct_phi_spine_progress_parent : forall N S0 i0 S1 S2 i c n xs X
 Phi1 Phi2 Psi1 Psi2 bs,
 bounded_progress_parent N ->tsize xs<=N ->
 check [] xs(TInterp(TApp(branches(TApp S0 i0))c)X) ->
 conv(TApp(TMuS S0)i0)(TApp(TMuS S1)i) ->
 enum_pos c n ->Forall(fun d=>exists m,enum_pos d m)bs ->
 spine_mem c Phi1 ->spine_phi S1 i Phi1 Psi1 ->
 spine_phi S2 i Phi2 Psi2 ->conv Psi1 Psi2 ->covers bs Phi2 ->
 (exists d,In d bs /\enum_pos d n) \/exists xs',step xs xs'.
Proof.
 intros N S0 i0 S1 S2 i c n xs X Phi1 Phi2 Psi1 Psi2 bs
 HP Hsz HC Hconv Hpos Hbs Hmem Hphi1 Hphi2 Hpsi Hcov.
 destruct(spine_phi_mem_or_luna S1 i Phi1 Psi1 c Hphi1 Hmem
  (exists xs',step xs xs')) as [HM|HS].
 - intros d Hcd HD.
   eapply converted_branch_dead_payload_steps_parent;
     [exact HP|exact Hsz|exact HC|exact Hconv|apply conv_phi_cjoin;exact Hcd|exact HD].
 - left. eapply erased_spine_covered_pos;
     [exact Hpos|exact Hbs|exact HM| |exact Hpsi].
   eapply spine_phi_covers;eassumption.
 - right. exact HS.
Qed.
Print Assumptions converted_branch_dead_payload_steps_parent.
Print Assumptions direct_phi_spine_progress_parent.
