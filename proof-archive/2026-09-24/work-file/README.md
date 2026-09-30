# Proof work files

This directory preserves the exploratory Coq developments that were formerly
named `_tmp_*` in `progress/`. The main sources live in `work-file/progress/`;
generated `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files were preserved too,
but source plus a fresh `coqc` run is authoritative.

The scratch modules import the live `progress/Progress.v` and often import one
another by their `_tmp_*` logical names. A typical one-file check is:

```sh
cd work-file/progress
coqc -Q ../../progress '' _tmp_epstep.v
```

For a dependent module, compile its imported scratch modules first in the
same directory. Existing `.vo` files may be stale after edits to
`progress/Progress.v`. Since the module split, historical files using
`Import TypeRules` or `TypeRules.term` also need those references updated to
`TypeRulesCore`; they are not part of the active Makefile build.


## Integrated results (2026-09-05)

The signature-transport proof is complete. The full `progress/Progress.v` rebuild
succeeds, and `Print Assumptions progress_proved` reports
`Closed under the global context`. The standalone transport theorem and
assembled proof also pass their assumption audits.

`Progress.v` embeds the checked conversion, signature-instance translation,
pruning confluence, reduction/pruning commutation, and membership/coverage
proofs as local modules. It specializes the bounded progress induction with
the proved transport theorem. The final theorem statement is unchanged;
`canonical_forms_sig` is no longer used. Only `TypeRulesCore` and Stdlib
are external dependencies.

The new proof sources are `_parent_instance_pruning.v`,
`_parent_pruning_diamond.v`, `_parent_pruning_lower.v`,
`_parent_step_prune.v`, `_parent_pruning_commute.v`,
`_parent_instance_translation.v`, `_parent_instance_join.v`,
`_parent_instance_observations.v`, `_parent_signature_transport.v`, and the
`_luna_instance_*.v` modules. The translation itself is collected in
`progress/SignatureInstances.v`; constructor/payload support remains in the
standalone `SignatureLemmas.v`, `SignatureConversion.v`, and
`ErasureCounterexample.v` libraries. The final `Progress.v` does not require
these standalone or scratch libraries.

The erased-sort reflection shortcut remains false, as proved in
`ErasureCounterexample.v`; progress uses the explicit-instance argument.
The older conditional and diagnostic experiments below are retained as
history and are not part of the final proof. Rebuild scratch libraries before
reusing them after the main `Progress.vo` changes.

## Trusted milestones

The most useful completed source files are:

- `_tmp_pdev_lift.v`
- `_tmp_eta_cancel.v`
- `_tmp_eta_shape.v`
- `_tmp_epstep.v`
- `_tmp_epstep_inv.v`
- `_tmp_eta_tool.v`
- `_tmp_epstep_diamond.v`
- `_tmp_epstep_subst.v`
- `_tmp_epbranches_nth.v`
- `_tmp_pstep_var_rigid.v`
- `ProgressWork.v` (stable aggregate of every completed work module)
- `_work_commute.v`
- `_work_mixed_closure.v`
- `_work_cjoin.v`
- `_work_cstep_invariants.v`
- `_work_conv_whd_pos.v`
- `_glm_enumt_cons_nil.v`
- `_glm_conv_subst0.v`
- `_parent_conv_subst_all.v` (closed arbitrary-cutoff two-sided conversion
  substitution, derived from cutoff zero through fresh-variable lambda
  injectivity)
- `_glm_muapp_sort_from_pi.v` (closed consumer, conditional only on the
  remaining Pi-codomain compatibility theorem)
- `_glm_phi_erase_epstep_counterexample.v` (closed boundary result showing
  why unrestricted eta reflection must not be assumed)
- `_parent_phi_erase_sort_algebra.v`
- `_parent_check_pi_formation.v` (closed inversion retaining the domain and
  codomain formation premises of any checked syntactic Pi)
- `_parent_mus_cstep_inv.v` (closed one-step/block/path inversions showing
  that neither a bare `TMuS` head nor a stuck `TMuS` application can reduce
  to a sort)
- `_parent_inert_cstep_inv.v` (closed combined-path inversions for `TUnit`
  and `TPair`, including their sort-endpoint contradictions)
- `_parent_epi_nonsort.v` (closed sort-endpoint contradictions for both
  syntactic `TEPi` computation roots)
- `_parent_cstep_standardize_counterexample.v` (closed counterexample to the
  core-before-eta sort-standardization premise)
- `_parent_mueq_eta_sort_root.v` (closed sort-ending root-eta simulation that
  removes the false general theorem's opaque-head side condition; only the
  separately named lift-descent interface remains as a theorem binder)
- `_parent_mueq_eta_sort_recursive.v` (closed well-founded root-eta case:
  assuming sort transport only for strictly smaller sources, it transports
  the eta redex to the same sort without any lift-descent premise; confluence
  also closes the whole syntactic eta-redex source case)
- `_parent_mueq_sort_stable.v` (closed endpoint transport for every source
  already carrying a rigid `hshape`; only the sort case survives)
- `_parent_mueq_projection_sort_recursive.v` (closed well-founded `fst` and
  `snd` pair-redex cases, using confluence to transport the selected component)
- `_parent_mueq_interp_sort_recursive.v` (closed well-founded
  `TInterp (TIVar i) X` root case, plus closed contradictions for the five
  interpretation roots whose contracta have rigid non-sort heads)
- `_parent_pi_sort_rep_consumer.v` (closed qconv-chain consumer reducing the
  needed Pi/sort codomain fact to the precise endpoint-directed
  `mueq_pi_sort_rep_transport_parent` interface)
- `_parent_pi_sort_rep_normalize.v` (closed equivalence of the representation
  premise with a direct Pi endpoint plus codomain-sort endpoint statement)
- `_parent_mueq_pi_hshape_recursive.v` (closed stable-head branch for that
  direct endpoint theorem, recursing only on the Pi codomain)
- `_parent_muapp_sort_from_endpoint.v` (closed final `muapp_sort` consumer and
  subtyping invariant, conditional only on that precise endpoint interface)
- `_parent_phi_erase_sort_direct.v` (closed direct consumer reducing the
  specialized Pi/sort codomain fact to stable sort reflection through
  `phi_erase`, without phase standardization)
- `_parent_phi_erase_sort_hshape.v` (closed direct erased-sort reflection for
  every source already carrying a stable head tag)
- `_parent_phi_erase_idem.v` (closed idempotence of `phi_erase`)
- `_parent_phi_erase_epstep_forward.v` (closed forward preservation of
  parallel eta reduction and branch development by erasure)
- `_parent_phi_erase_sort_factor.v` (closed factorization of direct sort
  reflection into pstep erasure reflection and endpoint-aware one-step eta
  backward conversion, without standardization)
- `_parent_phi_erase_fixed_sort.v` (closed reduction-to-sort consequence for
  an erasure-fixed term convertible to a sort)
- `_parent_muapp_sort_from_pi_sort.v` (closed generic final typing/subtyping
  consumer from only the specialized Pi-with-sort codomain property, with a
  corollary conditional solely on direct erased-sort endpoint reflection)

`ProgressWork.v` re-exports the stable subset above.  The many other
`_glm_*` files are retained as reusable proof layers, but conditional files
should be checked at their theorem binders before promotion; a compiling
conditional theorem is not evidence that its premise has been discharged.

Their dependencies include `_tmp_lower.v`, `_tmp_case_lift.v`,
`_tmp_epi_helper.v`, `_tmp_ind_helper.v`, `_tmp_switch_full.v`,
`_tmp_iall_full.v`, and `_tmp_hyps_full.v`.

## Do not treat as completed

- `_tmp_lower.v` aborts `lower_sound_aux` near the end; earlier declarations
  in the module are usable.
- `_tmp_convpos.v` assumes `conv_join` with `Parameter`.
- `_tmp_eqdec.v`, `_tmp_subst_var.v`, and `_tmp_dbg.v` contain aborted
  experiments.
- `_tmp_convfinal.v` is a failed direct approach, not a proof.
- `_work_commute_eta_ind.v` is an abandoned direct induction and contains an
  `Abort`; use `_work_commute.v` instead.
- `_glm_conv_subst_sort.v` is rejected: it does not compile and its proposed
  transitivity step is not valid.

Use `rg -n '\b(Abort|Admitted|Parameter|Axiom|Conjecture)\b' *.v` before
promoting any scratch module into `Progress.v`.
