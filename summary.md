# `Progress.v` proof status

Updated 2026-09-05. No new axioms are permitted. The original scope was the
local assumptions in `progress/Progress.v`; its completed proof now has no
global assumptions. Other metatheory obligations remain separate conjectures.

## Module layout

`progress/TypeRulesCore.v` contains the definitions. `progress/TypeRules.v`
exports the core and the individual theorem files documented in
[progress/README.md](progress/README.md). Progress is proved; seven other
main obligations remain conjectures. The module split preserves all rule
and theorem statements. The full rebuild and `make -C progress check` pass. The public export audit
confirms closed progress and type-side preservation, with the original
preservation dependency retained by multi-step preservation.

## Current status (2026-09-05)

The final signature-transport obligation is proved. The complete `progress/Progress.v` rebuild succeeds.
`Print Assumptions progress_proved` reports **Closed under the global context**.
The standalone transport theorem and the assembled proof also compile with
closed assumption audits.

`progress/Progress.v` contains the entire proof and imports only `TypeRulesCore`
and Stdlib. The statements of `progress_n` and `progress_proved` are unchanged.
The final proof specializes the checked bounded progress induction with the
proved tag-transport lemma. It no longer uses `canonical_forms_sig`.
No typing, conversion, or reduction rules were changed, and no axioms or
admitted proofs were added.

The signature proof translates each mu-S application into an explicit
signature instance. Directed pruning deletes only labels whose branch
payload is impossible under the smaller-term progress hypothesis. Pruning
is confluent and commutes with beta/eta reduction. Their combined confluence
provides a common instance at which source membership and target coverage
can be compared. A removed source tag forces a payload step; a retained tag
selects a covered case branch.

The earlier proofs of `conv_whd`, `conv_pos`, `spine_covered`,
`conv_enumt_cons_nil_absurd`, and `muapp_sort` remain closed.

The earlier erased-sort reflection shortcut is false; its checked witness
remains in `progress/ErasureCounterexample.v`. That counterexample does not
refute progress and the final proof does not require that shortcut.

The following development notes are historical. Conditional or aborted
experiments described below are not dependencies of the final proof.

## Signature conversion progress (2026-09-05)

`progress/SignatureConversion.v` compiles and imports only the three standalone
libraries `Progress`, `SignatureLemmas`, and `ErasureCounterexample`, plus
Stdlib. Its final seven assumption audits are closed under the global context.
It contains the following new checked results:

- erased Sigma and enumeration value classification, retaining checked
  component origins;
- product and choice payload type extraction, including substitution of the
  dependent codomain;
- `desc_against_erased_step_parent`: all four `desc_against` constructors,
  including finite choices, force a payload step under the smaller-term
  progress hypothesis;
- `erased_spine_covered_pos`: erased-convertible spines preserve the covered
  numeric tag;
- `mus_branch_transport_luna`: arbitrary full conversion between mu-S
  applications preserves the erased branch description, via the finer
  branch erasure;
- `direct_phi_spine_progress_parent`: a direct Eq-phi pruning step either
  preserves a covered numeric tag or yields a payload step.

The bounded-progress premise is explicit and is precisely the induction
hypothesis available in the main case proof. It is not a new axiom. The direct
Eq-phi theorem does not cover an arbitrary beta/eta/phi conversion derivation.
These direct-conversion lemmas are now included in the complete signature
transport proof described above.

## Checked confluence and conversion infrastructure

The stable aggregate is `work-file/progress/ProgressWork.v`. Important checked
files include:

- `_work_commute.v`: pstep/epstep commutation (the eta side correctly uses an
  rtc closure);
- `_work_mixed_closure.v`: diamond and confluence for the combined `cstep`;
- `_work_cjoin.v`: the `cjoin` equivalence and conversion bridges;
- `_work_cstep_invariants.v`: stable head, `EnumT`, Pi, sort, and position
  inversions for combined paths;
- `_work_conv_whd_pos.v`: exact `conv_whd` and `conv_pos` proofs;
- `_luna_mueq.v`, `_luna_mueq_equiv.v`: structural modulo relation and its
  equivalence laws;
- `_glm_qconv_def.v`, `_glm_qconv_congr.v`, `_glm_qconv_main.v`: quotient-path
  relation, all constructor congruences, and `conv_qconv_glm`;
- `_glm_injectivity_close_rep.v`, `_glm_injectivity_close_main.v`: honest
  component-changing representation transport and conditional exact EnumT/Pi
  injectivity;
- `_glm_muapp_sort_origin.v`, `_glm_muapp_sort_close.v`,
  `_glm_muapp_sort_specialized.v`: the complete typing-side `muapp_sort` proof,
  conditional only on Pi-codomain injectivity and substitution of a term
  convertible to a sort;
- `_glm_conv_subst0.v`: exact two-sided conversion substitution at cutoff 0,
  proved by beta-expanding both endpoints; this avoids any `cv_phi` induction;
- `_parent_conv_subst_all.v`: exact two-sided conversion substitution at every
  cutoff.  Lambda conversion is injective by lifting both bodies, applying
  them to a fresh variable, beta-reducing, and cancelling lift/substitution;
  induction on the cutoff then reduces the successor case to cutoff zero.
  The exported `conv_subst_compatible_parent` has no assumptions;
- `_glm_muapp_sort_from_pi.v`: complete `muapp_sort` proof conditional only on
  Pi-codomain injectivity (the substitution premise has been eliminated);
- `_glm_enumt_cons_nil.v`: closed contradictions for
  `TEnumT (TConsE ...)` versus `TEnumT TNilE` in both orientations, sufficient
  to replace the only use of `conv_enumt_inj`;
- `_glm_phi_erase_epstep_counterexample.v`: a closed counterexample to
  unrestricted one-step eta reflection through `phi_erase`, with reusable
  rigid-head inversion lemmas and the strongest exact negation theorem;
- `_glm_phi_erase_sort_pipeline.v`: the complete closed conditional pipeline
  from full core reflection, sort-only eta reflection, and sort-endpoint
  standardization through stable erasure reflection, sort-codomain transport,
  subtyping transport, and the final `muapp_sort_narrow_glm` theorem;
- `_parent_phi_erase_sort_algebra.v`: closed sort/variable preimage,
  cutoff-zero substitution-to-sort, and `enum_pos` erasure-reflection helpers;
- `_parent_check_pi_formation.v`: closed typing inversion showing that every
  checked syntactic Pi retains domain and codomain formation derivations,
  including checks ending through conversion, subsumption, or expansion;
- `_parent_mus_cstep_inv.v`: closed pstep/epstep/cstep path inversions for a
  bare `TMuS` head, including the endpoint contradiction
  `~ rtc cstep (TMuS S) (TSort j)`, plus the corresponding contradiction for
  a stuck `TApp (TMuS S) i`; these rule out opaque eta exceptions whenever
  the exceptional term itself must continue to a sort;
- `_parent_inert_cstep_inv.v`: closed combined-path head preservation for the
  unclassified inert `TUnit` and `TPair` forms, with direct contradictions for
  sort endpoints; these discharge the non-eta `hyps` contracta that fall
  outside the existing `hshape` invariant;
- `_parent_epi_nonsort.v`: closed contradictions for both syntactic `TEPi`
  roots; their direct contracta have rigid Unit/Sigma heads, so confluence
  excludes a sort endpoint;
- `_parent_mueq_eta_sort_root.v`: closed sort-ending root-eta simulation.  It
  uses the preceding endpoint contradiction to eliminate the known
  `me_muapp` obstruction, so the old extra non-`TMuS` head premise is gone;
  the existing lift-descent interface remains an explicit theorem binder;
- `_parent_mueq_eta_sort_recursive.v`: stronger closed root-eta case for the
  final well-founded proof.  Given sort transport only for strictly smaller
  source terms, it reduces the related eta body to the same sort and then
  contracts eta; confluence first shows that any syntactic eta redex reaching
  a sort has a contractum reaching the same sort, so the complete eta-redex
  source case is closed.  It needs neither unrestricted eta simulation nor
  the old lift-descent interface;
- `_parent_mueq_sort_stable.v`: closed sort transport across `mueq` for all
  rigid `hshape` sources at once.  Preservation of the stable head makes every
  non-sort tag contradictory, while the sort constructor fixes the level.  It
  also packages the reusable confluence principle that any root contractum
  with a rigid non-sort head makes a sort endpoint impossible;
- `_parent_mueq_projection_sort_recursive.v`: closed well-founded transport
  for both projection redexes.  Confluence forces the selected pair component
  to reach the endpoint sort, the smaller-term hypothesis transports that
  component across `mueq`, and the related projection then contracts;
- `_parent_mueq_interp_sort_recursive.v`: the analogous closed
  interpretation-variable case.  Its contractum `TApp X i` is strictly
  smaller, so the recursive transport hypothesis and the corresponding
  `ps_interp_var` contraction close the related endpoint.  The remaining
  interpretation roots (`TI1`, product, Pi, Sigma, choice) are also closed:
  their direct contracta have rigid Unit/Pi/Sigma heads, so confluence rules
  out a sort endpoint;
- `_parent_pi_sort_rep_consumer.v`: closed quotient-chain consumer for the
  precise remaining endpoint interface.  Because arbitrary `qconv`
  intermediates need not be syntactic Pis, it carries an honest `cjoin`-based
  Pi representation together with a codomain path to the target sort.  An
  inhabitant of `mueq_pi_sort_rep_transport_parent` now yields the exact
  `conv (TPi A0 (TSort j)) (TPi A1 B1) -> conv B1 (TSort j)` fact;
- `_parent_pi_sort_rep_normalize.v`: closed equivalence between that
  cjoin-based interface and the simpler direct endpoint statement saying that
  `t ->* TPi A B` with `B ->* TSort j` transports across one `mueq` link.
  This gives the well-founded assembly a smaller, syntax-directed target;
- `_parent_mueq_pi_hshape_recursive.v`: closed stable-head branch of the
  direct endpoint theorem.  A stable source reaching a Pi must itself be a
  Pi; its codomain is strictly smaller, so the recursive sort-transport
  hypothesis transports that codomain across structural `mueq`;
- `_parent_muapp_sort_from_endpoint.v`: closed final typing consumer that
  weakens the old full Pi-injectivity premise to exactly
  `mueq_pi_sort_rep_transport_parent`.  Its subtyping invariant handles
  conversion, transitivity, Pi variance, and the impossible non-Pi targets;
  consequently that one endpoint premise now implies the original
  `muapp_sort` statement directly;
- `_parent_phi_erase_sort_direct.v`: a smaller phase-order-independent
  consumer.  The single premise `phi_erase_sort_endpoint_reflect_parent`
  reflects a combined path from an erased term to a stable sort.  Together
  with the already closed `conv_phi_cjoin` and Pi cjoin inversion, it yields
  the exact Pi-with-sort codomain property directly; no standardization or
  full Pi simulation is involved;
- `_parent_phi_erase_sort_hshape.v`: closed direct reflection branch for every
  classified stable head.  Erasure preserves its head tag, so only an actual
  source sort can reach a sort endpoint;
- `_parent_phi_erase_idem.v`: closed proof that `phi_erase` is idempotent,
  allowing erased intermediate reducts to serve as their own preimages in
  endpoint/path inductions;
- `_parent_phi_erase_epstep_forward.v`: closed forward preservation of
  parallel eta reduction and eta branch development by `phi_erase`; this is
  deliberately only the valid forward direction;
- `_parent_phi_erase_sort_factor.v`: closed factorization of the active direct
  reflection theorem into two smaller statements: ordinary pstep erasure
  reflection for core blocks, and endpoint-aware backward conversion for one
  genuine eta step whose reduct is already convertible to the final sort.
  Reflexive eta blocks are skipped by the outer path induction, while the tail
  after a nonempty block supplies the conversion, so no eta reduction
  reflection and no phase standardization are assumed;
- `_parent_phi_erase_fixed_sort.v`: closed lemma turning conversion of an
  erasure-fixed term to a sort into an actual combined-reduction path to that
  sort; this is available to the endpoint-aware eta proof;
- `_parent_muapp_sort_from_pi_sort.v`: closed generic typing/subtyping
  consumer from only that specialized Pi-with-sort codomain property, plus a
  corollary reducing the original `muapp_sort` statement exactly to
  `phi_erase_sort_endpoint_reflect_parent`;
- `_glm_cjoin_subst_{pstep,epstep,cstep,main}.v`: arbitrary same-substituent
  compatibility for pstep, epstep, cstep, rtc cstep, and cjoin;
- `_glm_mueq_sim_close_rep.v`, `_glm_mueq_sim_close_sort.v`: complete
  conditional consumers from a direct `cstep`/`mueq` simulation to EnumT/Pi
  component transport and sort-target substitution;
- `_glm_final_from_sim_glm.v`: the final conditional bridge from simulation to
  exact `conv_enumt_inj`, Pi injectivity, sort-target substitution, and
  `muapp_sort`.

All listed principal theorems have been independently recompiled and audited
with `Print Assumptions`; they are closed. Compatibility assumptions in the
conditional theorems are binders, not global axioms.

## Reduction/substitution milestones

The following reusable layers are also checked and closed:

- `_glm_conv_lift_bundle_{eval,desc,spine,main}.v`: exact conversion lifting;
- `_glm_subst_reduction_bundle_{step,sem,eval,spine}.v`: step, evaluation,
  neutrality, pruning, and spine-phi under same substitution;
- `_glm_conv_subst_{algebra,rigid,same_neutral,neutral_pair}.v`: substitution
  algebra, rigid-skeleton transport, and neutral-substituent conversion;
- `_glm_conv_subst_neutral_at.v`: neutral-at-cutoff strengthening (mechanical
  worker errors were repaired and the file now independently compiles);
- `_glm_mueq_pstep_atomic.v`, `_glm_mueq_epstep_atomic.v`: the opaque
  mu-application cases for pstep/epstep, including rtc-oriented corollaries;
- `_glm_mueq_pstep_conditional_inv.v`: structural mueq inversions and TCase
  branch congruence helpers.

Unrestricted conversion substitution is now proved without induction over
conversion.  The earlier direct constructor induction was blocked at `cv_phi`
because arbitrary substitution can destroy its neutral-spine premise;
`_parent_conv_subst_all.v` bypasses that obstruction by deriving every cutoff
from the closed cutoff-zero theorem through fresh-variable lambda injectivity.

## Important correction: eta-only simulation is false

The attempted factorization

```coq
mueq t u -> epstep t t' ->
exists u', rtc epstep u u' /\ mueq t' u'
```

is false because `me_muapp` stores an arbitrary full `conv` proof and overlaps
eta bodies. `_glm_mueq_eta_shape.v` contains the checked counterexample
`mueq_eta_muapp_obstruction_glm`. It uses the beta expansion of `TVar 0` to
build an mueq-related eta body whose right side must beta-reduce before eta can
fire. `Print Assumptions` reports the counterexample closed.

This refutes only the too-strong *eta-only simulation route*, not the original
Progress axioms. The correct remaining target is direct simulation by the
combined phase:

```coq
forall t u t', mueq t u -> cstep t t' ->
  exists u', rtc cstep u u' /\ mueq t' u'.
```

Here the right side may take a pstep phase to expose eta and then contract it.
The checked consumers in `_glm_mueq_sim_close_rep.v` and
`_glm_mueq_sim_close_sort.v` are already parameterized by exactly this direct
interface.

Unrestricted eta-step reflection through `phi_erase` is also false.  The
closed witness in `_glm_phi_erase_epstep_counterexample.v` is

```coq
TLam (TApp (TMuS (TVar 0)) (TVar 0)).
```

Its erasure eta-contracts to `TMuS TUnit`, while the original term is eta-rigid
because `TMuS (TVar 0)` is not in the image of `lift 1 0`.  This does not
refute sort-ending reflection: that fabricated reduct has `TMuS` head and
cannot itself eta-reduce to a sort.  Current work therefore uses stable-sort
invariants, not the false unrestricted interface.

Core-before-eta standardization at a sort endpoint is false as well.
`_parent_cstep_standardize_counterexample.v` gives the smaller closed witness

```coq
TSnd (TLam (TApp (TPair TUnit (TSort 0)) (TVar 0))).
```

Eta exposes the pair under `TSnd`, then the core projection produces
`TSort 0`.  The source is pstep-rigid, while every eta-only path preserves the
outer `TSnd`; consequently there is no factorization into `rtc pstep` followed
by `rtc epstep`.  Therefore the third binder of
`_glm_phi_erase_sort_pipeline.v`, `cstep_sort_standardization_glm`, is
formally refuted and that conditional pipeline cannot be instantiated.

## Completed signature obligation

The formerly outstanding interface is now proved by
`_parent_signature_transport.signature_tag_transport_proved`, embedded in
`Progress.v`:

```coq
forall N S0 i0 S1 i1 c n xs X bs,
  bounded_progress_parent N -> tsize xs <= N ->
  check [] xs (TInterp (TApp (branches (TApp S0 i0)) c) X) ->
  conv (TApp (TMuS S0) i0) (TApp (TMuS S1) i1) ->
  enum_pos c n -> Forall (fun d => exists m, enum_pos d m) bs ->
  spine_mem c (labels (TApp S0 i0)) ->
  covers bs (labels (TApp S1 i1)) ->
  (exists d, In d bs /\ enum_pos d n) \/
  exists xs', step xs xs'.
```

The general beta/eta/phi case uses explicit signature instances and combined
confluence. `SignatureProgressReduction.progress_n_transport` consumes this
proved theorem, so no signature-transport premise remains in `progress_n`
or `progress_proved`.

The earlier beta/eta-only transport theorem and the branch-erasure recovery
counterexample remain in `progress/SignatureTagTransport.v`. They document
why the final proof tracks enabled labels explicitly.

The exact Pi-codomain conversion property formerly listed here is no longer
needed for `muapp_sort`; the closed erased-observation proof replaces that
approach.

New checked sublemmas are in `_luna_repair_erased_sort_sub.v`,
`_luna_repair_erased_subst.v`, `_luna_repair_app_origin.v`, and
`_parent_repair_muapp.v`; these are integrated in `MuApplicationSort`.
`progress/SignatureLemmas.v` collects the checked Sigma-join inversion,
pair and constructor origins, membership through spine inclusion, live-tag
membership through pruning, and erased-empty-enumeration impossibility for
closed values. It also proves the empty-choice dead-payload progress case,
given progress for the payload's smaller component. The file imports only
`Progress` and Stdlib; its exported results are closed. These supporting
results are used by the now-complete signature-transport argument.

The new work modules `_luna_finish_core_reflect.v`,
`_luna_finish_branch_erase.v`, `_parent_finish_fconv_lift.v`,
`_parent_finish_branch_sound.v`, `_parent_finish_bad_rigid.v`,
`_luna_finish_branch_rigid.v`, and `_luna_finish_sort_counterexample.v`
were compiled with closed assumptions. The final counterexample and its
required proofs are collected in `progress/ErasureCounterexample.v` so
checking it does not require the scratch-module dependency graph.

`_luna_finish_pstep_sim.v` is an unverified attempt to instantiate the older
large pstep/mueq simulation proof. It is not part of the integrated proof or
the trusted counterexample dependency graph; `-vos` alone is not validation.

Scratch `.vo` files importing the previous `Progress` become stale after
rebuilding the integrated `Progress.v`; rebuild their source dependencies
before reusing them. The standalone files in `progress/` avoid that dependency.

## Known invalid or diagnostic files

- `_glm_conv_subst_sort.v` is rejected: it does not compile and its proposed
  transitivity step misuses rigid-skeleton substitution.
- `_glm_phi_erase_pstep_sort_dbg.v` is only an aborted goal probe from the
  superseded mutual-derivation attempt.
- `_tmp_lower.v`, `_tmp_eqdec.v`, `_tmp_subst_var.v`, `_tmp_dbg.v`, and
  `_tmp_convfinal.v` contain aborted/diagnostic experiments.
- `_tmp_convpos.v` contains a `Parameter` and is not trusted.

These files must not be imported into the final proof.

## Verification

Representative work-file check:

```sh
cd work-file/progress
coqc -Q ../../progress '' _glm_final_from_sim_glm.v
coqc -Q ../../progress '' _glm_mueq_eta_shape.v
```

Build and audit from the repository root (the Makefile orders dependencies):

```sh
make -C progress check
rg -n '^(Axiom|Conjecture)|Admitted|admit' progress/Progress.v
```

Then:

```coq
Require Import Progress.
Print Assumptions progress_proved.
```
