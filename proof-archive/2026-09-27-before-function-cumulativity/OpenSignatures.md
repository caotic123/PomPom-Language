# Open-signature Rocq specification

This is the relational Rocq version of [type-rules.md](type-rules.md).
The representation uses [stable numeric IDs](STABLE_IDS.md) and an
alpha-equivalence setoid, with sequential term interning and no hashing.
**Twenty-seven metatheory claims have closed proofs**, 16 derived claims depend on
existing conjectures, and 4 remain conjectures. See
[PROOF_STATUS.md](PROOF_STATUS.md) for dependencies and
[PROOF_START.md](PROOF_START.md) for the first proof and acceptance check.

The mathematical rule reference, with the earlier 82 context, typing,
name-resolution, and elaboration rules, examples, and paper citations, is available as
[LaTeX](../docs/type-rules/open-signatures.tex) and
[PDF](../docs/type-rules/open-signatures.pdf).
Its Rocq binder-encoding details predate this migration; the active source
also includes explicit alpha conversion and alpha transport of typing.

```sh
make -C progress check-bindings
make -C progress open-signatures
make -C progress audit-open-signatures
```

The syntax, alpha setoid, core rules, elaboration, examples, and binding
regressions are checked with Rocq 9.1.0. The full build and umbrella
`Require Import OpenSignatures` succeed; type correctness and the other
open obligations remain explicit conjectures. The independent
`check-bindings` target imports through `OpenSignaturesExamples`.

| Module | Contents |
| --- | --- |
| [OpenSignaturesSyntax.v](OpenSignaturesSyntax.v) | Stable binder IDs, finite-map contexts, capture-avoiding substitution, and generated helper types and terms. |
| [OpenSignaturesAlpha.v](OpenSignaturesAlpha.v) | Alpha-equivalence setoid, exact comparison, sequential term IDs, and proved table invariants. |
| [OpenSignaturesCore.v](OpenSignaturesCore.v) | Descriptions with bottom, reference `μᴵ`, `close F G`, case analysis, induction, operational and full reduction, conversion, and declarative typing. |
| [OpenSignaturesBinding.v](OpenSignaturesBinding.v) | Substitution support, alpha/free-variable invariance, context scoping, and freshness proofs without metatheory axioms. |
| [OpenSignaturesSubstitution.v](OpenSignaturesSubstitution.v) | Axiom-free alpha compatibility, free-variable support, binder renaming, and substitution composition. |
| [OpenSignaturesProgress.v](OpenSignaturesProgress.v) | Reduction invariants, canonical forms, and progress parameterized only by conversion joinability; no conjectures are imported. |
| [OpenSignaturesElaboration.v](OpenSignaturesElaboration.v) | Open signature assembly, stable constructor identities, local tag translation, empty-payload witnesses, coercion generation, and source elaboration. |
| [OpenSignaturesExamples.v](OpenSignaturesExamples.v) | Lists, nonempty lists, trees, compact/padded rows, source examples, and five checked computations. |
| [OpenSignaturesDerivedTyping.v](OpenSignaturesDerivedTyping.v) | Function/product formation, constant functions, abort, and unroll; weakening is explicit. |
| [OpenSignaturesDataTyping.v](OpenSignaturesDataTyping.v) | Description payload introductions and projections. |
| [OpenSignaturesRowTyping.v](OpenSignaturesRowTyping.v) | Row computation, tuple typing, signatures, and constructors. |
| [OpenSignaturesCaseTyping.v](OpenSignaturesCaseTyping.v) | Handler tuples, row mapping, and case typing. |
| [OpenSignaturesElaborationSoundness.v](OpenSignaturesElaborationSoundness.v) | Simultaneous synthesis/checking/case soundness with explicit premises. |
| [OpenSignaturesCoercionTyping.v](OpenSignaturesCoercionTyping.v) | Row handlers and description coercions with explicit weakening and dead-witness typing. |
| [OpenSignaturesTransport.v](OpenSignaturesTransport.v) | Axiom-free domain formation; derived context exchange and dependent function coercions. |
| [OpenSignaturesSubtypingSoundness.v](OpenSignaturesSubtypingSoundness.v) | Subtyping soundness from weakening, type correctness, full preservation, and dead-witness typing. |
| [OpenSignaturesExampleTyping.v](OpenSignaturesExampleTyping.v) | Polymorphic list, nonempty-list, and tree definitions and constructors. |
| [OpenSignaturesBindingTests.v](OpenSignaturesBindingTests.v) | Context, substitution, alpha-equivalence, typing, and sequential-ID regressions. |
| [OpenSignaturesConfluence.v](OpenSignaturesConfluence.v) | Closed conversion joinability and confluence via the auxiliary nameless proof and checked encoding/reflection. |
| [OpenSignaturesLabels.v](OpenSignaturesLabels.v) | Closed uniqueness of row label resolution. |
| [OpenSignaturesTypingEncoding.v](OpenSignaturesTypingEncoding.v) | Typed encoding/reflection gives axiom-free weakening, substitution, and type correctness. |
| [OpenSignaturesBeta.v](OpenSignaturesBeta.v) | Beta preservation for the named calculus, independent of full preservation. |
| [OpenSignaturesPayloadInversion.v](OpenSignaturesPayloadInversion.v) | Axiom-free inversion of close constructors. |
| [OpenSignaturesEtaCounterexample.v](OpenSignaturesEtaCounterexample.v) | Axiom-free refutation of unrestricted full preservation under the current cumulativity rule. |
| [OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) | Twenty-seven closed claims, 16 derived claims depending on conjectures, and 4 conjectures. |
| [OpenSignaturesAudit.v](OpenSignaturesAudit.v) | Rule signatures and assumption checks, beginning with `context_validity`. |
| [PROOF_START.md](PROOF_START.md) | First theorem, proof approach, and acceptance criteria. |

Prior proofs, the unfinished progress development, and generated artifacts
are saved in [proof-archive/2026-09-24](../proof-archive/2026-09-24/README.md).
The active build includes no archive modules or previous proof implementations.

The main closure rule is implemented directly:

```text
xs : ⟦F i⟧ (close G G)
──────────────────────
in xs : close F G i
```

The raw syntax retains the implicit index type as an explicit argument to
generic operators. `close` types never unfold by conversion. Recursive
induction uses the diagonal motive `P G j y` for children, and its recursive
call uses outer definition `G`. One-layer `closeCase` supports motives at
every universe level; recursive induction is small, as in the sketch.

The core has no constructor-subtyping relation. `sub` in the elaboration
module generates a core function. Live row branches keep their payload and
translate their tag by constructor identity. Impossible source branches
generate empty elimination, including when no target position exists.
Dependent function coercions substitute the converted argument into the
source codomain and choose fresh numeric binders to avoid capture.

The modeled source syntax accepts description-valued constructor schemes:
the positive recursive binder has already been represented by `TIVar`.
It specifies the theory boundary rather than a parser for the proposed
surface notation. Raw `ECore` terms are checked-only; an annotation is
required to synthesize their type. Guessing a declarative type for an
unannotated core `in` could assign it different constructor identities.

The elaboration relations permit explicit derivations and checked
emptiness witnesses. They are not a deterministic implementation of
inference or a decision procedure for semantic inhabitation. Source case
results are nondependent; the core case eliminator itself is dependent.

The theorem statements cover context validity, substitution, preservation,
progress, full beta/eta normalization and confluence modulo alpha, consistency,
canonical forms, closure elimination, name resolution, coverage, emptiness,
coercion typing, elaboration soundness, coherence, and concrete example
typing. Coherence is observational and quantified over typed closing
substitutions; it does not assert that alternative coercions are
definitionally equal. A deterministic policy for dependent inference and
a semantic construction relating the diagonal to reference `μᴵ` remain
design obligations.

Five current example proofs check singleton head, tail, widening, a
compact/padded round trip, and preservation of a free payload ID. The
binding regressions also exercise shadowing, capture avoidance, alpha
comparison, stable lookup, and ID reuse. None uses a metatheory conjecture.
The ten older computation proofs remain in the archive. Compiling a
`Conjecture` validates its statement's Rocq type, not its truth.

The current unrestricted eta rule makes `full_preservation` false. See the axiom-free [counterexample](OpenSignaturesEtaCounterexample.v) and [proof status](PROOF_STATUS.md).
