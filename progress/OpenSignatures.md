# Open-signature Rocq specification

This is the relational Rocq version of [type-rules.md](type-rules.md).
Import `OpenSignatures` for the revised calculus. The `TypeRules` entry
point remains the earlier signature-pair calculus; its proofs do not apply
to this version.

The mathematical rule reference, with all 82 context, typing, name-resolution,
and elaboration rules, short prose, examples, and paper citations, is available as
[LaTeX](../docs/type-rules/open-signatures.tex) and
[PDF](../docs/type-rules/open-signatures.pdf).

```sh
make -C progress open-signatures
make -C progress audit-open-signatures
```

The revision builds with Rocq 9.1.0. The normal `progress` build also
includes its modules. Generated artifacts for this version are ignored by
Git; source and build configuration are the reviewable changes.

| Module | Contents |
| --- | --- |
| [OpenSignaturesSyntax.v](OpenSignaturesSyntax.v) | De Bruijn syntax, lifting, substitution, and the types of closure eliminators and generated coercions. |
| [OpenSignaturesCore.v](OpenSignaturesCore.v) | Descriptions with bottom, reference `μᴵ`, `close F G`, case analysis, induction, operational and full reduction, conversion, and declarative typing. |
| [OpenSignaturesElaboration.v](OpenSignaturesElaboration.v) | Open signature assembly, stable constructor identities, local tag translation, empty-payload witnesses, coercion generation, and source elaboration. |
| [OpenSignaturesExamples.v](OpenSignaturesExamples.v) | Lists, nonempty lists, trees, compact/padded rows, source examples, and ten closed computation checks. |
| [OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) | 47 explicitly unproved metatheory and example-typing conjectures. |
| [OpenSignaturesAudit.v](OpenSignaturesAudit.v) | Rule signatures and `Print Assumptions` checks separating conjectures from closed computations. |

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
source codomain and preserve de Bruijn scope when inserting binders.

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

The conjectures cover context validity, substitution, preservation,
progress, full beta/eta normalization and confluence, consistency,
canonical forms, closure elimination, name resolution, coverage, emptiness,
coercion typing, elaboration soundness, coherence, and concrete example
typing. Coherence is observational and quantified over typed closing
substitutions; it does not assert that alternative coercions are
definitionally equal. A deterministic policy for dependent inference and
a semantic construction relating the diagonal to reference `μᴵ` remain
design obligations.

The ten proved examples check only concrete syntax computations, including
`head (singleton a)`, its tail, widening, a compact/padded round trip, bottom
interpretation, opaque closure types, and binder handling. No general
typing or metatheory conjecture is used by those checks. Compiling a
`Conjecture` validates its statement's Rocq type, not its truth.
