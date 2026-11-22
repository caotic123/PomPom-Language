# Annotated core repair

On September 30 the user selected **explicit core annotations with general
eta contraction** as the repair for full preservation. **Full preservation is
proved for this core without axioms**
([AFullPreservation.v](AFullPreservation.v)):

```coq
Theorem full_preservation : forall Gamma t u A,
  typing Gamma t A -> reduction t u -> typing Gamma u A.
```

`reduction` contains all 31 primitive root computations of the raw calculus,
general eta contraction, and every one-hole compatible context: 100
positions, including binders and every annotation. Multistep preservation
follows. `reduction_erasure` proves that each annotated step erases to one
raw `reduction` step, or to no step when it occurs inside an erased
annotation.

**Status (October 11 decision):** the core stays a checked side development.
It has not replaced the public named calculus, which keeps its 46 proved /
1 refuted status. Annotated strong normalization is open and needs a new
typed semantic model; see [Normalization is open](#normalization-is-open)
and [Decision](#decision).

The new syntax retains the domain and codomain on lambdas and applications,
the dependent product on pairs and projections, the enumeration on positions,
and the index type on description constructors. Reference and closure rolls
have separate annotated constructors, both erasing to the old `TIn`.
Annotations are terms in the same syntax. All binding operations and compatible
contexts traverse them, with the correct extra binder in dependent codomains.

For example, the old counterexample contains the local identity
`lambda x. x`. Its annotated version is `lambda x : A. x` with result
annotation `A`. Thus the function expression beneath `lambda A` contains
`A` freely in its annotations. It fails the eta freshness test.
[ARegression.v](ARegression.v) proves that the annotated source still has
the original polymorphic type, erases to the exact counterexample, and has
no root eta contraction. It also checks contraction of an application and
proves the general eta schema for arbitrary annotated functions.

The de Bruijn rule is:

```text
lambda [A; B]. app [C; D] (lift f) #0  -->eta  f
```

Here `lift` traverses the entire `f`, including every annotation. There is
no restriction to values or neutrals and no premise that assumes typing of
the reduct. The executable `eta_contract` checks absence of index zero and
removes the unused binder. Its soundness, completeness, and the rule's
stability under lifting and substitution are proved in [AEta.v](AEta.v).

[ATyping.v](ATyping.v) checks annotations recursively for every constructor.
Judgment result types and context entries use erased types, so type conversion
uses the existing raw beta/eta equality and cumulative universe comparison.
This does not erase annotations from the terms on which eta operates.
The erasure theorem maps every annotated typing derivation to a checked
original typing derivation. Weakening, substitution, type-comparison transport,
and beta preservation are proved for the new judgment, without axioms.

## Proof structure

| File | Result |
| --- | --- |
| [AStrengthening.v](AStrengthening.v) | Annotation-sensitive strengthening with a reconstructed, possibly more precise type. |
| [AEtaPreservation.v](AEtaPreservation.v) | General eta preservation for arbitrary contracted functions. |
| [ARootBeta.v](ARootBeta.v), [ABeta.v](ABeta.v), [AProjections.v](AProjections.v) | Preservation for every primitive root computation. |
| [ACompatible.v](ACompatible.v) | Preservation through every compatible context, including annotations. |
| [AStructuralPreservation.v](AStructuralPreservation.v) | Combination of the root, eta, and compatible cases. |
| [AFullPreservation.v](AFullPreservation.v) | Public statement, multistep form, and erasure simulation. |
| [ACriticalPair.v](ACriticalPair.v) | Annotated reduction is not confluent on the nose. |
| [ACompleteness.v](ACompleteness.v) | Annotation completeness: every raw typing derivation has an annotated term with the same erasure and type. |
| [AStepFunction.v](AStepFunction.v) | Executable root computation matching `structural_root`; decidability of annotated reduction. |
| [ACfRaw.v](ACfRaw.v), [ACfHelpers.v](ACfHelpers.v) | Raw freshness through reduction, conversion, and universe comparison; generation lemmas and rigid-head separation. |
| [ACfNormal.v](ACfNormal.v) | Typed annotated normal forms erase to raw normal forms. |
| [ACfConfluence.v](ACfConfluence.v) | Confluence and conversion joinability modulo annotations, given strong normalization. |

## Confluence holds only modulo annotations

[ACriticalPair.v](ACriticalPair.v) types this term in the context
`f : Unit -> Sort 0`:

```text
app [Unit; Sort 1] (lambda [Unit; Sort 0]. app [Unit; Sort 0] f #0) tt
```

Here the lambda is used at `Unit -> Sort 1` through function cumulativity.
Beta yields `app [Unit; Sort 0] f tt`. Eta yields `app [Unit; Sort 1] f tt`.
Both reducts are normal and distinct, and they have the same erasure.
`annotated_reduction_not_confluent` refutes plain Church–Rosser for annotated
reduction without axioms. Any confluence claim for this core must therefore
compare reducts modulo annotations. Raw eta can still fire where annotated eta
is blocked by an annotation that mentions the bound variable, so the raw
confluence theorem cannot simply be lifted back.

## Bridges to the raw calculus

`typing_erasure` and `annotation_completeness` together prove
`typing_iff_annotation`: a raw term is typable at `A` exactly when some
annotated term with that erasure is. The raw rules carry formation premises
for every result type, so annotations are reconstructed from subderivations.

`typed_normal_erasure` proves that a typed annotated normal form erases to a
raw normal form. Its main difficulty is eta: a raw eta redex in the erasure
whose annotated function still mentions the bound variable cannot occur in a
typed normal term. The proof is a strong induction on term size that
establishes, for every constructor, that a variable absent from the
erasure, the type, and newer context entries is absent from every annotation,
and that elimination forms have principal types free of that variable.

With raw confluence this gives `confluence_modulo_annotations`: two reducts
of a typed term reach terms with equal erasure. It and
`conversion_joinability_modulo_annotations` take strong normalization of
typed annotated terms as an explicit argument. No axiom is used.

## Normalization is open

Each annotated step erases to one raw step or to no step, but raw strong
normalization does not transfer:

- Steps inside annotations are invisible to the erasure. Substitution can move
  annotated terms into deeper annotations, so nesting depth is unbounded and
  no measure built from raw normalization decreases.
- A translation into raw terms that keeps annotations as junk fails: 18 of the
  31 root rules (`epi_cons`, `switch_succ`, `interp_var/pi/sig/choice`,
  `iall_var/pi/sig/choice`, `hyps_var/prod/pi/sig/choice`, `ind`,
  `close_case`, `close_ind`) build annotated nodes that raw reducts never
  contain.
- Porting the raw untyped-candidate model fails. Candidates must contain every
  neutral term, including ill-typed ones whose erasure reduces while annotated
  reduction is stuck: an eta redex blocked by an annotation that mentions the
  bound variable, or a reference eliminator applied to a closure roll (and the
  converse). The second case could be removed by extra rules that never fire on
  typed terms; the first is intrinsic.

A proof needs a typed (Kripke) logical relation over annotated terms, indexed
by contexts and stable under weakening, with raw normalization, confluence,
and eta safety as black boxes. It would be at least the size of the raw model
(about 7,000 lines). The annotations are the only reason: the raw calculus
already normalizes with untyped candidates.

## Decision

On October 11 the user decided to document these results and keep the public
calculus as it is. The unannotated calculus is consistent, normalizing,
confluent, and satisfies progress. Its only defect is that eta contraction can
lose a typing. Preservation for every computation rule in every position, with
eta retained in conversion, is proved as `named_computation_preservation`.
The named annotated layer, elaboration into this core, and migration of the
public claims were not started.

Options for resuming:

1. Build the typed model. Strong normalization then makes confluence modulo
   annotations unconditional.
2. Make annotations inert, with no reduction inside them. Normalization then
   follows directly from raw normalization and full preservation still holds,
   but confluence weakens to "modulo annotations and eta": a reducible
   annotation can block an eta contraction forever.
3. Migrate the public calculus with normalization as an explicit premise.

## Checks

```sh
make -C progress annotated-core audit-annotated-core
rocq check -silent -Q progress '' annotated.AAudit
```

The audit must print `Closed under the global context`. Syntax, binding
operations, contexts, and erasure are mechanically generated by
[generate_syntax.py](generate_syntax.py). Proofs are separate and checked by
Rocq; regenerating syntax does not generate proofs or trust an external solver.
