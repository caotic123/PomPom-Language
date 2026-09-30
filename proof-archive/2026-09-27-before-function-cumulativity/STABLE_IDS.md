# Stable bindings and alpha-equivalent terms

The active Rocq model uses two distinct kinds of numeric identity:

- A **binding ID** names a variable. A context is a finite map from binding
  IDs to types. Extending the map never changes existing IDs or stored types.
- A **term ID** names a representative in a particular interning table.
  Alpha-equivalent terms reuse the representative's ID. New classes receive
  consecutive IDs. There is no hashing.

Types use the same term syntax: dependent types can refer to ordinary term
bindings, and a type expression can itself be a variable or application.
An ID is meaningful in its own namespace and table; it is not a global
number shared across independently created tables.

## Bindings

`TPi x A B`, `TSigma x A B`, and `TLam x b` record their binder explicitly.
`TVar x` refers to that ID, rather than a distance from the most recent
binder. For example, extending the context containing `10 : Type` with
`20 : TVar 10` preserves the stored type `TVar 10` exactly.

`subst u x t` substitutes for the free binding ID `x`. It leaves other
free IDs unchanged and respects shadowing. If a binder would capture a
free variable of `u`, only that binder and its bound occurrences receive a
fresh ID. No lifting operation is needed.

## Alpha setoid and interning

The intended equality of terms is alpha-equivalence, registered as a Rocq
setoid. This is distinct from Rocq's structural equality of the raw syntax
and from beta reduction or the calculus's broader conversion relation.

`alpha_eqb_in xs ys t u` compares the two original terms directly, carrying
two lists of corresponding enclosing binders, nearest first. At a lambda,
it extends both lists with the binder IDs. Pi/Sigma domains use the current
lists and their codomains use the extended lists. Variables must match the
same enclosing binder, or have equal free IDs. Constructor shapes, universe
levels, and labels must also agree. There are no intermediate comparison
keys, numeric constructor tags, or hashes.

`alpha_eqb` starts with two empty binder contexts. Reflexivity, symmetry,
and transitivity are proved for the comparison, supplying the term setoid.

The interning table searches representatives using this alpha comparison.
It reuses a matching ID or appends a new representative. Appending preserves
all earlier IDs. Numeric equality represents alpha equality for terms
interned in the same valid table, not beta/eta conversion.

## Migration checks

- [x] Explicit binder IDs and finite-map contexts.
- [x] Capture-avoiding substitution with stable free IDs.
- [x] Alpha setoid and sequential interning.
- [x] Core reduction, typing, elaboration, and examples use stable IDs.
- [x] Theorem statements and the existing partial proof use the new APIs.
- [x] Regression checks cover lookup, capture, alpha equality, and ID reuse.

Type correctness, weakening, and substitution remain conjectures. The
unfinished attempts are preserved in the September 26 proof archive. See
[PROOF_STATUS.md](PROOF_STATUS.md) for the current checked results.

Run `make -C progress check-bindings` to check the implemented modules and
36 binding/example checks. The full `open-signatures` target also builds;
`audit-open-signatures` reports the remaining assumptions explicitly.
