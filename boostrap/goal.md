# PomPom bootstrap goal

- [ ] Stop goal: check the complete `libs/` folder with the PomPom bootstrap implementation, run its tests, and check the fuzzy-false tests; finish only when the evidence shows the bootstrap works.
- [ ] Implement the bootstrap in PomPom itself under `boostrap/`.
- [ ] Use `libs/string.pom` for string operations instead of reimplementing strings locally.
- [ ] Split the implementation into focused libraries; add as many libraries as clarity and dependency structure require.
- [ ] Ensure every recursive definition is expressed through `accessibility_less` and/or `recur`, so all bootstrap recursion is well-founded.
- [ ] Preserve the semantics of the existing implementation; adaptations may change structure but not behavior.
- [ ] Insert small proofs throughout the implementation to check invariants and semantics while building it.
- [ ] Preserve unrelated pre-existing worktree changes; current inspection found modified and untracked files in the Haskell implementation and `libs/`.
- [x] Created the explicit persistent goal and this engineering log before implementation work. Motivation: make the acceptance criteria and constraints auditable from the start.
- [ ] Map the current parser, checker, CLI, library dependency order, test commands, and fuzzy-false behavior before choosing the bootstrap module boundaries.
- [ ] Record each discovered bug or missing feature here as a separate unchecked item until fixed and verified.
- [ ] Agent coordination: no sub-agent used initially; direct inspection keeps ownership clear. If one is used later, its task and the review of all its work will be logged here.
- [x] Inspected the repository shape and current worktree before editing implementation files. Motivation: the existing modified/untracked string, accessibility, parser, checker, and CLI work is part of the user's state and must be preserved.
- [ ] Discovery: the native README explicitly says the current Haskell checker does not enforce termination; the PomPom bootstrap must therefore add well-founded traversal structure even where the reference implementation uses ordinary Haskell recursion.
- [ ] Discovery: the present command loads transitive `.pom` imports, reverses the accumulated definition groups, and calls the Haskell `typeCheck`; reproduce this observable import/check order in the bootstrap driver.
