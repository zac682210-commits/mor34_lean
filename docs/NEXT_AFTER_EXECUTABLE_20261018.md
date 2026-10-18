# Resume after executable original-input checkpoint

Read ACCEPTANCE.json, session_executable_20261018.json, executable_verified_metadata.json and REVIEW_EXECUTABLE_20261018.md first. Final successful CI and matching source/artifact identities are authoritative. Preserve older checkpoints and frozen Model/Targets/PaperInterface. Work on codex/mor34-formalization, no merge/publication. No bypass of local Lean execution restrictions; compile on GitHub Actions.

## Do not redo these completed components

- ExecutableMatrixNormals: finite rank/row-map/column-map enumeration, integer rejection tests, finite Laplace determinant, first successful Option extraction. Sound and complete for arbitrary finite matrices, including rank zero and no rows/columns.
- OrderedCounts and ExecutableCountForms: deterministic finite count enumeration, exact augmented-row space description, q+1 forms, uniform magnitude bounds.
- ComputedCellPipeline and ComputedSearchPayload: the actual computed family in all cell searches; query-call and dense row-payload contracts at every recursive state.
- NormalSearchCost: per-invocation candidate count under s<=d, actual-state cardinality invariant, candidate-call charge along the q+1-step basis search.
- NormalCheckIntermediates: coefficient/product/partial-sum magnitude and magnitude-bit bounds, also for rejected candidates.
- OrderedBinarySets, ExecutableReturnedSets and ExecutableRecognitionBranches: computable returned family, deterministic enumeration, finite support parity enumeration and correct invalid/empty/supported branching.
- ExecutableNormalizedPipeline: computable basis extraction and complete normalized output contract relative to specified ILP/rank primitives. Dimension is obtained as basis.card-1; facet flag is basis.card=n. Signed empty-face dimension is separately proved.
- ExecutableNormalization: computed raw coefficient classes and item fibers via Finset.orderIsoOfFin, then Tuple.sort within classes. No Fintype.equivFin choice remains in this path. GroupedSorting's sortItems/sortGrouped are now ordinary computable defs; their mathematical bodies and all frozen targets are unchanged.
- ExecutableRawPipeline.runExecutable plus executable_original_input_output_contract: original-coordinate output after the actual computed normalization. The old classical wrappers remain historical and must not be mistaken for the current path.

## Next concrete obligation: an explicit operational cost model

Read COST_BRIDGE_OBLIGATIONS_20261018.md for the phase-by-phase bridge and a concrete first trace theorem.

The candidate-charge functions and earlier oracle-call recurrences are mathematical accounting models. They do not automatically describe every callback invocation in compiled Lean. Function-valued extrema and coefficient vectors can be recomputed on access unless materialized. computedCountForms now binds its matrix search result before mapping entries. Candidate normal coefficients are materialized by nested materializeFin tables before annihilation checks. Searched lower/upper witness coordinates are also materialized by storedParityExtrema before mode enumeration, and the stored structure is proved equal to the original extrema. Other repeated access and exact storage costs still need review.

The current implementation materializes searched lower/upper witnesses and normal coefficient tables, and derives endpoints from the stored witnesses. The corresponding semantic equality proofs are complete. Before claiming compiled cost, specify the operational semantics of those constructions. FiniteTable.materializeFin already supplies a list-backed finite-function table and proves lookup equality. It is already used for the nested candidate normal coefficient table; StoredExtrema applies this to extrema. Precisely account for list-index costs or use arrays with a verified equivalent interface. Establish exactly which calls are shared. Do not infer execution sharing from definitional equality or from a theorem named '*Calls'. Do not hide this by simply assigning the desired recurrence as a runtime definition.

Then combine:
1. parameter-only normal candidate counts and small determinant traces;
2. intermediate integer bit bounds and a specified multiplication/comparison model;
3. support, extrema, cell and edge solver queries with actual integer payloads;
4. polynomial construction/enumeration and final 0/1 rank/basis costs;
5. an explicitly stated fixed-dimensional ILP cost contract.

The current extrema routine scans thresholds. It preserves the intended FPT shape with an extra polynomial n factor, but does not prove the manuscript's sharper logarithmic query expression. The small determinant enumeration belongs only to q-sized normal matrices; do not use it to rank the final n-column matrix.

Primitive ILP/exact-rank implementations and the Frank--Tardos compression corollary remain separate. Complete paper/FPT/unconditional solver flags remain false. If the goal is an oracle-relative formal cost theorem using published algorithm foundations as explicit hypotheses, distinguish that from internalizing those algorithms.

## Checked upstream APIs

Pinned Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b, Lean 4.19.0:
- Finset.orderIsoOfFin is computable and uses sorted-list indexing.
- Tuple.sort is computable; previous project noncomputable annotations were unnecessary.
- List.Nodup.getEquiv uses idxOf, and is a usable deterministic inverse API.
- Finset.sort with a named lexicographic relation avoids conflicting pointwise order instances on functions.

## Evidence and time

The environment gate now has nine commands, including a distinct runtime smoke gate. All named project theorems must match Check.lean and audit_axioms.py; accepted transitive axioms stay propext, Quot.sound, Classical.choice, with no sorryAx/project axiom. Proof-level classical choice is permitted; executable data paths must compile as defs.

The smoke checks exercise eleven normal-generator edge cases and four raw grouping/sorting checks. They are not proofs and are not used in any theorem. Compilation verifies that the data path has executable code; it does not demonstrate performance or supply the missing primitive algorithms.

Keep actual active time separately from CI-only waiting, upload tail and inter-session gaps. Prior ledger before this round: 303.974 minutes. Do not reuse the old 2–6 hour estimate for executable generation: that scope has now changed substantially. Assess remaining cost-model work separately.
