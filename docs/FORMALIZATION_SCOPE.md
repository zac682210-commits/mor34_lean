> Scope update, 2026-10-18: the user now requests only newly contributed proofs. See `SCOPE_NEW_PROOFS_20261018.md` and `NEXT_NEW_PROOFS_20261018.md`. Requirements below to reimplement established algorithms or verify compiler execution costs are historical and no longer prerequisites.

# MOR34 formalization scope

Reference: Zhiyan Lin, *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges*, v0.1, October 13, 2026. The unchanged reference PDF hash appears in `source_map.json`.

## Mathematical contract and indexing

`Item m` is the disjoint union of the coefficient classes. A finite set of items represents a binary point. Natural count coordinates encode the paper's bounded nonnegative integer coordinates. Lean positions are zero-based: paper position k corresponds to Lean value k-1. Both the paper's cut r and Lean's cut r separate the first r positions from the remainder; Lean's adjacent pair is (r-1,r). Thus the paper inequalities z_j+2 <= r <= w_j-2 are unchanged.

`Tight P S` means feasible and at equality. It does not assume validity of the inequality. `WellFormed` records positive sorted weights and the other input hypotheses, and contains no parity, exchange, rank or algorithm conclusion. Zero candidate coefficients and equal weights are allowed. Full coordinatewise parity is required, not only parity in the selected class. The other coordinates of z and w need not have a common ordering.

## First verified proof chain (earlier October 16 checkpoint)

1. `balancedSplit` and the more general `split_prescribed` extend a prescribed subset inside the complement of the opposite prescribed subset, using Mathlib's existing finite-set extension lemma.
2. `class_pair` partitions the symmetric difference in each class into equal halves, restoring common selected items to both outputs.
3. `class_pair_cross` forces two selected and two omitted positions around a specified interior cut. Its construction requires exactly the two-unit margins in the target.
4. `pairingAtCut` assembles the per-class sets and proves the complete frozen `PairingAtCutGoal`: coordinatewise repartition, balanced class counts, and an inversion across the cut in each output.
5. `repartition_sum` proves weighted-sum conservation. `candidateValue_counts` expresses candidate value by class counts. `one_tight_of_repartition` proves that at least one output is feasible and at equality; it does not incorrectly require both to be feasible.
6. `tight_swap` and `intervalExchange` prove the four membership cases of paper Lemma 2's edge assertion by feasibility-preserving replacements.
7. `adjacent_of_crosses` narrows a crossing exchange to the adjacent pair. `interiorExchange` combines this with the feasible output and proves the exact frozen `InteriorExchangeGoal`.

All 24 named theorem dependencies were checked in GitHub Actions run 38919230112 on commit 8ac25e0cc6a5c28693b4f05c34e4bfff222896aa. No target definitions were weakened in this stage. The original frozen interface files retain their previous hashes. Only standard Lean axioms propext, Classical.choice, and Quot.sound occur.

## Additional verified structure (October 17 checkpoint)

`Components.lean` completes the finite-path characterization by adjacent cuts and the interval-component and parity-interior consequences. `ExchangeKernel.lean` formally identifies local class connectivity with the actual global exchange quotient.

`PrefixMinimality.lean` proves the exact frozen prefix-minimality contract by the increasing enumeration of selected positions, and proves both count preservation and tight-prefix preservation.

`PartitionKernel.lean` proves the finite partition kernel identity over Real. `ExchangeKernel.lean` instantiates it with the quotient by actual exchange paths, identifies the original oriented exchange span, proves component-map surjectivity and dim E + C = n.

`TightDimension.lean` realizes finite sets as real 0/1 vectors, proves each exchange direction lies in the tight-point vector span, and applies rank-nullity on that subspace. Its dimension formula has an explicit nonempty-tight-set hypothesis, consistent with affine dimension; no assertion about empty-face dimension -1 is made here.

`PrefixQuotient.lean` proves the exact component image identity for tight points and bounded feasible tight prefixes. Together these complete the mathematical statements of paper Lemmas 2, 3 and 4 in the grouped finite-set model.

All 73 named theorem dependencies passed on commit 1ab49f5e6de4be6ad59dd31c2f34f09ebdbc6211, run 38931568115. The original model and frozen interfaces have unchanged hashes. Logs and source hashes are retained separately from earlier checkpoints.

## Current scope after the bounded-normal checkpoint

The earlier sections above are historical checkpoints. Affine cells, augmented span, rational/real rank bridge and the full normalized solver-relative output contract have since been proved. Bounded normals now describe arbitrary finite count selections and are integrated into boundedPipeline; raw grouping/sorting and discrete/dimension transport are also proved. See ACCEPTANCE.json and REVIEW_NORMALS_20261017.md for exact current coverage.

Remaining: raw output/basis/geometric-facet wrapper, executable normal generator, complete row encoding/cost model, exact rank and fixed-dimensional ILP foundations, FPT runtime and compression. Classical choices and explicit solver contracts remain. Complete paper certification is not claimed. Same-session review only.

## Current scope after the original-input checkpoint (October 18, 2026)

Full original-input output contract relative to explicitly specified ILP and rank primitives: invalid witness, signed empty-face dimension, actual face dimension, geometric facet decision and an affine basis of original tight binary points. All actual count/parity/forced/violation rows have integer coefficient bounds and dense payload bounds; recursive cell-query states satisfy the payload invariant. A concrete recursive integer determinant and exact finite pivot search are verified, including arithmetic charges along the search path and intermediate partial-sum bit bounds. Finite integer normal-candidate tests are proved sound and complete; enumeration itself remains open. Classical normalization and bounded normal-family choices remain. The concrete pivot search has not replaced the normal chooser. Full executable generation, serialization/construction costs, primitive algorithms, total FPT runtime and compression remain open.

The prior bounded-normal checkpoint above is historical. Current authority: ACCEPTANCE.json, source_map.json and REVIEW_RAW_20261018.md. Solver-relative semantics are complete; unconditional algorithm/FPT completion is not claimed.

## Executable original-input checkpoint (October 18, 2026)

Executable original-input procedure with complete output correctness relative to explicit ILP and exact-rank primitive contracts. Raw coefficient classes, item fibers and within-class sorting are computed. Finite integer normal search, support parity enumeration, returned tight-point family, deterministic binary-point ordering, rank-guided affine-basis extraction and original-coordinate relabeling are computable. Invalid witnesses, empty signed dimension, supported geometric face dimension/facet flag and tight affine basis are verified. Candidate-call charges, generated row payloads and candidate partial-sum bit bounds are proved. Normal coefficient and extrema witness tables have proved lookup/structural equality. Operational sharing/materialization costs, enumeration/construction/serialization bit costs, total cost composition, primitive implementations and compression remain open; no full FPT runtime claim.

Current authority: ACCEPTANCE.json and REVIEW_EXECUTABLE_20261018.md. Historical classical interfaces are preserved but are not the latest execution path.
