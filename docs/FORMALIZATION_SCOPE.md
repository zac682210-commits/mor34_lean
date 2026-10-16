# MOR34 formalization scope

Reference: Zhiyan Lin, *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges*, v0.1, October 13, 2026. The unchanged reference PDF hash appears in `source_map.json`.

## Mathematical contract and indexing

`Item m` is the disjoint union of the coefficient classes. A finite set of items represents a binary point. Natural count coordinates encode the paper's bounded nonnegative integer coordinates. Lean positions are zero-based: paper position k corresponds to Lean value k-1. Both the paper's cut r and Lean's cut r separate the first r positions from the remainder; Lean's adjacent pair is (r-1,r). Thus the paper inequalities z_j+2 <= r <= w_j-2 are unchanged.

`Tight P S` means feasible and at equality. It does not assume validity of the inequality. `WellFormed` records positive sorted weights and the other input hypotheses, and contains no parity, exchange, rank or algorithm conclusion. Zero candidate coefficients and equal weights are allowed. Full coordinatewise parity is required, not only parity in the selected class. The other coordinates of z and w need not have a common ordering.

## Verified proof chain

1. `balancedSplit` and the more general `split_prescribed` extend a prescribed subset inside the complement of the opposite prescribed subset, using Mathlib's existing finite-set extension lemma.
2. `class_pair` partitions the symmetric difference in each class into equal halves, restoring common selected items to both outputs.
3. `class_pair_cross` forces two selected and two omitted positions around a specified interior cut. Its construction requires exactly the two-unit margins in the target.
4. `pairingAtCut` assembles the per-class sets and proves the complete frozen `PairingAtCutGoal`: coordinatewise repartition, balanced class counts, and an inversion across the cut in each output.
5. `repartition_sum` proves weighted-sum conservation. `candidateValue_counts` expresses candidate value by class counts. `one_tight_of_repartition` proves that at least one output is feasible and at equality; it does not incorrectly require both to be feasible.
6. `tight_swap` and `intervalExchange` prove the four membership cases of paper Lemma 2's edge assertion by feasibility-preserving replacements.
7. `adjacent_of_crosses` narrows a crossing exchange to the adjacent pair. `interiorExchange` combines this with the feasible output and proves the exact frozen `InteriorExchangeGoal`.

All 24 named theorem dependencies were checked in GitHub Actions run 38919230112 on commit 8ac25e0cc6a5c28693b4f05c34e4bfff222896aa. No target definitions were weakened in this stage. The original frozen interface files retain their previous hashes. Only standard Lean axioms propext, Classical.choice, and Quot.sound occur.

## Outstanding scope

The adjacent-cut assertion is the main assertion of paper Lemma 4; its consequent statement about all interior items lying in one graph component is not yet encoded. Similarly, the component-interval consequences of Lemma 2 remain open despite its proved edge assertion.

Next: encode connected components and prove the interval consequences, then prefix sorting and the exchange quotient. The substantive remaining chain is E = ker A, the affine dimension identity, affine behavior on the parity cells, and the tight-point span identity. Integer-programming and compression complexity require separately specified algorithms, encoding and cost bounds. These are not consequences certified by the current build.

Successful compilation proves the submitted Lean statements; correspondence to the full paper still requires review. No independent formal audit or main-theorem completion is claimed.
