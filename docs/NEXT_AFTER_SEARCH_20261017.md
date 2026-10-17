# Next after row-solver searches and explicit exchange rows

Read ACCEPTANCE.json and the newest session ledger first. The chronological CI attempt list includes failed drafts; only the accepted source commit is proof evidence.

## Completed changes to preserve

- Actual linear scans attain both extrema, with search-result identities. Do not revert to abstractly supplied attained extrema.
- CellCondition is encoded by exactly 3q integer inequalities, including endpoint degeneracy guards and integer middle upper endpoints.
- The explicit parity-row solver instantiates cell search and the existing retained-matrix rank theorem.
- The validity branch has its own feasible-plus-violation rows. Never add a violation inequality to a tight-equality system.
- Support and invalidity branches return original binary witnesses, and distinguish valid empty levels from invalid inequalities.
- Feasible binary points have full affine span, using the empty set and every feasible singleton.
- Forced-pair slopes and the empty-residual case are explicit rational linear rows over 2q integer variables. Exchange is equivalent to the implemented row family.
- The forced solver returns actual tight binary exchange witnesses, and a finite adjacent-pair filter has exactly the structural edge direction span.

Consult REVIEW_SEARCH_20261017.md for scope, implementation variations and assumptions. The linear extrema scan and redundant forced rows are intentional simpler implementations that preserve polynomial overhead. Neither should be described as the manuscript's exact optimized binary-search implementation.

## Next concrete target: a single returned certificate

Use ParityRowSolverSpec, ViolationSolverSpec and ForcedRowSolverSpec as explicit primitive contracts. These are correctness contracts for finite rational rows over integer variables, not project axioms. Avoid introducing a new general predicate or span oracle.

1. Package each parity's result by inspecting parityListSolver solve epsilon []. None certifies emptiness; Some supplies the nonempty proof needed by rowSearchedExtrema. Generate cell bases using the same forms and row solver. This will eliminate classical nonemptiness guards from executable control flow. The global choice of normal forms still needs a later constructive replacement.
2. ComputedMatrix now supplies the finite-edge subtype equivalence and reindexed integer rank certificate. Reuse computed_matrix_rank and computedRowIndex_card directly in the returned supported certificate; do not reprove the augmented-span result.
3. Define one certificate record for invalid, valid-empty and supported cases. In the supported case include selected count profiles, computed edges, and the actual integer matrix. An explicit exact rank oracle may be used temporarily, but label the contract and do not call it a verified rank algorithm.
4. For the paper's affine-basis output, replace each direction row with the forced solver's two tight witnesses: forcedSet and its feasible swap. Their difference is the direction. Select an independent subset of the resulting actual point family. Prove spanning, independence and correct cardinality; distinguish classical existence from the returned finite algorithm.

## Facet connection

FeasibleDimension closes full dimension for both feasiblePointSet and its explicitly defined convex hull knapsackPolytope. Next prove that for a Valid candidate the supporting equality face is the convex hull of tightPointSet. Handle the empty level separately. Then connect a formal facet predicate to dimension n-1. Do not merely define 'facet' to mean the desired matrix-rank test.

## Query and bit complexity

The verified sum for validity, support, extrema and cells is

    1 + 2*2^q + 2(n+q)2^q + 2(q+1)^2 6^q.

Adjacent edge queries contribute at most n additional calls. Enumeration/filter bookkeeping, normal construction, rank computation and the work inside each ILP call are not included. The implemented forced system has n+2q+|R|+6 rows, including harmless zero rows; do not copy the smaller unimplemented row count from the earlier planning note.

For integer normals, reuse the pivot-minor/adjugate plan in NEXT_AFTER_ENCODING_20261017.md. It needs bounded selected coordinates as a hypothesis; current quotient-basis normals have no coefficient-size bound. Formalizing a bit bound on the current arbitrarily chosen normals is invalid.

Fixed-dimensional ILP runtime and Frank–Tardos compression remain independent large foundations. The complete paper/FPT flags must stay false. Optional Corollary 6 remains open.

## Validation and timing

Continue on codex/mor34-formalization. The local Lean startup restriction is not a mathematical blocker because GitHub Actions is compiling the pinned source. Do not claim compilation from a static scan. Preserve the original model/goal files and run all eight environment-gate commands, including the full transitive axiom allowlist. Save exact successful logs and artifact/source hashes. Update the time ledger from actual active work only; earlier unlogged preparation remains unknown.

## Pinned Mathlib sources inspected for the facet bridge

These paths refer to Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, not an unverified current website version.

- `Mathlib/Analysis/Convex/Hull.lean`: `affineSpan_convexHull` directly identifies the affine span of a hull with that of its generators. This is now used by knapsackPolytope_affineSpan and knapsackPolytope_finrank.
- `Mathlib/Analysis/Convex/Exposed.lean`: `IsExposed` describes maximizers of a continuous linear functional, and `IsExposed.isExtreme` gives extremeness. A supporting face should use these geometric semantics, not a definition equating facetness to matrix rank.
- `Mathlib/Analysis/Convex/Extreme.lean`: `IsExtreme` uses the open-segment condition. The inspected `facets` name in SimplicialComplex/Basic is for simplicial-complex facets and should not be reused as if it were a polytope facet API.

A useful general intermediate statement is: if a real linear functional f satisfies f(x)<=b for x in S, then

    {x in convexHull(S) | f(x)=b} = convexHull({x in S | f(x)=b}).

One proof route is convexHull_min applied to the set of x with f(x)<=b and the additional implication f(x)=b -> x belongs to the hull of tight generators. In a convex combination, equality of the weighted average of two quantities <=b forces equality for every positive-weight term; zero weights must be treated separately. This avoids assuming the conclusion about the face, and works without relying on every feasible binary point being a vertex. It is a proposed proof route, not a checked theorem in this checkpoint.

`EdgeWitnesses.lean` now supplies the actual returned tight point and its tight swap for every computed edge, with their point-vector difference proved equal to the retained direction. The remaining point-basis task is finite union, augmented spanning and independent subset extraction, not finding the pair witnesses again.

## Original-input preprocessing

The frozen model already assumes normalized sorted coefficient classes, nonempty classes and individually feasible positive-weight items. A complete paper-level algorithm must also construct these data from the original input and prove preservation of validity, equality faces and the relevant dimension bookkeeping when removing fixed variables. The q<=K+1 relation is a theorem about that grouping, not a consequence of giving an arbitrary Model a q parameter. Keep this obligation separate from correctness of the grouped core.

## Tight-point basis: concrete proof route

Use the finite binary-set family

    image prefixSet (selectionFinset P S)
      union image computedEdgeWitness (univ : Finset (computedEdges solve))
      union image computedEdgeSwap (univ : Finset (computedEdges solve)).

Its cardinality is at most (q+1)6^q+2n by Finset.card_image_le/card_union_le, selectionFinset_card and computedEdges_card. All members are Tight: selected prefixes use S.contained through selectionFinset_coe, and the two edge images use computedEdgeWitness_pair.

For the augmented span, the easy inclusion is into augmentedSpan(tightPointSet). For the reverse inclusion, rewrite selected_augmented_span P hWF S. The selected-prefix component lies in the new family. Each generator of the adjacent-direction component is the difference between two pointAugment vectors in the family, by computedEdges_span and computedEdgeWitness_pair; the first coordinate cancels. Apply Submodule.map_span and span_le to extend this to the whole direction space. This establishes the actual finite point-family spanning statement without needing a new quotient argument.

The repository already has affineSpan_of_augment_mem in CountBasisBridge.lean and augment_mem_of_affineSpan in AugmentedSpan.lean; use these to pass from equality of augmented spans to equality of affine spans.

Pinned Mathlib `exists_affineIndependent` (LinearAlgebra/AffineSpace/Independent.lean) states exactly: for a set s there is t subset s with affineSpan(t)=affineSpan(s) and AffineIndependent on t. For a finite returned family, t is finite too. This closes classical basis existence with actual returned tight points. It does not implement independent-row extraction or prove its bit complexity. If claiming an algorithmic basis output, use exact rational rank/elimination on the returned augmented 0/1 rows and prove its selection contract instead of hiding that step behind classical choice.

A geometric facet predicate may use the standard codimension-one-face definition: the candidate level is a nonempty convex extreme/exposed subset of the actual polytope, with affine dimension one less than that polytope. This is distinct from defining facetness by the computed matrix rank. If instead using maximal proper faces as the definition, the equivalence to codimension one needs a separate finite-polytope theorem; it should not be assumed for arbitrary convex sets. State which standard convention is used before proving the recognition bridge.
