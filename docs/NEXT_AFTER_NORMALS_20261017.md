# Continue after bounded normal integration and raw normalization

Read ACCEPTANCE.json and session_normals_20261017.json first. The exact successful source and retained logs are authoritative. Preserve frozen Model, Targets and PaperInterface. Continue on codex/mor34-formalization; do not merge or publish. Do not bypass the local compiler startup restriction; use GitHub Actions.

## Preferred pipeline

Use boundedPipeline and boundedCellSelection for further work. They retain the normalized output contract while using boundedCountForms at every recursive count search. Legacy normalizedPipeline is still proved but does not acquire the new coefficient bound automatically.

ColumnNormals, ColumnNormalBounds, BoundedMatrixNormals, BoundedCountForms and BoundedNormalFamily close the previous bounded-normal connection. The original-column formula avoids column-complement reindexing. There are exactly q+1 equations, possibly zero, not a claimed independent basis of normals. The coefficient bound includes constants and permits dependent input count sets.

NormalQueryBounds covers both strict sides and the parity substitution. CountSearchFormsBounded tracks all intermediate recursive states. The bit bound is for magnitude only; add the sign bit in an encoding-length model.

## Small executable normal generator still separate

PivotSearch now enumerates all Fin r -> Fin d maps, checks injectivity and nonzero supplied determinant, and proves soundness/completeness with <=d^r attempts. It does not replace the classical independent-row and pivot choices inside boundedCountForms. Do not label the generator fully executable.

To replace those choices, either:

1. carry actual search-state row independence and enumerate only the full-row-rank pivot, or
2. enumerate original row/column minors and choose maximal nonzero size for arbitrary B.

The first route uses the existing basis-search independence invariant. In reachable states both row count and column count are <=q+1, so even elementary determinant expansion is parameter-compatible. Prove the call/arithmetic count and intermediate integer sizes for an explicit determinant evaluator. Do not apply exponential minor enumeration to the final n-column rank matrix.

## Raw input normalization

GroupedSorting proves the class-wise weight permutation and all discrete predicate preservation. InputGrouping constructs a normalized Model and an item bijection from raw Fin n data under the paper hypotheses, n>0, and permits coefficient zero/tied weights. RawTransport proves feasibility, tightness, validity, preservation of the actual positive coefficient-value set, q<=K+1 and q<=n. RawGeometry transports tight binary vectors and their affine-direction dimension.

The next integration step is a raw-output wrapper, with explicit coordinate permutation of witnesses and returned basis. The signed empty-face convention is already transported by relabel_signed_dimension; boundedPipeline_raw_dimension already states the computed dimension directly in original coordinates. Transport the convex hull/equality face and geometric facet definition, then compose boundedPipeline_correct. Do not replace geometric facetness by a rank definition. The cardinality parameter must refer to raw c, using relabel_positive_values. Prove affine independence under relabelLinear for returned bases, not just spanning or dimension.

Useful pinned Mathlib APIs inspected this round:

- Data/Fin/Tuple/Sort.lean: Tuple.sort, Tuple.monotone_sort (already used).
- Logic/Equiv/Basic.lean: Equiv.sigmaSubtypeFiberEquiv (already used).
- Logic/Equiv/Defs.lean: Equiv.sigmaCongr, sigmaCongrRight.
- LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean: AffineMap.vectorSpan_image_eq_submodule_map.
- LinearAlgebra/Dimension/Finrank.lean: LinearEquiv.finrank_map_eq.

A raw normalization existence theorem is not a costed sorting implementation. Its use of Fintype.equivFin/classical choice must remain visible in the executable scope description.

For the concrete row bounds and the actual three-row-per-coordinate cell encoding, see ROW_ENCODING_PLAN_20261017.md.

## Remaining complexity foundations

- Explicit bit bounds for the complete ordinary, forced, parity and validity row systems. PrefixEncodingBounds now bounds prefix costs and ordinary/forced intercepts from the original weight bound. Finish the row-family case split and the input encoding conventions.
- Executable normal generator and finite coefficient-size invariants during its computation.
- Exact rank algorithm and fixed-dimensional ILP implementations, or clearly delimited imported contracts.
- Full time model and FPT theorem; Frank--Tardos compression remains separate.

Complete paper/algorithm/FPT flags remain false. Next-stage estimate should distinguish solver-relative semantic completion from full verified complexity foundations. Do not convert audited theorem count into a completion percentage.

## Evidence and timing

Replay the eight readiness commands and the transitive axiom allowlist. Retain the exact artifact, manifest, source tree correspondence and frozen-file hashes. Every round needs actual active time and cumulative recorded time; don't add gaps, sleeps or nominal hourly slots. Earlier unlogged preparation remains unknown. The current review is same-session only.

## Concrete raw-result transport route

Pinned API inspection also identified `LinearMap.image_convexHull` (Analysis/Convex/Hull.lean), `AffineIndependent.map'`, `AffineMap.affineIndependent_iff`, and `AffineEquiv.affineIndependent_iff` (LinearAlgebra/AffineSpace/Independent.lean). Use relabelLinear for the point map. Its injectivity transports independence; the finite subset map induces the required equivalence between the original and mapped basis index types. Prove both the point-family image identity and that the returned subset map is injective before transporting cardinals.

For raw facet geometry, define the raw feasible binary convex hull and the equality level by the raw coefficient linear functional. Establish the feasible-point image and coefficient-functional identity under relabelLinear. LinearMap.image_convexHull then transports the ambient polytope and the equality face. Either transport the extreme-subset predicate directly, or reuse the already proved general supporting-level extreme lemma on the raw linear functional. Combine convexity, nonemptiness and the affine-direction dimension identity with the SAME IsCodimensionOneFace predicate. Do not define the raw facet predicate as the desired output Boolean or rank equality.

The targeted pinned-source search did not locate a directly named IsExtreme.image theorem in Analysis/Convex. This is not evidence that none exists elsewhere; a short direct convex-combination argument or the supporting-level lemma already in the project is sufficient.

## Replacing classical normalization choices later

The raw grouping proof currently uses Fintype.equivFin. A concrete replacement can enumerate the finite image of c in the integer order using Finset.orderIsoOfFin, and enumerate each fiber by the original Fin n index order before applying Tuple.sort to its weight tuple. All comparisons are then on integers or Fin indices. This avoids introducing a generic classical enumeration as an algorithmic primitive. Preserve the already proved item-bijection specification, so the semantic transport lemmas and boundedPipeline_raw_dimension can be reused unchanged. A runtime proof for those sorting operations is still separate; computability by itself does not prove polynomial time.
