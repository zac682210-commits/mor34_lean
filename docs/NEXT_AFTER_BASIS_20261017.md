# Next after normalized output and returned point bases

Read ACCEPTANCE.json and session_basis_20261017.json first. The accepted source commit, not the latest failed draft in the attempt list, is the proof checkpoint. Preserve the original frozen model and targets.

## Completed target to preserve

The structural proof is now connected to a complete normalized-input output record, relative to the explicitly specified parity/violation/forced ILP solvers and an exact rational-rank evaluator. The supported branch returns the correct dimension, facet Boolean and a searched affine basis of actual tight binary sets. Empty faces use signed dimension -1 and invalid candidates have no face-dimension value. Normal-form generation still uses Classical.choice.

Reuse these modules and results:

- ReturnedPoints: small actual tight-point family, augmented and affine span identities.
- SupportingHull / FacetBridge: equality face equals hull of tight binary generators, is convex and extreme, and has the dimension used by the computed rank test. Facets use the standard codimension-one-face convention, not a matrix-rank definition.
- FiniteBasisSearch / BinaryPointBasis / ReturnedBasisSize: rank-guided list scan, real independence and full spanning, exact basis cardinality. Exact rank is a primitive contract, not a verified elimination implementation.
- ExecutedCells: actual optional solver answer controls empty parities; one outer test and attained extrema per parity, then the mode union. The union is proved equal to the structural selection.
- RecognitionCertificate / NormalizedPipeline / SignedDimension: complete return contract in one record, validity included in DefinesFacet.
- BasisRankCalls: at most 2(n+1)((q+1)6^q+2n) rank evaluations for extraction, excluding the cost inside each evaluation.
- ParameterCount: q<=K+1 where K counts actual distinct positive values on the normalized input's items; q<=n. Original-input preprocessing is still open.

## Immediate next mathematical target: replace normal choice

CramerBounds, BoundedPivotNormals, PivotNormalSpan and PivotNormalBits provide a bounded normal family for a GIVEN nonsingular integer pivot block A and free columns C. They prove annihilation, rational independence, complete kernel spanning, magnitude <=r!N^r, and an explicit logarithmic magnitude-bit bound. They do not select this pivot block from the count matrix and are not yet connected to FormsDescribe.

To complete that connection:

1. For a finite selected count set B, take augmented integer rows (1,z). Their entries are bounded by n+1 when the coordinates are bounded by n. Actual cell-search containment supplies this hypothesis.
2. Select independent rows and an r-column restriction giving a nonsingular r-by-r minor. Search/choose only among finite subsets of the original rows and columns, so original entry bounds are retained. Prove the full row span equals that of the selected rows.
3. Reindex columns by Fin r + Fin f with r+f=q+1 and identify the row matrix as [A C]. Transport pivotNormal back to Option(Fin q).
4. Convert the transported vectors to IntegerForm using the none coordinate as constant and the some j coordinate as coefficient. Show that their equations describe the augmented row span, not merely that they annihilate known rows. This needs the row-space/double-annihilator bridge.
5. Replace BuiltSelection's classical quotient-normal family with this bounded construction. Do not attribute the new size bound to the old arbitrarily chosen normals.
6. Use the small selected-count invariant: each queried B has at most q+1 points, and its augmented matrix has q+1 columns. Exhaustive minor/pivot enumeration here is parameter-bounded and can fit 2^{O(q log(q+1))}; polynomial Gaussian elimination is not required for this small normal-generation subroutine. Do not apply that argument to the final matrix with n+1 columns, where exhaustive minors can be exponential in n. A cost model is still needed for either implementation.

Pinned Mathlib paths consulted:

- LinearAlgebra/Matrix/Adjugate.lean: cramer_apply, mulVec_cramer.
- LinearAlgebra/Matrix/AbsoluteValue.lean: det_le.
- LinearAlgebra/Matrix/NonsingularInverse.lean: mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det.
- LinearAlgebra/Matrix/ToLin.lean: range_vecMulLinear identifies the row span.
- LinearAlgebra/Dual/Lemmas.lean: dualAnnihilator_dualCoannihilator_eq and forall_mem_dualAnnihilator_apply_eq_zero_iff.
- Data/Nat/Log.lean: le_pow_iff_clog_le and le_pow_clog.

The targeted searches in the pinned Mathlib source did not reveal a directly named nonsingular-minor extraction theorem. This is a search observation, not proof that no suitable theorem exists. Matrix transvection diagonalization exists and is already used by RankScalar, but it does not automatically preserve small entry bounds for the original pivot minor.

## Separate larger obligations

- Original-input normalization for the stated paper theorem: construct nonempty coefficient classes, sort weights inside each class, and prove preservation under the item permutation. Section 2 already assumes positive weights and feasible singletons; eliminating infeasible or fixed items is an optional extension, not a prerequisite for this theorem. ParameterCount does not replace the grouping/sorting step.
- Polynomial encoding lengths for all ordinary/forced/parity rows and constructed normals.
- Verified executable exact linear algebra and fixed-dimensional ILP, with an explicit bit-operation cost model.
- Full FPT runtime theorem and Frank–Tardos compression; optional component-count corollary remains separate.

Keep complete_paper, complete_algorithm_correctness and complete_FPT_complexity false. A more precise positive flag is normalized_output_contract_solver_relative. Do not translate a theorem count into a completion percentage or silently treat solver contracts as implementations.

## Timing and evidence

Continue on codex/mor34-formalization; no merge, release, email or submission is requested. Use GitHub Actions because the local compiler startup restriction remains unresolved. Do not bypass it. Reuse the pinned Lean 4.19.0 and dependency manifest. The environment gate prints the complete failed command log, allowing earlier independent-module errors to be seen; its eight checks and fail-closed exits are unchanged.

Record active work, excluding session gaps and pure waiting. Never replace older session ledgers. On success retain exact logs, artifact SHA256, source blob comparison and frozen-file hashes. Review changes against the source statement before marking a new scope flag.

## Refined small-matrix route found during this round

For the count-basis subroutine, B.card<=q+1 is an actual invariant, not merely an output-size bound at the end. Every insertion increases size by at most one, and fuel starts at q+1. The queried augmented row matrices thus have at most q+1 rows and exactly q+1 columns. Enumerating all row/column subsets and computing determinants by the permutation formula uses at most 2^{O(q log(q+1))} arithmetic operations, with bounded integers supplied by the determinant estimates. This is compatible with the target FPT exponent, although the operation-count proof has not yet been formalized.

An even more focused route uses the already proved linear independence of the selected augmented rows: only a full-row-rank column minor needs to be chosen. Show the columns span Q^r from row independence, select a column basis, and derive a nonzero r-by-r determinant. A finite first-success search over column subsets can then replace classical pivot choice. Empty B requires standard coordinate normal forms; a full q+1-row selection requires an empty normal list.

The generic FormsDescribe theorem currently ranges over all finite B. The actual reachable selections are small, independent, and count-bounded. Either prove a general bounded generator using finite maximal minors, or refine the oracle correctness proof to carry these invariants. Do not add the desired invariant as an unchecked global assumption. The final n-column rank computation remains a separate polynomial-time foundation.

## Refined continuation target after pivot-minor existence

When independent_rows_pivot_minor is listed in the accepted audit, nonsingular original-column minor existence is complete for independent rational rows. The remaining work is integer/count-matrix transport, an explicit finite selector if executable normal generation is required, column reindexing, and the FormsDescribe converse. See PIVOT_INTEGRATION_PLAN_20261017.md for the exact row-space reconstruction and a parameter-compatible exhaustive search cost argument. That document does not assert a checked runtime theorem.
