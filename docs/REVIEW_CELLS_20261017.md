# Statement correspondence: affine cells and augmented span

Same-session manual review, not independent review. Compiler acceptance and the exact checked revision are recorded separately in ACCEPTANCE.json.

## Lemma 5

`ParityExtrema` stores coordinate extrema and actual tight feasible witness profiles in the same full parity class. Existence is proved using the finite type of bounded profiles, not postulated. Different coordinates may have different witness profiles, as in the manuscript.

`CellCondition` has the three manuscript alternatives: the low endpoint, the middle interval [low+2,high-2], and the high endpoint. The high alternative additionally requires low<high. Thus coincident endpoints are represented only by the low alternative. Empty middle alternatives contain no counts. Full parity, feasibility, boundedness and candidate equality are retained in `parityCellSet`.

`parity_cell_cover`, `cellCondition_unique`, `tight_has_parity`, and `cell_index_card` provide the cover, uniqueness within a parity class, existence of a full parity label, and 6^q index bound. Feasible points have only one full parity label by their remainders modulo two. No singleton extremum vector is assumed jointly feasible.

`actual_cell_slopes` invokes the proved interior exchange connectivity theorem on the actual extremal witness profiles. Every zero-based item position that changes between two middle counts lies in the forced component. `prefix_sum_increment` then supplies the exact difference of prefix sums. `actual_cell_affine` produces an `AffineMap` on the whole real count space, whose equality to the component-count image is proved on the actual feasible cell. The equality is not an input hypothesis.

## Theorem 8, structural span

`adjacentDirectionSpan_eq_exchange` decomposes every exchange direction along its adjacent interval. This proves that the retained adjacent directions span the full kernel; it does not silently retain all non-adjacent edges.

`CellBasisSelection` is a precise output contract for the cell-basis subroutine. For each nonempty parity class it selects one actual set of coordinate extrema, then a finite set of feasible counts in every cell whose real count embeddings span that cell. Affine independence is not required by this contract; a small affine generating set suffices for the span identity. It does not assume the desired item-vector span equality. `selectedPoints_quotient_spans` proves that equality in the quotient using the affine-cell theorem and the prefix image identity.

`augmented_span_lift` adds the kernel directions back to the quotient. `selected_augmented_span` instantiates it for actual tight binary points and actual adjacent exchange directions. The formulation uses a sum of submodules: the span of retained rows (1,p(z)) plus the mapped adjacent direction span (0,e_u-e_v). This is exactly the span of the union of those row families by the standard span-union and map-span identities.

The selection contract is not vacuous. `finite_count_affine_basis` uses Mathlib's existence of an affinely independent spanning subset in a finite-dimensional space, pulls it back through the injective count embedding, and proves the q+1 cardinal bound. `small_cellBasisSelection_exists` and `small_selected_span` then give an unconditional existence result. The small-set theorem exposes containment, spanning and the cardinal bound, not affine independence; it is not the full paper Lemma 7 algorithm. `selectionFinset_coe` and `selectionFinset_card` identify the retained finite counts and bound their total by (q+1)6^q.

This is a classical existence proof. It does not implement the integer-programming oracle, prove the O(q^2) oracle bound, or certify executable code for finding the basis.

## Dimension and scalar conversion

`augmentedSpan_anchor` writes a nonempty augmented span as the sum of one anchor line and the zero-augmented direction space. `augment_anchor_disjoint` uses the first coordinate to prove this sum direct. `augmentedSpan_finrank` therefore gives augmented rank = affine dimension + 1. The nonempty assumption is explicit; the empty-face convention -1 remains an algorithm-level obligation.

`RankScalar` uses Mathlib's transvection diagonalization to preserve square-matrix rank under a field embedding. The rectangular rational/real case reduces to a square Gram matrix, using the established ordered-field rank identity. This avoids treating an arbitrary injective rational-linear map as preserving real linear independence, which would be false.

## Concrete retained matrix

`RetainedRowIndex` is the finite disjoint union of retained count profiles and actual adjacent exchange edges. `retainedMatrix` has integer entries and columns indexed by `Option (Item m)`, with `none` representing the augmented coordinate. Prefix rows are (1,p(z)); exchange rows are (0,e_u-e_v).

`retained_row_cast` identifies these coordinates with the real product-space rows through `LinearEquiv.piOptionEquivProd`. `retained_row_span` proves equality of their span with the retained-prefix span plus the adjacent direction span. `retained_matrix_real_rank` uses the standard row-space characterization of matrix rank and the coordinate linear equivalence. `retained_matrix_rational_rank` combines the scalar bridge, structural span theorem and augmented dimension theorem. The matrix representation is therefore connected to the actual geometric theorem, rather than passed in through an assumed row-span equality.

`adjacentEdge_card` bounds adjacent exchange rows by the number n of items using the injective map from an adjacent edge to its left endpoint. `small_retained_matrix` combines this with the prefix bound, producing a finite integer matrix with at most n+(q+1)6^q rows and n+1 columns, and the correct rational rank. This is a slightly looser row bound than n-q+(q+1)6^q, sufficient for the manuscript's asymptotic matrix-size bound. It does not establish the time to construct the selected rows.

## Boundaries

All geometry remains over Real and uses the frozen binary knapsack model. Rational-to-real matrix rank is a separate bridge. None of this proves the fixed-dimensional ILP runtime theorem, Frank–Tardos compression, a certified rational elimination implementation, or the full executable recognition procedure. A theorem count is not a completion percentage.

## Edge-case review

- Zero-width middle intervals have one possible count and need no changing item slope. Empty middle intervals are harmless empty cells.
- The affine helper may use a base prefix that is not tight; no tightness of that base is assumed or needed. Equality is asserted only for feasible tight counts in the cell.
- Full count parity, rather than parity in one coordinate, is passed to the interior-pairing theorem.
- The global basis selection chooses one extrema record per nonempty parity class. Proof irrelevance makes the nonemptiness witness immaterial in the retained finite union.
- The factor (q+1)6^q bounds retained count profiles. Images can coincide, so it is also an upper bound on retained binary prefixes.
- The augmented-span theorem includes the first coordinate. It therefore controls affine combinations, not merely a linear span of unaugmented points.
- The nonempty affine-dimension identity has an explicit nonemptiness hypothesis. Empty-face dimension -1 is not represented by the natural-number finrank.
