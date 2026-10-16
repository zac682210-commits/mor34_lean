# Next obligation: actual parity cells, not an assumed affine model

This is a development plan, not a proved theorem.

The remaining structural step is paper Lemma 5. The current componentCountMap is a real linear map on the actual item coordinates. Component labels are quotients by finite paths in the actual exchange graph. No component partition or kernel equality is supplied as an input hypothesis.

## Proposed proof split

1. Prove a generic finite-prefix sum identity. For bounded counts low <= z <= high, assume only that the unit component label of every position low_j <= u < high_j equals a fixed slope vector s_j. Then prove

   A(pointVector(prefixSet z)) = A(pointVector(prefixSet low)) + sum_j ((z_j : Real) - (low_j : Real)) * s_j.

   This is a generic helper, not the paper result. Its label-constancy hypothesis must subsequently be proved for each actual parity cell.

2. Package the right side as an AffineMap from (Fin q -> Real) to the real component-coordinate space. Prove the map agrees at the natural count embedding; do not replace the claimed map by an arbitrary function on a finite set.

3. For each nonempty full parity class, obtain coordinate extrema l_j and h_j from actual bounded feasible tight counts. The profiles witnessing different coordinates may be different; the existing interiorExchange theorem permits this.

4. Define the three coordinate alternatives exactly as in the paper: z_j = l_j; l_j+2 <= z_j <= h_j-2; z_j = h_j. Full parity, feasibility and candidate equality remain imposed. If l_j=h_j retain only one endpoint alternative; discard empty middle intervals.

5. For a middle coordinate, use parity_interior_connected and componentLabel_eq_iff_class_connected to prove label constancy. Lean positions l_j+1 through h_j-2 are in one component; every item whose prefix status can vary between middle counts lies inside this range. Endpoint coordinates are fixed and may use zero slope.

6. Instantiate the affine helper and prove the cover by at most 2^q * 3^q = 6^q cells. Count the cells separately from proving affinity; a helper with assumed label constancy is insufficient to close Lemma 5.

## Subsequent obligations

- Tight-point augmented span identity using an affine basis in each nonempty cell and adjacent exchange directions.
- Exact rank over Q versus R and nonempty affine dimension versus augmented rank minus one.
- Correctness and witness extraction for an explicit recognition procedure.
- The fixed-dimensional ILP running-time theorem and Frank-Tardos compression have not been formalized. A structural Lean proof must not be described as a checked FPT complexity theorem.

## Current implementation choices to preserve

Keep the frozen Model/Targets/PaperInterface definitions unchanged. Tightness is feasibility plus candidate equality, not an extra assumption of validity. Zero candidate coefficients and tied weights remain permitted. All geometric spaces use Real. Natural-number counts represent bounded nonnegative integer counts. Empty-face dimension -1 still needs separate algorithm-level handling.
