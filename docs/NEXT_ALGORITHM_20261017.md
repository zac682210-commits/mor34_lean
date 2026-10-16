# Next stage after the structural checkpoint

Acceptance.json and source_map.json identify exactly which declarations have compiled and passed the axiom allowlist. This plan does not certify any unimplemented part.

## What the structural theorem establishes

`small_selected_dimension` produces at most (q+1)6^q retained prefix profiles. The span of their augmented binary points together with the adjacent exchange rows has dimension dim(aff(T))+1 for a nonempty tight set. Selection is classical and noncomputable. `integer_matrix_rank` separately proves that any finite integer row matrix has the same rank after rational and real casts.

## Algorithm correctness still required

1. Encode the convex-prefix epigraph ILP and prove equivalence to bounded feasible count profiles, including arbitrary rational linear restrictions and parity substitution. The current prefix-minimality theorem supplies a prerequisite, not this encoding theorem.
2. Encode and verify the adjacent-edge minimum-cost realization used by the paper's oracle. Current adjacency predicates quantify actual tight witnesses; they are not executable tests.
3. Formalize the affine-basis procedure with integer-feasibility calls. `finite_count_affine_basis` proves existence of a small generating set, not a query algorithm or its bit complexity. Preserve the original restricted integer count sets.
4. Assemble an explicit recognition procedure, handling invalid inequalities and empty faces before the nonempty dimension branch. Keep feasibility distinct from validity; do not assume validity inside Tight.
5. Use the concrete `retainedMatrix` and its rational-rank theorem when connecting the procedure to the returned dimension. Matrix packing and the scalar bridge are provided; a certified executable rational elimination implementation is still separate.
6. For an output basis of actual tight binary points, replace each adjacent direction by its tight witness and its swapped point; prove preservation of the augmented row span and verify the subsequent independent-row extraction.

## Complexity boundary

The fixed-dimensional ILP runtime theorem and Frank–Tardos compression remain external mathematical foundations not formalized in this repository. Do not add them as project axioms and call the complete FPT theorem verified. An oracle-relative correctness theorem is a useful intermediate result if its oracle contracts and unresolved runtime assumptions are explicit.

## Preservation rules

Do not change Model.lean, Targets.lean, or PaperInterface.lean to facilitate later proofs. Keep zero coefficients, tied within-class weights, original tightness, full parity, empty-cell handling, actual exchange connectivity, and the real/rational distinction. Report actual active work time; earlier unlogged preparation remains unknown.

## Concrete first target: the epigraph equivalence

Keep the integer arithmetic of Model.lean. For one sorted nonempty class of size m, define F(z) as the sum of weights at indices u<z. For a breakpoint t<m, define

    L_t(z) = F(t) + w_t * ((z : Int) - t).

Here w_t is the zero-based weight, so this is the paper's slope w_(t+1). For each bounded z, prove L_t(z)<=F(z):

- If t<=z, split classPrefix(z) into classPrefix(t) and their set difference. Every added weight is at least w_t; the difference has z-t elements.
- If z<=t, split classPrefix(t) at z. Every removed weight is at most w_t; the difference has t-z elements.

Then prove a supporting equality exists. For z<m use t=z. For z=m use t=m-1 and the single-item prefix increment. This includes z=0 and avoids an undefined slope at m.

These facts give, for integer y and bounded z,

    F(z)<=y  iff  forall t<m, L_t(z)<=y.

Applying this in every class yields the exact existential epigraph statement:

    sum_j F_j(z_j)<=capacity
      iff exists y : Fin q -> Int,
        (forall j t, L_(j,t)(z_j)<=y_j) and sum_j y_j<=capacity.

The forward witness is y_j=F_j(z_j); the reverse implication sums the coordinate lower bounds. Candidate equality and extra rational linear restrictions can be conjoined unchanged. Parity substitution is a separate bijection between bounded natural counts with remainder epsilon and integer variables v satisfying z=2v+epsilon; explicit bounds are needed when crossing Nat/Int.

This route proves the exact oracle formulation before attempting its runtime or implementing a solver. It does not require an additional mathematical conjecture, but all finite-sum, endpoint and cast details still need Lean proofs.

## Acceptance gates for the next implementation

1. **Exact encoding.** A two-way theorem for the integer prefix epigraph, with endpoint support at the last item and the bounded Nat/Int conversion. This is a statement about the original feasible counts, without a solver assumption.
2. **Oracle-relative procedure.** Represent a feasibility oracle by a function and an explicit soundness/completeness contract; the contract must specify a witness on success and emptiness on failure. Use it to implement the growing affine basis. Prove termination by a strictly increasing rational span dimension bounded by q, and count at most 2q tests per stage. Do not replace the restricted set by its real relaxation.
3. **Recognition assembly.** Prove actual adjacent-edge tests, extrema and cell calls supply the checked matrix construction. Handle validity and empty faces before using the nonempty augmented-rank formula. Return actual tight points if an affine-basis output is claimed.
4. **Costed theorem.** Only after the procedure and encodings are fixed, attach operation and bit-length bounds. A finite enumeration algorithm proves decidability but cannot stand in for a fixed-parameter time proof. Any external algorithm theorem still assumed at this stage must be explicit in the theorem statement and report.

There are two distinct deliverables: a kernel-checked oracle-relative correctness theorem, and an end-to-end executable FPT algorithm with the external integer-programming foundations formalized. Completing the first must not be reported as completing the second. The next estimate should be revised after the exact encoding and first verified procedure compile, rather than extrapolated from the number of declarations.
