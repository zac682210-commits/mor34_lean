> Scope update, 2026-10-18: the user now requests only newly contributed proofs. See `SCOPE_NEW_PROOFS_20261018.md` and `NEXT_NEW_PROOFS_20261018.md`. Requirements below to reimplement established algorithms or verify compiler execution costs are historical and no longer prerequisites.

# Remaining operational cost bridge

This is a specification for the next proof block, not a proved runtime theorem.
The current source has correctness and several mathematical call/bit bounds.
It does not yet connect those bounds to a complete operational semantics.

Let n be the item count, q the number of coefficient classes including zero,
d=q+1, N=max(1,max_j m_j), and L the original binary input length. Bounds
below refer to generated query data or explicitly named charge functions.

## Existing components and missing connections

| Phase | Established component | Required operational bridge |
| --- | --- | --- |
| Raw grouping/sorting | `normalizeRawExecutable`, coefficient and item transport, q parameter bound | Charge ordered finite-set construction, fiber enumeration, sorting, inverse lookup and relabeling under one input representation |
| Validity/support | Correct invalid/empty/supported branch, at most 2^q support checks | Include initial validity solver evaluation supplied in `RowPrimitives`; relate actual executable parity enumeration to the trace |
| Extrema | Coordinate scan correctness; aggregate charge at most 2(n+q)2^q | Trace stored lower/upper witnesses and table lookup; avoid counting a call once merely because two expressions are mathematically equal |
| Cell bases | At most 3^q modes per parity and q+1 search states; at most 2(q+1)^2 scalar queries per cell | Instrument each state with its actual form-generation and solver-query trace; prove result projection equals the existing definition |
| Normal generation | At most (d+1)d^(2d) candidates when retained row count is at most d; finite Laplace determinant; coefficient/product/partial-sum bits | Charge key enumeration, column injectivity, determinant subcalls, d-by-d materialization and all-row annihilation tests, including rejected keys |
| Returned tight points | Family cardinality at most (q+1)6^q+2n; all points tight and span proved | Charge finite union/deduplication, prefix construction and edge witnesses; cardinality does not count all repeated edge-solver invocations |
| Affine basis | Exact rank-based extraction and correct cardinality; abstract bound 2(n+1) times returned-family size | Transfer bound to `orderedBinarySets`; count augmented matrix construction and specify polynomial exact-rank cost |
| Output | Original-coordinate tight affine basis, dimension and facet correctness | Charge coordinate remapping, bit output and serialization |

The edge implementation deserves a small explicit trace: constructing
`computedEdges` calls the forced solver; extracting a witness calls it again;
constructing the swapped witness can call it once more. Separate images may
also reconstruct the edge set. The established bound on distinct adjacent
pairs (at most n) is not a proof of exactly n primitive invocations. A constant
multiple remains suitable for an FPT bound, but must be derived from the
chosen evaluator or avoided by storing witnesses once.

## First tractable next theorem

Instrument the one-dimensional descending scan with a result and a query
trace. Prove (i) its result projection equals `descendingSearch`; (ii) trace
length equals the existing `descendingSearchCalls`; (iii) every trace query is
one of the actual threshold queries. Lift this to the explicit finite table
construction for the 2q extrema witnesses. This will give an operationally
meaningful solver-call bound for one full phase without inventing a total
runtime definition equal to the desired bound.

Use a declared call-by-value cost semantics or an instrumented algorithm with
a proved projection theorem. Pure extensional equality to a Lean function is
not sufficient to establish compiler-level asymptotic cost. A theorem about
an instrumented reference algorithm should be labeled as such; it need not
claim a verified Lean backend cost model.

## Completion criterion for the oracle-relative FPT result

Specify costs for fixed-dimensional integer feasibility (dimension q+O(1),
actual encoded row bit length) and rational rank of the final binary matrix.
Combine the verified traces and bit bounds into f(q) times a fixed-degree
polynomial in L. The polynomial degree must not depend on q. Generic small
normal enumeration is allowed inside f(q); minor enumeration of the final
n-column rank matrix is not.

The current scanning extrema introduce a polynomial n factor. An FPT theorem
for this implementation can therefore be valid without reproducing the
manuscript's sharper logarithmic number of extrema queries. State which bound
is proved. Implementing ILP, exact rank and coefficient compression from their
foundations is a separate undertaking, not a prerequisite for clearly stated
solver-relative correctness.
