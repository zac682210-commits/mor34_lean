# MOR34: retained selection execution and cost composition

This checkpoint continues the user-authorized scope: formalize the new proofs and
applications, using established ILP, rank, arithmetic, sorting and FT results as
explicit local interfaces. It does not claim a compiled-machine runtime theorem.

## Concrete advance

The selection phase now has one charged execution, rather than only an external
query-count estimate. It enumerates the parity assignments, performs each support
query once, retains the coordinate extrema tables, enumerates the cell modes,
executes each cell basis search, serializes the small bases and retains the output
list. The branch taken and the charged calls use the same retained values.

`chargedDenseSelection_value` identifies that list's finite set with the previous
computed selection. `chargedDenseSelection_points` proves boundedness and
tightness of every returned point. `chargedDenseSelection_span` transports the
already proved augmented-span theorem to this actual returned list. No change
has been made to Model.lean, Targets.lean or PaperInterface.lean.

The retained list, even before deduplication, has length at most
`(q+1)*6^q`. Coordinate minima/maxima use the existing linear scan, not the
manuscript's sharper binary search; the formalized complexity statement therefore
does not claim the binary-search query formula.

## Cost statement and exact scope

Write `n = Fintype.card (Item m)` and bound input integer magnitudes by `2^L`.
`chargedDenseSelection_polynomial` bounds the cost of the retained selection by

    cellSelectionFactor q I K c * (n+L+2)^(4*c+d+5).

Here the dense solver has its established per-input size bound with exponent c;
N, D, J and E are the stored-normal coefficient read, decoding, insertion and serialization
allowances bounded by `K*(n+L+2)^d`. The exponents c and d must be independent
of q to yield the intended parameterized polynomial statement. The coefficient
may depend on q. The structure DenseCellPrimitives assumes only local solver and
finite-collection contracts, not the desired cost of the full selection phase.

Normal generation is already charged separately by builtCountForms and
builtCountFormBudget; N is not a replacement budget for normal generation.
This is an arithmetic/reference-cost phase result. It is not yet the total bit
complexity of the original-input algorithm. In particular the separate weighted
row evaluator below has not yet replaced all row evaluators in that full path.

## Additional connections

`chargedRankBasis` follows the actual early-stopping scans and repeated rank
comparisons. Its cost is derived from individual rank/input-construction and
insertion costs and the actual retained candidate list length. A concrete adapter
from the produced binary matrix to the rank callback remains to be connected.
The rank algorithm itself is an established external primitive.

Literal bounds now cover count, forced-exchange, violation and parity rows.
`weightedEvaluateRow` emits the same dense arrays as the original row evaluator,
but charges each arithmetic operation using its actual operands. The generic
subterm bound controls intermediate expressions, not only final row entries.
For rows with at most `12*(n+L+2)` nodes and the stated common literal radius,
`weightedEvaluateRow_polynomial` proves the local bound

    (12*H*170^a+5) * (n+L+2)^(3*a+1).

This uses an established arithmetic contract on operands of at most
`170*(n+L+2)^3` bits. WeightedRowApplications discharges the node-count and
literal premises for actual count, forced-exchange and violation constructors
from the original input bounds. Extra count-query literals have their explicit
radius bound. Parity transformation and replacing all evaluators in the whole
solver-call path remain to be connected.

## What still prevents acceptance of the whole time theorem

1. Connect the actual forced-exchange and validity/support branch schedule,
   retained witnesses, and selected-prefix output construction.
2. Connect concrete rank matrix emission and rank costs to the new rank loop.
3. Instantiate weighted arithmetic at every row and normal-computation caller,
   including finite-collection comparisons and storage; a row-only bound does
   not discharge these operations.
4. Compose original-input grouping/sorting, retained tables, final relabeling,
   and compression costs using local established contracts.
5. Only after a phase-complete sum with parameter-independent input exponent,
   mark the new complexity application and compressed algorithm complete.

Core new geometric proofs remain complete. `complete_FPT_complexity`,
`new_applications_complete`, `new_paper_proofs_complete` and `complete_paper`
remain false. Named declaration counts measure audit coverage, not percentage
completion. No new empirical estimate is inferred from those counts.

## Verification

Accepted source: `cc1e47944a0001ed035ddae7c5a062c9887bc439`; run: `39137807454`.
All nine commands exited zero; all 977 named declarations passed the allowlist
audit; 15 runtime smoke checks passed. The 67 added named theorems are registered
in both Check.lean and the audit list. All 204 source/configuration blobs match
the remote source tree. The dependency manifest and artifact SHA-256 match.
Details are in `selection_verified_metadata.json`,
`source_hashes_selection_20261018.json` and ACCEPTANCE.json. Failed intermediate runs are not acceptance evidence. All checks
are from this session and GitHub Actions; no independent external replay is claimed.

The reference execution is part of the mathematical algorithm model. Kernel
verification of its value/cost equations does not certify Lean compiler
optimizations or the machine runtime of proof-erasure and retained closures.
