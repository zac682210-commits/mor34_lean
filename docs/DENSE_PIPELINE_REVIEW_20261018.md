# Dense request and arithmetic review — 18 October 2026

This checkpoint stays within the user's scope: new proofs and applications of
established primitives. It does not formalize ILP, rank, Frank–Tardos, sorting,
or the Lean backend. Acceptance is tied to the source and artifact recorded in
ACCEPTANCE.json, not to the presence of source files alone.

## What this checkpoint connects

The previous checkpoint constructed expression trees and gave local budgets.
It left an important caller obligation: a mathematical residual-weight function
was not yet an actual read from the table charged at construction time. The new
`compiledForcedRequest` retains that table and supplies it to all slope rows.
`retainedSlopeRow` reads its coefficient once, retaining it for both the output
coefficient and the intercept; its prefix uses the same stored table. The
non-slope input accesses still have an explicit primitive read budget R.

`evaluateInteger` evaluates each arithmetic node and retains its children.
`evaluateConstructedRow` materializes two integer lists and a constant. This is
proved equal to the old rational inequality. `denseParityRow` reads each old
count coefficient once and uses it for both doubling and the parity correction.
The cost list is shared. These are data transformations with checked values;
the solver is no longer asked to interpret an unevaluated expression tree.

The three request families enumerate their row indices explicitly. Completeness
and exact cardinality imply absence of duplicates. This matters for transferring
an encoding bound expressed as a finite sum: completeness alone would permit an
arbitrarily repeated list. `densePayload_of_value` proves that equality of two
integer-coefficient rational inequalities determines the actual stored integers.
Consequently, the existential old encoding bound applies to the array sent to
the solver, rather than to an unconnected smaller representation.

One `DenseRowSolverSpec` supplies soundness and completeness on the concrete
arrays. Its three adapters derive the old count/parity, forced-exchange and
violation specifications. `dense_original_input_output_contract` then gives the
original-input output contract, including dimension, validity, facet recognition
and the returned basis, using computed normalization and the same exact rank
primitive. This is solver-relative correctness, not a runtime claim.

## Exact local bounds

Write n for the number of items, q for coefficient classes, and assume q<=n.
The following are coarse reference bounds, not empirical timings.

| Quantity | Bound | Essential local premise |
|---|---|---|
| Complete forced request, including residual table and AST evaluation | `521(n+1)^3` | input scalar access R<=n+1 |
| Complete count/parity request | `2048(n+1)^4` | at most 3q+1 query rows, scalar access R<=4(n+1)^2 |
| Complete violation request | `2048(n+1)^4` | scalar access R<=4(n+1)^2 |
| Actual integer payload of each applicable request | `168(n+L+2)^4` | input magnitudes <=2^L; cell queries use their reached-state invariant |
| Payload plus explicit row/dimension headers | `180(n+L+2)^4` | same assumptions |
| One external solver call | `I[180(n+L+2)^4]^c` | its per-input size cost contract |

`denseCellRequests_cost_on_states` derives the construction-plus-solver bound at
every reached cell-search state from the existing correctness and payload
invariants. It does not assume that invariant as a final whole-program premise.
`boundedCountRequest_payload` also covers arbitrary bounded base-query lists;
empty support queries are included. The two coordinate-scan query lemmas prove
the requisite bounds for every scanned threshold, including the signed upper
query `m_j-k`. They can be substituted in `boundedCountSolver_cost`, so base and
coordinate requests need not rely on a cell-only invariant.

The local exponent c must be chosen uniformly in q when assembling an FPT
family; the local theorem for one q alone makes no such uniformity assertion.

`chargedFirstWitness` and `chargedDescendingSearch` follow the actual early-stop
path and retain the answer of each call. `chargedBasisExecution` adds explicit
finite-collection insertion charges. Its state-local cost theorem only needs
bounds on reached states, rather than on every arbitrary finite set of counts.
`chargedCellStep` retains generated normal forms and their outside queries.

## Integer operations versus bit costs

`constructionSubterm_bits` bounds every intermediate AST value, including values
that later cancel. The bound is `work*clog_2(M+2)+2` when literals are bounded by
M. It is not merely a final-output magnitude bound.

`weightedEvaluateInteger` evaluates the same expression with local charges for
reading, addition, multiplication and negation. The values are proved equal to
the original interpretation. If the established arithmetic primitives cost at
most K on the proved operand-size range, the actual evaluation charge is at most
`work*K`. `weightedEvaluateInteger_cost_of_literals` discharges all operand-size
premises using the intermediate-value theorem. The count-row literal bounds are
also instantiated. Forced/violation/parity literal bounds and weighted evaluation
still need to be composed at all caller sites before claiming total bit time.

The array payload measure dominates the intended standard dense integer input.
It is not a verified byte serialization protocol. A solver with unusually large
witness outputs also requires its ordinary output-size/time guarantee when those
witnesses are decoded; mere feasibility correctness does not bound arbitrary
unused witness coordinates. This is a local external primitive obligation, not
permission to assume a bound for the entire MOR34 procedure.

## Remaining work in the approved scope

1. Retain raw-normalization scalar/query tables and instantiate their read budgets
   using standard collection/sorting contracts. Their semantic correspondence is
   already proved. Do not reopen the geometry or sorting internals.
2. Finish the charged outer schedule: parity support and extrema, cells, exchange
   witnesses, point emission/storage, rank matrices and output relabeling. Reuse
   the existing call/cardinality/bit bounds. Preserve the actual stored answers.
3. Substitute weighted arithmetic and local solver/rank/collection bounds into
   that schedule with polynomial degrees independent of q, then apply the
   already checked compression substitution and parameter-factor inequalities.

The general pairing, exchange, span, component and correctness theorems are not
missing. The remaining issue is one phase-complete cost derivation. A definition
summing plausible phase budgets, or a premise asserting the desired total cost,
would not finish it. Full-FPT and complete-paper flags therefore remain false.

## Local review findings

The array transfer checks lengths before using default-zero indexed reads.
Zero-dimensional arrays are admitted; the raw public theorem separately keeps
its original nonempty-input hypotheses. Prefix filters and forced residual
lists keep their original order. Row-index enumeration does not use an arbitrary
classical ordering. Separate input and query read budgets are passed to the raw
pipeline, since the latter can require quadratic access allowance.

No new experiments are claimed from the existing fifteen smoke checks. Named
axiom counts are evidence coverage, not a percentage of paper completion.

## Final caller review

Reusing the supplied `(weight, R)` value in several forced rows overcounts that
read if the caller retained it once; it does not undercount it. The residual
table itself is constructed once per forced request, not once per slope.
`denseNormalizedPipeline` is currently used for the output-equivalence theorem;
its existence does not assert that all pure extrema/point definitions are
shared by the eventual charged outer execution. That sharing is a remaining
cost-composition obligation and is stated explicitly above.

All solver size theorems apply to well-sized arrays produced by the corresponding
constructors. The generic interface also permits q=0; the public raw theorem
retains the paper's positive-size and well-formedness assumptions. The bit-size
measure includes a dimension/row-count allowance; any fixed encoding convention
and its constant factors belong in the established primitive cost contract.
No statement depends on equality between nominal source code and a particular
backend's allocation strategy.
