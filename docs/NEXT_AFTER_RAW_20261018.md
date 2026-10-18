# Resume after original-input output and row-payload integration

Read ACCEPTANCE.json, session_raw_20261018.json, raw_verified_metadata.json and REVIEW_RAW_20261018.md first. Final successful CI, source identity and retained logs are authoritative. Do not redo the completed raw output wrapper. Preserve all older checkpoints and the frozen Model, Targets and PaperInterface hashes. Work on codex/mor34-formalization; no merge or publication. Do not bypass local compiler restrictions; use GitHub Actions.

## Completed semantic endpoint

RawInputPipeline.original_input_output_contract takes original Fin n integer data, the manuscript positivity/singleton/nonnegative-coefficient hypotheses, and RowPrimitives for the normalized model. Its RawOutput.Correct conclusion includes original invalid witnesses, valid empty equality faces, supported-face dimension, a geometric facet Boolean, and an actual affine basis of original tight binary points. rawNormalization_dimension covers empty dimension -1. rawNormalization_parameter uses the actual positive coefficient values. Primitive ILP and rank correctness remain explicit; no runtime is inferred.

RawFacet, RawBasis and RawOutput provide reusable transports. In particular do not rebuild an independence argument from cardinalities: relabelBasis_independent already proves it under the index and coordinate equivalences. Do not redefine facetness by rank.

## Query coefficients and payload

IntegerRowBounds has the integer representative predicate, parity transformation, signed payload lengths and generic row bounds. CountRowBounds, ForcedRowBounds and ViolationRowBounds cover actual constructors. CellQueryBounds includes all three coordinate rows, the strict normal query and their actual withParity rows. RawEncodingBounds transfers raw magnitude assumptions and class sizes.

UniformEncoding uses H=2(q+1)!N^(q+1), U=(6N+10)(M+H+1) and signed-bit bound

clog_2 N + clog_2(M+1) + (clog_2(q+1)+clog_2 N)(q+1) + 8.

BasicRowPayload proves the forced and violation systems' total dense payload using their actual row cardinalities. RowPayload bounds the actual n+5q+4 row scalar-cell system by (n+5q+4)(2q+1) times that bit bound. SearchPayload follows all actual recursive states with N=card(Item)+1. It bounds every potentially queried separating normal at each visited state, a safe superset of the firstWitness prefix. The overall encoding length still needs a precise header/serialization convention if the cost model uses serialized input. The payload sum is not itself a self-delimiting wire format.

If extending these bounds to the entire operational trace, include the initial support queries, extrema thresholds, validity and edge calls. The per-family coefficient lemmas are available. Use the correct searched extrema witnesses to bound low/high endpoints. Do not assume an arbitrary supplied extra rational row is integer-bounded.

## Concrete small determinant and remaining generator

FiniteDeterminant gives laplaceDet, exactPivotSearch and an instrumented scalar-arithmetic trace. The exact determinant premise is discharged for exactPivotSearch. PivotCost bounds determinant arithmetic along its actual search path by d^r(r+3)^2 r!, excluding enumeration/injectivity/bit costs. DeterminantIntermediates bounds each term and any partial sum before cancellation, including magnitude bits.

This does NOT replace boundedCountForms. It still selects independent original rows and pivot columns classically. The next useful step is a deterministic normal generator, with verified connection to the family actually passed to linearSpanOracle. Keep the semantic FormsDescribe and magnitude contract so the rest of the pipeline can be reused.

A potentially simpler route, identified and partially formalized at the end of this round, is finite candidate enumeration. NormalCandidate proves selected_rows_span_of_checks and checked_candidate_describes: a nonsingular original-row/original-column minor, together with integer annihilation checks on every original row, suffices to describe the entire original row space. normal_candidate_exists supplies completeness of this candidate test. None of these theorems is yet the executable enumerator.

For an s-by-d integer matrix, enumerate r=0,...,d and all row/column maps Fin r -> Fin s and Fin r -> Fin d. Reject noninjective columns and zero determinants; test every original row against the Cramer normals. Soundness does not even require row-map injectivity; the nonzero minor guarantees it. Completeness follows from the new existence theorem. Use deterministic firstWitness and retrieve its result with Option.get using the proven isSome fact. The test only uses finite integer equalities.

At actual count-basis search states, s<=q+1 and d=q+1. This cardinality invariant must still be explicitly connected to every queried state; the current SearchPayload containment invariant only controls coordinates. A direct way to prove the missing state-cardinality invariant is induction on basisSearch fuel using card(insert z B)<=card B+1, maintaining B.card+fuel<=q+1 from the empty start. No solver correctness is needed for this cardinality argument. The stronger queried-state bound can be used separately from containment.

For d>=1 and s<=d, at most (d+1)d^(2d) candidates are inspected (an informal bound to formalize). Each candidate needs at most 1+rd small determinants for direct Cramer entries and O(sd^2) integer operations to check annihilation, in addition to enumeration and injectivity tests. Thus the crude enumeration still fits 2^{O(d log d)} times polynomial bit cost. For arbitrary large s, do not silently claim FPT from an s^d bound. Existing semantic contracts can cover arbitrary finite B while the runtime proof uses the actual small-state invariant.

Replace the Matrix.det/Matrix.cramer values in the generated entries with laplaceDet on the pivot and updated-column matrices; prove equality to columnNormal. A classical existence proof used solely to prove a successful finite search does not make the extracted data classical, but a Classical.choose in the data-producing definition would. Deterministic enumeration of B and raw normalization still need their own implementation.

An alternative route is incremental selection from an ordered list of original rows:

1. Maintain a finite matrix of independent selected original rows plus a pivot embedding with nonzero determinant.
2. Use columnNormals_describe to decide whether an input row lies in their rational span by finite integer dot-product equality checks.
3. If it is outside, append it and use exactPivotSearch. Completeness provides Option.isSome; Option.get retrieves a computed pivot without classical selection.
4. Prove span preservation at every step and original-entry magnitude preservation. The selected row count is bounded by q+1.
5. Form the existing Cramer equations using the computed rows and pivot. Bound arithmetic counts and intermediate bit sizes.

Pinned Mathlib APIs checked on October 18:

- LinearAlgebra/LinearIndependent/Lemmas.lean: linearIndependent_fin_cons, linearIndependent_fin_snoc, LinearIndependent.fin_cons.
- LinearAlgebra/Matrix/Adjugate.lean: Matrix.cramer_apply identifies a Cramer entry with the determinant after updateCol.
- Data/List/OfFn.lean: List.ofFn_injective, List.ofFn_inj.
- Data/List/Lex.lean: LinearOrder (List α) for ordered α.
- Data/Finset/Sort.lean: Finset.sort and sort_perm_toList.

For deterministic count-set enumeration, a local order can be lifted from List.ofFn, then Finset.sort can replace arbitrary toList. Check computability of the instantiated order rather than merely removing a noncomputable keyword. For raw normalization, enumerate coefficient values and fibers in their natural integer/Fin orders; replace Fintype.equivFin choices. Returned finite point families also need a deterministic enumeration if the whole pipeline is claimed executable.

Do not use factorial minor enumeration to rank the final n-column matrix. The parameter-sized determinant implementation is only appropriate for the small normal-generator matrices.

## Complexity and manuscript alignment

The currently formalized extrema routine scans thresholds; the manuscript describes binary search. The larger polynomial n factor is compatible with the final FPT form, but the manuscript's exact sharper oracle-call expression is not thereby formalized. Preserve this distinction in reports.

Unconditional primitive ILP/rank implementations, a complete bit-operation model, the full asymptotic FPT theorem and Frank--Tardos compression remain separate. Complete paper and complete FPT flags must stay false until those are actually done. Same-session inspection and kernel compilation are not independent external review.

## Evidence and time

Run all eight readiness commands and all named-theorem axiom checks. Capture the exact artifact digest, manifest, source Git-blob correspondence and frozen hashes before changing acceptance. Avoid counting CI-only waiting, upload tail or gaps between sessions as active work. The new checkpoint records actual active time; earlier unlogged preparation remains unknown. Do not equate declaration count with a completion percentage.
