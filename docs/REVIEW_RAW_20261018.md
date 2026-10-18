# Review of original-input output transport and row-size bounds

This is a same-session source and mathematical review. It is not independent review. The final accepted commit, complete build logs and axiom audit are recorded in ACCEPTANCE.json and raw_verified_metadata.json only after the final CI gate passes.

## Original input and scope of the new top-level theorem

The reference manuscript assumes n>=1, positive integral weights and capacity, feasible singletons, nonnegative integral candidate coefficients, and an arbitrary integral right side. RawNormalization/normalizeRaw use exactly those hypotheses. Candidate validity is not an input hypothesis of original_input_output_contract. The primitive solver structure contains the soundness and completeness contracts for the explicit row systems, plus exact rational matrix rank. It does not contain a desired face, dimension, span or facet conclusion.

The normalization record contains a class count, nonempty class sizes, the normalized sorted model, and a bijection to the original Fin n coordinates. Weight, coefficient, capacity and right-side preservation are explicit fields, proved from normalized_model_exists. The same item bijection is used for the output witnesses, output basis, and geometric coordinate map. The parameter bound counts the distinct positive coefficients in the original input, not a separately supplied upper bound.

RawDecision uses three distinct branches:

- invalid: a feasible original subset whose coefficient sum exceeds the original right side;
- empty: validity and an empty equality face; no returned basis;
- supported: validity, a tight original subset, the real affine-direction dimension of the equality face, and a Boolean equivalent to geometric facetness.

RawOutput adds a finite family of original subsets. In the supported branch every subset is tight, its binary points are affinely independent, their affine span is the full tight-point affine span, and the family has dimension+1 members. Invalid and empty branches return the empty family. The dimension accessor is none for invalid input, -1 for a valid empty face, and the nonnegative dimension otherwise. No numerical convention is silently used to identify an invalid candidate with an empty valid face.

## Geometry is not defined by the answer

rawKnapsackPolytope is the convex hull of the original feasible binary points. rawCandidateLinear is the original coefficient dot product. rawCandidateFace is its equality level in that convex hull. RawDefinesFacet requires validity and the same IsCodimensionOneFace predicate used in the normalized development: a nonempty convex extreme subset with affine codimension one.

RawFacet first proves the original supporting-level identity directly with supporting_hull_eq. It then transports feasible and tight point sets, convex hulls, supporting faces, nonemptiness and affine-direction dimensions by relabelLinear. Facet equivalence is a consequence of those facts; it is not a definition by a rank test or the algorithm's Boolean. Validity is used where the equality level is asserted to be the convex hull of tight generators. This condition is essential.

RawBasis maps finite subsets through Equiv.finsetCongr, which is injective. Its induced equivalence on the basis index types proves affine independence after the linear equivalence of coordinate spaces. The family cardinality is preserved exactly. The affine-span proof maps both sides of the already established normalized span equality. It does not infer affine independence merely from cardinality or span.

## Coefficient and payload bounds

CountInequality stores rational coefficients, while all actual query families use integer coefficients. IntegerBounded explicitly exhibits integer representatives for both q-variable blocks and the right side. The proofs therefore establish integrality as well as magnitude bounds. Generic user-supplied rational restrictions are not claimed to be integer-bounded without a corresponding hypothesis.

For a class-size bound N, original magnitude bound M>=1, and integer extra-query bounds C,D>=0, write

R(N,M,D)=(2N+2)M+N+D+1.

The actual count rows have count-coefficient bound M+C+1, cost-coefficient bound 1, and right-side bound R. Parity substitution z=2v+epsilon changes these bounds to 2(M+C+1), 1, R+q(M+C+1). This statement is connected to the actual withParity operation.

Forced exchange rows include ordinary rows from unaffected classes, the residual sorted-weight slopes, a separate empty-residual row, forced count bounds, candidate equalities and capacity. All of them have bounds M+1,1,R(N,M,0). The violation row has right side -(d+1), not -d. The proof includes this strict integer offset. Its base feasible rows are related to the actual count-row constructors, without adding candidate equality by mistake.

A cell contributes three rows per coordinate: lower bound, upper bound and guard. Even when an endpoint alternative is empty or duplicate, the guard is retained. With low and high coordinates in [0,N], these query rows have coefficient bound 1 and right-side bound N+2. Neither validity of the particular mode nor nonemptiness of that cell is assumed for this magnitude estimate.

For H=2(q+1)!N^(q+1), the strict normal query has bounds H,H+1. Combining it with the cell rows gives bounds H+1,N+H+3. The common radius

U=(6N+10)(M+H+1)

dominates every integer entry in the resulting parity row system when q<=N and M,N>=1. A deliberately loose but explicit bound on each signed integer payload is

B=clog_2(N)+clog_2(M+1)+(clog_2(q+1)+clog_2(N))(q+1)+8.

The actual scalar cell query has n+5q+4 rows, each with 2q integer coefficients and one integer right side. The total dense integer payload is consequently bounded by

(n+5q+4)(2q+1)B.

BasicRowPayload also provides full-system totals for forced and violation rows: respectively (n+2q+card(pairAllowed)+6)(2q+1)B and (n+2q+2)(2q+1)B. These are the actual row index cardinalities, not a guessed number of constraints.

The payload sum counts magnitude bits and a sign bit, including zeros. It is not a claimed self-delimiting serialization format. Dimension/row headers, parsing, integer arithmetic costs and solver runtime remain separate. The logarithmic expression gives the relevant polynomial coefficient-size statement rather than an inference from small numerical examples.

SearchStates follows the actual recursive oracle answers. The payload invariant is established at every queried state from containment of all inserted points in the cell. It covers every potentially issued separating query at that state, hence also the prefix of such queries actually inspected by firstWitness. The instantiated theorem uses exactly rowSearchedExtrema, rowCellOracle and boundedCountForms from boundedPipeline. It is not restricted to the final basis.

## Concrete small determinant evaluator

laplaceDet is a direct recursive Laplace expansion on Fin r integer matrices. Correctness is proved against Mathlib's determinant. exactPivotSearch supplies this evaluator to the earlier finite pivot enumeration and discharges its determinant-correctness hypothesis.

The traced evaluator returns the same determinant and an arithmetic counter. A sign power is charged its exponent, and each summand is charged for two products and one addition. The recursive upper budget is T(0)=0, T(r+1)=(r+1)(T(r)+r+3), with T(r)<=(r+3)^2 r!. Array indexing, construction/storage and machine bit costs are excluded explicitly.

Every Laplace term has magnitude at most r!N^(r+1). Every partial sum of the r+1 terms, before cancellation, has magnitude at most (r+1)!N^(r+1). Its bit bound follows from the existing factorial-power estimate. Thus the final determinant bound is not being used to assume a bound on potentially larger intermediate sums.

PivotCost sums determinant arithmetic along the actual firstWitness path. Noninjective candidates have zero determinant charge. The total determinant arithmetic is at most d^r(r+3)^2 r!. Candidate construction, injectivity checks, branch tests and integer bit costs are deliberately excluded rather than silently treated as free in a full runtime claim.

The exact pivot procedure remains separate from boundedCountForms, whose independent-row and pivot selection is still classical. This update must not set executable_normal_generator=true. Factorial determinant expansion is only intended for matrices of parameter-bounded dimension. It must not be used as the rank algorithm for the final matrix with n+1 columns.

## Alignment with the manuscript and remaining obligations

The structural pairing, exchange, quotient and affine-cell results are unchanged. The source model and theorem interfaces remain frozen. The implemented coordinate-extrema routine uses a finite scan, whereas the manuscript describes binary search. The scan changes the displayed call count from a logarithmic factor in n to a polynomial factor in n; it still fits the claimed FPT form if all remaining runtime obligations are proved. It should not be described as a formal proof of the manuscript's exact sharper oracle-call expression.

The new top-level output theorem completes original-input semantics relative to the explicit primitive contracts. It does not implement the ILP solver or exact rank algorithm. Classical normalization, Finset enumeration choices and bounded-normal choices remain in the overall pipeline. A verified output contract is not an executable bit-complexity theorem. Complete paper, unconditional algorithm and full FPT/compression flags remain false.

The next concrete work is to replace independent-row/pivot choices in the actual normal generator, preserve deterministic finite ordering through normalization and basis extraction, and connect the coefficient-payload bounds to a complete cost model. Primitive ILP, exact rank and Frank--Tardos implementation/complexity foundations remain separately scoped.

## Finite normal-candidate certificate

NormalCandidate separates a useful executable test from choosing an independent row basis. A candidate selects original rows and an injective list of original columns with nonzero determinant. If each original row annihilates every resulting Cramer normal, columnNormals_describe puts every original row in the selected-row span. The reverse span inclusion holds because the selected rows are original rows. Hence the candidate describes the entire original row space, not merely a subspace of it. normal_candidate_exists derives a successful candidate from an independent original-row basis and a nonzero original-column minor. Classical selection occurs in this existence proof; no executable enumeration is claimed yet. The zero-row and zero-rank cases are included through the Fin 0 determinant convention.

## Boundary cases and parameter interpretation

The raw hypotheses allow zero candidate coefficients and arbitrary negative right side. A negative right side is handled by the invalid-witness branch rather than silently excluded. An all-zero candidate with right side zero defines the entire polytope; the geometric codimension test does not call it a facet. A valid equality level with no tight generator uses the separate empty branch and dimension -1. Returning an empty basis in either the invalid or empty branch is part of the output contract. These facts follow from the branch specifications and transports, not from numerical examples.

The candidate certificate includes rank zero: the empty pivot determinant is 1, its Cramer equations describe the zero row span, and the all-row checks force every original row to be zero. The existence theorem also permits zero row/column counts. Original knapsack inputs still require n>=1 as in the manuscript.

With d=q+1 and N=n+1, the dense row-payload expression is polynomial in n, log M and q. Candidate enumeration at small search states can retain a 2^{O(q log q)} parameter factor even with factorial small determinants. This is a mathematical route, not an established Lean runtime theorem: actual state cardinalities, integer operation costs, deterministic enumeration, and external primitive cost composition still need formal connection. In particular the classical existence proof of a successful candidate is not counted as execution of an enumeration algorithm.
