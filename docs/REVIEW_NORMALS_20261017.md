# Statement review: bounded normal integration and input normalization

This is a same-session mathematical and source review, not independent review. Compiler acceptance and exact source identity are recorded separately in ACCEPTANCE.json and normals_verified_metadata.json. These notes do not mark an uncompiled draft as verified.

## The complete row-space test

ColumnNormals uses the original column index type throughout. For a selected full-row-rank integer matrix R and an original-column embedding c, A=R[:,c]. For every original column j, the integer vector is

v_j(k) = det(A) [k=j] - sum_i cramer(A,R[:,j])_i [c(i)=k].

The list has one vector per original column; zero vectors are allowed. These are equations, not a claimed linearly independent normal basis. Their common rational zero set is exactly the row span. For the converse, invertibility of A supplies weights w with w A = y_pivot; the Cramer identity converts each normal equation to det(A)y_j=det(A)(w R)_j. Cancellation proves membership for every column. No unproved double-annihilator implication is used.

For a possibly dependent input matrix, an independent spanning family of ORIGINAL rows is selected before taking original columns. No rational row elimination is used to claim preservation of the entry bound. The choices of rows, their enumeration and pivot columns are still classical.

## Magnitude and bits

At most one selected pivot index contributes to a given coordinate because c is injective. Each coordinate is therefore bounded by 2 r! N^r. With d columns, r<=d and N>=1 give 2 d! N^d. In the augmented count setting d=q+1.

The implemented bound is H(q,N)=2(q+1)!N^(q+1), including the affine constant. The magnitude-bit function is ceil(log_2(|z|+1)); a sign bit is separate. Its bound is

(clog_2(q+1)+clog_2(N))(q+1)+2.

Strict violations of a normal require the integer offset 1. Their coefficient magnitudes are at most H and their right sides at most H+1. Substitution z=2v+epsilon yields coefficient bound 2H and right-side bound H+1+qH. The parity theorem connects the integer transformation to the actual rational CountInequality.withParity row, rather than only proving a bound for an unrelated expression.

## Integration rather than attribution to an old choice

boundedCountForms is a fixed CLASSICALLY CHOSEN family satisfying the new magnitude bound. It does not attach this bound to the earlier arbitrary quotient-normal choice. boundedCellSelection and boundedPipeline use boundedCountForms in the actual recursive span searches. The old normalizedPipeline remains in the project as a legacy theorem.

CountSearchFormsBounded follows each successive solver answer. Containment of every inserted count vector in the cell proves the coordinate bound at every queried intermediate state. The guarantee is not restricted to the final selected basis. The number of scalar feasibility queries per cell is still at most 2(q+1)^2.

The boundedPipeline output contract retains the invalid witness / valid empty face / supported face split, signed dimension, geometric facet test and real tight-point affine basis. It remains relative to the explicitly stated exact ILP and rank interfaces.

## Boundary cases

Empty row families are covered by the determinant of the empty matrix. The resulting standard coordinate equations exclude every augmented vector (1,z), as required for the span of an empty count selection. Full augmented row span is described by zero equations; keeping q+1 zero entries in the list is harmless and does not cause false positive queries. Dependent input rows are allowed in the generic FormsDescribe construction. All proofs quantify over arbitrary finite sizes, including q=0 where the helper interfaces permit it.

## Finite pivot search

allFinFunctions enumerates d^r maps Fin r -> Fin d, including the r=0 case. tryPivot checks injectivity and a supplied exact determinant evaluator. pivotSearch is sound, complete for independent rows, and makes at most d^r attempts. This is a separate component: it has not replaced the classical choices in boundedCountForms. The evaluator contract is not a verified determinant implementation, and candidate count is not a bit-operation runtime.

## Grouping and sorting

GroupedSorting uses Mathlib's Tuple.sort to permute each coefficient class and proves WellFormed from all the grouped hypotheses except sortedness. The class labels are unchanged; weight sums and candidate values are preserved under the item permutation. Feasibility, tightness and validity transfer.

InputGrouping constructs coefficient classes from the actual finite image of the raw coefficients. Each fiber is nonempty. Its enumeration is combined with within-class sorting to obtain a normalized Model and a bijection to the original Fin n items, preserving weights, coefficients, capacity and right side. The hypotheses match the paper: n>0, positive weights/capacity, feasible singletons and nonnegative candidate coefficients. Empty n is not silently claimed.

RawTransport states the original subset predicates explicitly and proves their equivalence under a supplied preserving item bijection. This covers original feasible sets, tight sets and validity. RawGeometry additionally transports the actual tight binary vectors and the finrank of their affine-direction span through a real linear equivalence. The parameter bounds also refer to the original coefficient values. The signed dimension including the empty value -1 is also preserved, and boundedPipeline_raw_dimension composes it directly with the computed dimension return value. The complete returned output record, returned affine independence and geometric facet predicate are not yet all composed into a raw-input wrapper. Accordingly full original-input preprocessing/output integration remains unfinished.

## Prefix intercept helpers

PrefixEncodingBounds proves |prefixCost(w,z)|<=zM, ordinary intercept magnitude<=2sM and forced shifted intercept magnitude<=(2s+2)M for |w_i|<=M. These are generic integer estimates for the expressions occurring in ordinary/forced row definitions; no sortedness assumption is needed. They are not yet a complete encoding-length theorem for all generated rows.

## Limits retained

No complete FPT runtime, primitive ILP/rank implementation, Frank--Tardos proof or total bit-cost model is supplied by this checkpoint. No frozen definition in Model, Targets or PaperInterface is changed. Standard mathematical tools are not claimed as new research results. The proof-count increase measures audited declarations only, not a completion percentage.

## Interface assumptions checked explicitly

ParityRowSolverSpec assumes only that returned integer solutions satisfy the explicit rows and that a none answer means no integer row solution exists. It does not assume the target affine span, dimension, facet or basis conclusion. ExactIntegerRank assumes the exact rational rank of the input integer matrix, not the output dimension. These are standard primitive contracts, still unimplemented foundations in this project.

The bounded normal-family chooser uses the current finite selection B and its countRadius; it does not depend on the unknown future cell basis. On the empty selection countRadius=1, and the general augmented equations correctly exclude all vectors with leading coordinate 1. Zero normal equations at full row rank generate impossible strict-side queries and hence cannot add a false point under the solver contract.

The raw normalization theorem has exactly n>=1, positive weights/capacity, each singleton feasible and nonnegative c. The reference manuscript's Preliminaries begins with the same n>=1 and positivity hypotheses. Negative right-hand sides and the all-zero candidate vector are not excluded by normalization. The signed-dimension bridge explicitly assumes validity, so it does not incorrectly assign a supporting-face dimension to an invalid candidate.
