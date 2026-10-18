# Reference-algorithm cost derivation for the final formal block

This is a mathematical continuation note, not a checked Lean total-time theorem.
It records the remaining phase argument under the new-proof-only scope. No
claim about compiler caching or machine serialization is made.

Write n for item count, q for all coefficient classes including zero, and let
L bound the binary magnitude of every original coefficient. Put t=n+L+2.
A conventional total input length dominates this choice of L. Let c and e be
fixed polynomial exponents for the externally supplied ILP and exact-rank
algorithms, respectively. They must be independent of q and n.

Use a reference algorithm that evaluates each adjacent-pair solver once and
stores its answer, stores the two coordinate-extrema witness families per
parity, and stores each normal family before testing its scalar inequalities.
These are ordinary finite data tables, not an assumption that the Lean backend
memoizes arbitrary function-valued terms. Their semantic relation to the
proved pure definitions must be included in the final formal interface.

## Solver phases

1. The checked rowSearchCalls bound covers validity, support, scanning extrema
   and cell queries. It is at most Frow(q)(n+1), with
   Frow(q)=1+6*2^q+2(q+1)^2*6^q <= (q+2)^(3q+5).
2. Add at most n adjacent-pair feasibility calls when answers are stored once.
3. Every actual cell/forced/violation row system has payload <=168t^4. Signed
   variables can be split into positive/negative parts if required by the
   external canonical form: dimension remains at most 4q and payload changes
   by a constant-factor duplication plus elementary nonnegativity rows.
4. If the fixed-dimension solver costs G(4q) B^c on B-bit instances, the solver
   phases have cost at most a constant times
   (Frow(q)+1) G(4q) 168^c t^(4c+1).
   G(r)=r^{O(r)} is external. The composition with our dimensions and payload
   is the newly contributed application.

## Solver witness representation

The external primitive contract must include a returned feasible integer witness,
not only a feasibility bit. A bit-time bound already bounds the number of output
bits under the usual computation model. Our semantic code consumes the count
part and decodes it only after proving the original count bounds. For the
reference algorithm, store the answer once and use the bounded decoded counts
for prefix construction. Do not charge every arbitrary integer in an abstract
Option value as a unit-size machine object. If a separate explicit witness-size
bound is desired, the epigraph rows and positivity of weights constrain cost
coordinates as well; this additional formal lemma is unnecessary when the
external witness-producing solver's bit-cost contract includes its output.

## Normal computations

The checked aggregate candidate count is at most
6^q(q+1)(q+2)(q+1)^(2(q+1)) <= (q+2)^(5q+4).
Each key uses only matrices of dimension at most q+1. The proved Laplace
arithmetic budget is <=(r+3)^2 r!, and coefficient/partial-sum bit bounds are
O(q(log(q+1)+log(n+1))). Since q<=n, this is bounded by a fixed polynomial in t.
Injectivity and annihilation tests use parameter-polynomially many finite
operations. Thus the entire normal phase has a q^{O(q)} factor times a fixed
polynomial in t. The final formal block should use explicit budgets, including
rejected keys and construction of the finite key list, before invoking this
asymptotic consequence. It need not reprove standard integer multiplication.

## Rank and output phases

Let A(q)=(q+1)6^q. The returned family has at most A(q)+2n points. The checked
rank-call bound is <=2(A(q)+2)(n+1)^2, and every rank input has payload
<=2(n+2)^2. The newly added counted_rank_cost_bound gives
2(A(q)+2) R 2^e (n+2)^(2e+2) from an external per-call bound R B^e.

A deliberately simple implementation can represent each returned binary point
as an n-bit list, deduplicate and order the returned family by pairwise
comparisons, and remap coordinates using the stored permutation. Even a
quadratic comparison scheme costs a parameter-only factor times a fixed
polynomial in n. This avoids any need for a specialized efficient container.

## Finite construction phases

Group/sort coefficients and weights by standard polynomial-time comparison
algorithms. Build prefix tables explicitly. Build each dense query row directly
from prefix data and the stored normal family. There are O(n^2) entries per
query and O(n) elementary terms in an unoptimized coefficient construction;
all operands are bounded by the proved O(t^2) bit limit. Under schoolbook
arithmetic, a conservative O(t^8) construction budget per query leaves ample
room for these loops. This bound is a proposed budget: the loop description
and its charge must still be written in the final formal statement. Do not
mark it checked merely because it is polynomial on inspection.

The support/extrema/cell call count is a parameter factor times t, so charging
this conservative per-query construction may require t^9 in the total budget.
A global fixed exponent such as max(9,4c+1,2e+2), enlarged if needed for an
explicit chosen container convention, is sufficient once these phase counts
are formalized. Its exact numerical value is not part of the paper's claim.

## Final combination and compression

Sums and products of the displayed q^{O(q)} factors are still q^{O(q)}. Substitute
q<=K+1 to obtain the claimed parameter form. The implemented scanning extrema
increase a polynomial n factor but do not change FPT status or this parameter
shape. Do not claim the sharper logarithmic oracle count for this implementation.

For C9, the already checked external_compression_application preserves K and
all output semantics, with coefficient payload <=18(n+1)^4. Replace L by this
bound in the completed total-time theorem. The shift t=n+L+2 is <=20(n+1)^4;
alternatively absorb t<=2(n+L+1) into the parameter-independent constant and
reuse compression_cost_substitution. Add the external strongly polynomial
compression preprocessing. The arithmetic-operation conclusion then follows.

The last paragraph depends on completion of the total-time theorem, not just
on semantic compression. This dependency remains explicitly open in the
acceptance record.
