# Statement review: searches, exact solver rows, and recognition branches

This is a same-session review. A final verified source commit and compiler evidence are recorded in ACCEPTANCE.json only after the gates pass. This document does not certify an independent replay or a complete runtime theorem.

## Frozen problem

Model.lean, Targets.lean, and PaperInterface.lean are unchanged. All new conclusions refer to the existing Feasible, Tight, Valid, Exchange, full coordinatewise TightParity, and CellCondition predicates. In particular, the zero coefficient class is not removed from the parity vector. Existing WellFormed hypotheses include positive weights and capacity, feasible singletons, nonempty classes, and sorted weights.

## Search and attainment

ThresholdSearch uses the first successful lower-bound query, scanning n,n-1,...,0. It proves a maximizer only when every feasible score is bounded by n. Its existence lemma needs no score upper bound because the zero threshold is feasible in every nonempty set. No monotonicity of a particular returned witness is assumed.

CoordinateSearch obtains minima by reflecting z_j to m_j-z_j, using the actual integer upper bound m_j-k. The bounded-count hypothesis makes the reflected natural subtraction valid. Each returned count vector stays in the same full parity set. SearchedExtrema uses Option.get on the search output: it is not a separate classical choice of a point that happens to attain the same value. Both extrema are attained, and both search-result equations are explicit.

This implements linear scans rather than the manuscript's binary searches. The cost is at most 2(n+q)2^q feasibility calls over all parity classes. This polynomial overhead preserves compatibility with the intended FPT target, but no total-runtime claim follows from it alone.

## Cells and linear queries

Each coordinate contributes lower, upper, and constant-guard inequalities. The upper middle endpoint is h_j-2 in the integers, not natural truncated subtraction. The guard removes the high endpoint if low=high. Consequently the encoding also handles empty middle intervals, coincident extrema, and h_j<2 without inadvertently admitting extra points.

CellQueries proves exact equivalence to the original CellCondition, not a relaxed box. A separating query is prepended to the 3q cell inequalities. ParitySolver converts that entire finite list to the previously verified explicit integer rows and decodes the solver's actual integer solution. Its soundness and completeness assumptions concern only those concrete rows. RowSolverPipeline then supplies both attained extrema and cell search to the original CellBasisSelection, and connects the result to the existing retained-matrix rank identity.

## Validity and support

ViolationEncoding does not reuse the tight-equality rows. It uses only count bounds, ordinary prefix epigraphs and capacity, adding candidateValue>=rhs+1. Integrality justifies the strict violation offset. There are 2q integer variables and n+2q+2 rows.

RecognitionBranches checks invalidity first. A successful violation solution gives an actual original feasible binary set violating the candidate inequality. On failure, the solver's completeness yields Valid. Support scans all full parity classes; success gives an actual tight prefix, while complete failure excludes every original tight set by prefix minimality and parity coverage. The empty branch records Valid and no tight set, not an unsigned affine dimension of zero.

## Forced exchange rows and witnesses

The existing forced minimum keeps v and omits u, using the cheapest residual prefix at count z_j-1. ForcedLinearEncoding turns each residual line into

    w_a*z_j - y_j <= (a+1)*w_a - F_R(a) - w_v.

The cast of natural z_j-1 is justified only after proving z_j>=1. IntegerForcedEpigraph separates this arithmetic conversion from the original natural-count predicate. The empty-residual row is active exactly when deleting the pair leaves no items; it requires y_j>=w_v. It is never silently omitted.

ForcedRows preserves all original count bounds and adds 1<=z_j<=m_j-1. Ordinary slope rows in the forced class become zero rows; residual slopes replace them. This uniform representation is deliberately redundant, with n+2q+|R|+6 rows, all on 2q integer variables. This is not the smaller n+2q+2 row count proposed for an optimized formulation. Both are linear-size; only the implemented uniform count is claimed here.

The row feasibility equivalence is for the original Exchange and includes u<v. ForcedSolver does not interpret a feasible row system for reversed endpoints as an exchange. It returns the concrete forcedSet decoded from the integer solution, with Tight, forced-out membership and forced-in membership proved. ComputedEdges filters only adjacent pairs and proves exact agreement with the edge relation and direction span used by the structural theorem. EdgeWitnesses additionally extracts the actual returned tight set and its tight swap, whose point-vector difference equals the edge direction. There are at most n candidate adjacent pairs. ComputedMatrix constructs rows from that actual finite list and transfers the existing rank identity by an explicit row-index equivalence; its row bound is still n+(q+1)6^q.

## Dimension and accounting

FeasibleDimension proves the original feasible binary point set has full affine span and vector-span dimension n. The empty set supplies zero; feasibility of every singleton supplies every standard coordinate vector. The convex hull is explicitly defined as knapsackPolytope and has the same full affine span and dimension by Mathlib affineSpan_convexHull. The equality face and formal facet predicate still require a separate bridge.

QueryAccounting sums the validity, support, extrema and cell phases. It is a logical call budget, not an instrumented total runtime. Its cell phase is guarded by mathematical nonemptiness, and its budget explicitly reserves an additional feasibility query for every parity class; end-to-end executable control flow, exact normal generation and rank computation remain separate obligations. Classical normal existence bounds the number of normal forms, not their coefficient sizes.

## What remains open

- Connect every computed component into one returned recognition certificate and exact rank computation.
- Replace retained directions by actual tight-point witnesses when returning the manuscript's affine point basis.
- Connect the full-dimensional feasible polytope, valid supporting equality level and formal facet predicate.
- Bound normal coefficient lengths and provide a costed normal-generation procedure.
- Formalize fixed-dimensional integer-programming runtime, input bit complexity and Frank–Tardos compression.

The complete algorithm-correctness and full-FPT flags remain false until these obligations are discharged. The number of named checked lemmas is not a completion percentage.

## Normalized input versus arbitrary paper input

All solver correctness statements start from the frozen grouped Model and WellFormed assumptions. They therefore assume sorted class weights, distinct class coefficients, nonempty classes, positive capacity/weights, and individually feasible items. The original paper's preprocessing from an arbitrary binary-knapsack input to this normalized grouped model has not been turned into a verified algorithm. In particular, the q<=K+1 parameter translation and encoding cost of normalization are not proved merely by having a field named coefficient. This remains part of the whole-paper obligation and is another reason not to mark complete_paper true.

## Last accounting correction

The aggregate budget reserves 2^q extra calls for per-parity nonemptiness checks, separately from the initial support search (which may stop early). Thus the current bound is

    1 + 2*2^q + 2(n+q)2^q + 2(q+1)^2 6^q,

plus at most n exchange calls. This is a conservative budget; reusing already returned extrema/support witnesses could avoid some calls, but no such reuse is assumed in this claim.

## Boundary cases reviewed in this round

- Threshold existence and optimality are separate: the zero threshold ensures a result on a nonempty set, while a score upper bound is required for the maximizer conclusion.
- Minimum search reflects coordinates only under the original bounded-count condition; it does not infer z_j<=m_j from natural subtraction alone.
- Cell equivalence is proved even for arbitrary low/high vectors, not just attained extrema; the actual cell pipeline supplies valid extrema separately.
- A forced pair with u>=v is rejected by exchangeWitness before its solver answer is interpreted. Feasibility of rows for such endpoints is not claimed to imply Exchange.
- In the two-item forced class, residual slopes are absent and the explicit constant row remains. Ordinary other classes use WellFormed nonemptiness.
- The forced upper bound is integer m_j-1. Conversion to the original natural bound uses the integer lower bound and the presence of a valid Fin(m_j) endpoint.
- The returned swap preserves the candidate value because both items share a class, and preserves feasibility by sorted weights. It does not require the candidate inequality to be valid.
- Matrix rank correctness requires a nonempty tight set; the valid-empty recognition branch remains separate and is not assigned natural dimension zero.
- The original feasible point set contains zero and every unit vector by the frozen normalized-input assumptions. The full-dimension proof does not assume tight points span the entire ambient space.
- The actual matrix may still use classically selected normal forms and finite selections; its concrete integer entries and correct mathematical rank do not by themselves certify an executable rank routine.

The zero-candidate corner cases also fit the stated interfaces: coefficient=0 and rhs=0 make every feasible point tight, so the full-dimensional polytope has augmented rank n+1 rather than the rank n expected for a facet. Positive rhs yields a valid empty level, and negative rhs is violated already by the empty feasible set. No nonnegative-rhs assumption was added to WellFormed. These are semantic checks of the existing branch statements, not separately claimed new Lean theorems.

## Change in the proof boundary

| Previous checkpoint input or abstraction | This checkpoint's replacement | Still external or unfinished |
| --- | --- | --- |
| Attained parity extrema supplied to cell selection | Actual coordinate scans, attainment and exact result equations | Cost of executing integer-feasibility calls |
| A correct linear solver for each arbitrary cell | Exact 3q cell constraints and parity-row decoder | Primitive explicit-row ILP solver soundness/completeness |
| Semantic global Exchange relation | Uniform explicit integer rows, witness decoder and decision equivalence | ILP implementation and bit cost |
| Semantic adjacent-edge subtype in matrix rows | Filtered adjacent-pair list and proved row-index equivalence | Costed enumeration implementation analysis |
| Direction rows justified by existential tight points | Actual solver-returned set and its tight swap | Independent extraction from the finite family of returned points |
| Semantic count violation reduction | Separate feasible-plus-violation row generator and three original branch outcomes | One packaged end-to-end recognition certificate |
| Full dimension used in paper facet argument | Full affine span of feasible binary points and their convex hull | Equality-face hull theorem and geometric facet predicate |

The ILP contracts specify exactly which inequalities a solver must satisfy and what a negative answer means. Their correctness is a hypothesis of the surrounding algorithms; no opaque axiom was inserted to make the algorithms appear unconditional. The correctness assumptions have been made more concrete, while the unproved computational foundation remains visible.
