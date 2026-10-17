# Statement review: exact count encoding and oracle-relative basis search

This is a same-session statement review. The successful revision, raw compiler output, and axiom audit are recorded separately in ACCEPTANCE.json. A theorem mentioned here is accepted only at that recorded revision.

## Exact epigraph formulation

`prefixCost` uses the original zero-based `classPrefix`, with integer weights. `prefixLine_le` proves each supporting line is below the actual discrete cost by comparing shifted prefix sums. `prefixLine_attained` supplies an attaining line at every bounded count, including zero and the last count. At the last count it uses the final item, so there is no undefined slope at index m. Tied weights are allowed.

`prefix_feasible_epigraph` is a two-way feasibility equivalence with integer cost coordinates. `tight_prefix_epigraph` adds the original candidate equality. `restricted_count_epigraph` preserves arbitrary predicates on the integer count coordinates; the specifically linear version uses explicit rational rows. It does not silently turn an arbitrary predicate into a linear constraint.

Natural/integer count conversion includes nonnegativity and upper bounds. `count_parity_substitution` proves both directions of z=2v+epsilon, and `row_parity_iff` performs the substitution on the actual coefficients and right-hand side.

`CountRow` indexes two count bounds per class, two candidate-equality inequalities, one prefix line per item, the total-capacity inequality, and r extra inequalities. The exact number is n+2q+r+3. The variable blocks contain q integer counts and q integer epigraph values; the parity formulation replaces the count block and still has 2q variables. Constants such as F(t) depend on the input and a fixed breakpoint, never on an unknown variable.

This establishes the exact linear formulation and its dimensions. Polynomial coefficient encoding length, a cost model for constructing the rows, and the fixed-dimensional ILP runtime theorem are not included.

## Basis search and solver contracts

`basisSearch` is a fuel-bounded recursive procedure over finite selections. `SpanOracleSpec` requires every successful answer to be a candidate outside the current rational augmented span, and every stopping answer to certify that all candidates lie in that span. Both directions matter. The procedure increases the span dimension after every successful answer, starts from the empty selection, and is complete with q+1 stages for augmented q-dimensional counts.

`LinearOracleSpec` is weaker and more concrete than an unrestricted predicate oracle: it solves membership in a fixed candidate set with one additional integer linear inequality. It returns a candidate witness on success and certifies that no candidate satisfies that inequality on failure. Its implementation and runtime remain explicit assumptions.

Given integer equations describing the current augmented span, `linearSpanOracle` tests each equation in both signs. For an integer-valued form f, f is nonzero precisely when f>=1 or f<=-1. The signs and constant shifts are proved by `positiveQuery_iff` and `negativeQuery_iff`. `firstWitnessCalls` and `linearBasisCalls` follow the same branching decisions as the search; they count actual logical oracle invocations, including unsuccessful calls. They do not count the cost of executing an oracle or constructing normal vectors.

The bound 2(q+1)^2 is a slightly looser quadratic bound than the paper's anchor-first O(q^2) argument, and includes empty candidate sets and the initial empty selection.

## Integer equations and scope of constructivity

`bounded_integer_forms_exist` takes coordinates in the quotient by the actual selected augmented span. There are at most q+1 quotient coordinates. Each resulting rational functional is represented by its augmented-coordinate coefficients, and a common nonzero integer multiplier clears its denominators. Only preservation of the zero set is needed, so the multiplier need not be positive.

Consequently the normal-list condition is proved inhabited rather than introduced as a project axiom. However, the choice of quotient basis and denominators is classical. This is not a certified polynomial-time normal-generation implementation, and no coefficient bit bound is proved here. `count_basis_from_linear_oracle` exposes this distinction by existentially selecting a normal family and leaving the linear-feasibility solver contract as a theorem hypothesis.

## Real affine-space bridge

The search uses rational augmented count vectors. The manuscript's cell contract uses real, unaugmented affine spans. The bridge casts rational linear combinations to real linear combinations, then uses the first augmented coordinate to recover the affine constraint. The zero/empty-set case is handled explicitly. Thus the basis output can supply the real spanning requirement used by CellBasisSelection; no generic claim that an arbitrary injective rational-linear map preserves real independence is made.

The final output theorem also supplies real affine independence. This uses preservation of rational matrix rank under the actual entrywise embedding into the reals, and the first augmented coordinate. A normal-vector bit bound and a costed algorithm for generating the normal family remain open, so not every complexity clause of paper Lemma 7 is formalized.

## Remaining main obligations

- Turn the verified global exchange epigraph into the explicit integer-row solver interface, preserving witness extraction and singleton residual domains.
- Connect the actual cell solver and extrema computations to the retained matrix procedure.
- Check validity separately, handle empty faces, and return actual tight binary points if claiming that output.
- Replace classical normal choice with costed exact linear algebra if claiming executable FPT time.
- Formalize integer-programming and compression complexity foundations separately.

The frozen Model.lean, Targets.lean, and PaperInterface.lean are preserved. No theorem count is used as a completion percentage.

## Local forced-pair minimum cost

`restrictionIndices` encodes actual subsets in the inherited increasing order of an allowed set. `restrictedPrefix_minimal` therefore applies the existing sorted-prefix minimum theorem after deleting forbidden positions, rather than treating the original unmodified prefix as valid. `forcedPairPrefix` inserts the forced-in item and takes the required number of remaining cheapest items. Its cardinality, forced pair pattern, cost and minimum-cost inequality are proved separately.

`prefix_epigraph_all_sizes` supplies a constant inequality when the residual set is empty. `forcedPairPrefix_epigraph` includes this branch, covering a two-item original class. `forcedSet` assembles that local choice with ordinary prefixes in all other classes using a dependent update. `counts_forcedSet` preserves the full class-count vector. `forced_count_bounds` derives the necessary interval 1<=z_j<=m_j-1 from the actual omitted and included items. `forcedSet_minimal` compares each fiber separately and sums the inequalities. Consequently `exchange_iff_forced_counts` is equivalent to the frozen original Exchange predicate, not a replacement graph definition.

`exchange_iff_forced_epigraph` further replaces total forced cost with q integer cost variables and explicit supporting-line constraints. The other classes remain nonempty by WellFormed; the modified class has the explicit empty-residual branch. The natural expression z_j-1 occurs only under z_j>=1, so a future integer-row translation must explicitly use that bound when replacing it by integer subtraction. This checkpoint proves the exact epigraph equivalence, but not yet its full CountInequality row generator, solver implementation, or bit complexity.

## Boundary and assumption checks

- Empty candidate sets: the count-basis theorem permits an empty output and states spanning only for candidate points. It does not claim a nonempty affine basis without a nonempty hypothesis.
- Counts zero or at class size: ordinary prefix epigraphs have an attaining line at both endpoints. Modified classes instead restrict the count to [1,m-1].
- Two-item modified class: the remaining index set is empty. Its zero cost is retained as a constant row after adding the forced-in item's weight.
- Ties: only monotonicity of weights is used, so repeated weights are permitted.
- Integer parity: epsilon is a Fin 2 coordinate, and the integer substituted variables are constrained through the original count bounds. No real relaxation replaces integer feasibility.
- Candidate validity is never folded into Tight. Count validation and support are distinct statements, as required by the frozen model.
- The rational-to-real independence bridge is specific to the matrix entries' field embedding; injectivity of an arbitrary rational-linear map alone would not justify it.
- Theorem assumptions include soundness and completeness of the linear-feasibility oracle. That is a conditional algorithm theorem, not an external solver certified merely because its contract has a name.

## Original cell contract instantiated by search

`oracle_cell_basis_selection` uses one bounded family of integer normal equations for all cells, and sets each output basis to the actual `basisSearch` expression. It proves the original `CellBasisSelection` containment and real spanning fields, adds real affine independence, bounds each basis by q+1 points, and bounds each cell's feasibility calls by 2(q+1)^2. The extrema family is exactly the supplied family, so two cells do not silently use inconsistent extrema. Both the attained-extrema input and sound/complete per-cell linear-feasibility inputs remain explicit. The theorem does not implement extrema computation or prove those solvers satisfy their contracts.

## Validity cannot use the tight-count oracle unchanged

The explicit `countRow` system contains the equation candidateValue=rhs, encoded by two inequalities. It correctly represents tight profiles and is appropriate for support, cells, and their linear subqueries. It cannot detect a violating feasible profile by merely appending candidateValue>=rhs+1: the original equality would make every such query infeasible. `invalid_iff_count_violation` is a separate semantic reduction and does not make this row-translation error. The complete recognition implementation must construct a feasible-prefix row system without the equality rows, then add the integer violation inequality. Keep `complete_algorithm_correctness=false` until this branch and the other outputs are assembled.
