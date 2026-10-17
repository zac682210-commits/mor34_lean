# Next stage after exact encoding and query-bounded basis search

Use ACCEPTANCE.json for the verified commit; this document is a task plan, not proof evidence.

## What has moved forward

The count epigraph now has explicit rational rows, exact integer equivalence, parity substitution, and exact variable/constraint counts. The growing count-basis procedure has been defined and analyzed relative to a sound and complete linear-feasibility solver. Its normal families are proved to exist, and the real-affine contract is connected through augmented spans.

The recursive procedures are executable when their inputs are executable. The chosen normal families still use classical finite-dimensional bases. There is no verified bound yet on the time to generate them or the bit lengths of their coefficients. Therefore this checkpoint must not be advertised as an executable FPT implementation.

## Global adjacent-edge reduction and remaining row translation

For an actual adjacent pair u<v in one sorted coefficient class, let R be the remaining indices after deleting u and v. Order R by the inherited order and enumerate it increasingly. At a forced class count t with 1<=t<=m-1, the minimum class cost is

    weight(v) + prefixCost(remaining weights, t-1).

The local lemmas in RestrictedPrefix.lean and ForcedPairPrefix.lean now establish the following three facts. Reuse them when assembling the global model:

1. Every set omitting u and containing v is obtained by inserting v into a subset of R, and its count and cost are the residual count plus one and the residual cost plus weight(v).
2. Prefix-minimality for the inherited sorted order gives the minimum-cost realization. The produced witness is an actual binary set and satisfies the required pair pattern.
3. The residual prefix has an epigraph formulation. If R is empty, its cost is the constant zero and the only admissible forced count is one; do not call the nonempty-class slope theorem on an empty residual class.

`ExchangeEncoding.lean` now assembles those fibers, proves preservation of counts and global minimum cost, and gives `exchange_iff_forced_epigraph` for the original predicate. The witness is the concrete forcedSet.

**Next unfinished step:** convert ForcedEpigraph to an explicit CountInequality row family and instantiate its solver contract. Under 1<=z_j, rewrite the natural truncated subtraction cast as integer z_j-1. Include the constant cost row if the residual class is empty; avoid silently dropping this row. Then connect edge decisions and witnesses to the component computation.

## Assembly obligations

- Instantiate the one-extra-inequality solver for actual cells using exact_parity_linear_count_encoding. The solver contract must remain explicit until an ILP implementation is certified.
- Prove extrema search returns attained extrema in the same full parity class. Existing classical extrema existence is not a verified binary-search implementation.
- The original CellBasisSelection is now instantiated by oracle_cell_basis_selection. Supply its attained-extrema and per-cell linear-solver inputs; preserve their explicit correctness contracts.
- Assemble the retained matrix and return dimension, separating invalid inequality, empty equality level, and nonempty cases.
- Replace exchange directions by their two actual tight witnesses when returning an affine basis of original binary points.
- Prove the knapsack polytope has full dimension from 0 and the feasible unit vectors before concluding facetness from dimension n-1.

## Complexity obligations

The query count is not total runtime. It excludes linear algebra for normals, exact rank computation, extrema-query bookkeeping, oracle execution, and input/output encoding. Preserve separate flags for structural proof, relative algorithm correctness, coefficient bit bounds, and full FPT complexity. Do not add unproved algorithm foundations as project axioms.

## Timing and continuation

Read the newest session JSON before extending the time ledger. Accumulate only actual work; do not infer duration from the gap between commits or turns. Earlier preparation before the ledger remains unknown.

## Explicit rows for the next exchange-solver step

For the forced class j, write w_v for the forced-in weight, and let r_a be the a-th remaining item after removing u,v. On the admissible domain 1<=z_j<=m_j-1, the local line is

    w_v + F_R(a) + (z_j - 1 - a) w_(r_a) <= y_j.

Thus its explicit row is

    w_(r_a) z_j - y_j <= (a+1) w_(r_a) - F_R(a) - w_v.

The natural subtraction cast must first be rewritten using z_j>=1. Replace the forced class's ordinary count bounds by -z_j<=-1 and z_j<=m_j-1. Keep the original candidate equality and total-capacity row, and ordinary prefix lines for all other classes.

A simple uniform representation can always add the row -y_j<=-w_v. In the zero-residual case it is essential. In the nonempty case it is redundant because weights are positive and residual counts nonnegative; prove this before adding it unconditionally. There are n-2 remaining slope rows and one such constant row, hence n+2q+r+2 total rows with 2q integer variables, if the two original count-bound rows are replaced rather than supplemented. This count is a derived plan, **not yet a Lean theorem**. It avoids a dependent row type that changes at m_j=2.

Input-coefficient growth also remains to be formalized: ordinary constants w_t*t-F(t) and forced constants (a+1)w_(r_a)-F_R(a)-w_v use at most n input-weight terms. Parity substitution doubles count coefficients and subtracts one sum of at most q coefficients from each bound. These observations specify the arithmetic whose bit sizes must be bounded; they are not a certified runtime result.

## Extrema implementation: a simpler route preserving the FPT target

Pinned-source inspection found `Nat.findGreatest` and its specification in `Mathlib/Data/Nat/Find.lean`. A repository-wide text search for binary-search names found utility/meta uses, but no directly reusable generic oracle-call theorem. This is a search observation, not a claim that no such theorem exists elsewhere.

The theorem's FPT target does not require logarithmically many extrema queries. A descending linear scan of each class's m_j+1 thresholds uses polynomially many queries and can be simpler to formalize. For maxima, ask whether a feasible same-parity count satisfies z_j>=k, scanning k=m_j down to zero. The first successful witness attains the maximum: failure at all larger thresholds excludes a larger coordinate, while the returned witness is >=k. For minima, scan upper-bound thresholds upwards, or reflect the coordinate. Nonempty parity classes guarantee success at an endpoint.

Scanning both directions for every class uses at most 2*sum_j(m_j+1)=2(n+q) calls per nonempty parity class, hence at most 2(n+q)2^q across all classes. This is still compatible with 2^{O(q log(q+1))} poly(n,L); it only changes a polynomial factor and the exact procedure from the manuscript's binary-search implementation. This derivation is **not yet Lean-checked**. If used, state the implementation variation openly and prove the scan's witness and call-count properties, rather than claiming a verified binary search. It avoids spending time proving a logarithmic bound that the main parameterized theorem does not need.

## Important validity-branch row distinction

Do not instantiate invalidity checking with `countRow` unchanged: it imposes candidateValue=rhs. Remove its two candidate-equality rows and instead add

    -sum_j coefficient_j * z_j <= -(rhs+1).

The resulting feasible-prefix violation formulation has 2q integer variables and n+2q+2 inequalities (before additional restrictions). Its equivalence should follow from prefix_feasible_epigraph, integer count conversion, and invalid_iff_count_violation. Support checking can use the original tight formulation. The semantic invalidity reduction has already been checked; this explicit violation-row family has not. This distinction prevents an invalid candidate from being incorrectly accepted because a contradictory tight-and-violating query always returns infeasible.

## A bounded-normal replacement for the current classical normal choice

For a selected augmented count matrix with entries bounded in absolute value by n+1, choose an r-by-r nonsingular pivot minor, where r<=q+1. For each free column, set its free coordinate to the pivot determinant and all other free coordinates to zero; choose pivot coordinates using minus the adjugate times that column. Cramer's-rule identities identify these coordinates with signed r-by-r minors. Every coefficient is thus bounded by r!*(n+1)^r, giving an explicit O(r log(r(n+1))) bit bound. Free coordinates form a nonzero diagonal block, so the q+1-r normals are independent and span the annihilator. For r=0 use standard coordinate normals; for r=q+1 the list is empty.

This is a mathematical construction plan, not a proved property of the currently selected quotient-basis normals. Those existing normals may have uncontrolled denominators. The bounded replacement needs new Lean existence lemmas for the pivot minor, the adjugate/kernel equations, and the determinant bound, followed separately by an operation-counted elimination implementation if claiming total runtime.

The bounded-normal theorem must add the hypothesis that every selected count coordinate is <=n. The current generic normal theorem allows arbitrary finite subsets of natural count vectors, so a uniform n-dependent coefficient bound cannot be appended without that hypothesis. In the actual cell search, containment in the tight bounded-profile set supplies it. Pinned Mathlib APIs `Matrix.mul_adjugate` and `Matrix.adjugate_mul` are in `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`; the elementary determinant magnitude estimate can be derived from the permutation-sum definition if a suitable bound is unavailable.
