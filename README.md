# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 17, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39004885856), source `c37a5e28cfb3d5e642d4608aa0aaeaac10f1745d`. The full project builds and **282 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound` only). No `sorryAx` or project axiom. Frozen model and targets are unchanged.

Here n is the item count and q counts candidate-coefficient classes, including a possible zero class.

| Obligation | Verified scope |
| --- | --- |
| Structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span |
| Count ILP | Explicit exact rows, 2q integer variables, exact parity substitution |
| Attained extrema | Actual maximum/minimum scans; at most 2(n+q)2^q calls |
| Cell search | Exact 3q cell rows; actual search supplies the original real affine-basis contract |
| Validity/support | Separate violation rows; sound original invalid/empty/supported branches |
| Exchange edges | Explicit forced rows, actual tight binary witnesses, exact finite adjacent-edge list |
| Computed matrix | At most n+(q+1)6^q rows; rational rank equals nonempty tight-set affine dimension plus one |
| Full dimension | Feasible binary points and their convex-hull polytope have full affine span and dimension n |
| Call accounting | Validity/support/extrema/cells: <=1+2*2^q+2(n+q)2^q+2(q+1)^2 6^q; <=n further edge calls |
| Complete algorithm | Still open: one returned certificate, actual tight-point basis, facet bridge and rank implementation |
| Full FPT time | Still open: normal bit bounds, costed linear algebra, ILP foundations and compression |

Row-solver soundness/completeness remain explicit theorem hypotheses; the solvers are not certified by defining their contracts. Normal generation still uses classical choice. A call count is not total runtime. The linear extrema scans and redundant exchange rows are documented variations of the manuscript implementation. Same-session review only; theorem counts are not completion percentages.

## Evidence and continuation

- Raw successful logs: `logs/verified_search_20261017/`.
- Source/artifact hashes: `docs/source_hashes_search_20261017.json`.
- Scope: `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Statement review: `docs/REVIEW_SEARCH_20261017.md`.
- Next: `docs/NEXT_AFTER_SEARCH_20261017.md`.
- Chinese report: `docs/PROGRESS_SEARCH_20261017.md`.
- Ledger: `docs/session_search_20261017.json`; active 40.25 minutes this round, cumulative recorded 182.38. Earlier unlogged preparation is unknown; session gaps are excluded.

Run `python3 scripts/environment_gate.py` for the eight verification commands. All earlier checkpoints remain preserved. Historical preparation comments in frozen files do not describe current acceptance. The original manuscript is `reference/mor34_fpt_proof.tex`.
