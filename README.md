# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 17, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39008232389), source `0f93ca83fdc01aea389c1a5fbf969799d092c794`. All eight gates pass; **356 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound` only). No `sorryAx` or project axiom. Frozen model and targets are unchanged.

The normalized-input output contract is now proved: invalid candidates return a binary counterexample; valid empty faces have dimension -1; supported faces return their dimension, a geometric facet decision and a searched affine basis of actual tight binary points. This is relative to explicit integer-feasibility and exact-rank contracts. Normal forms are still classically chosen.

| Obligation | Verified scope |
| --- | --- |
| Structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span |
| Count/exchange ILP | Exact explicit integer rows, parity substitution, actual extrema and exchange witnesses |
| Actual point basis | Small returned tight-point family, rank-guided extraction, independence, full spanning and exact cardinality |
| Geometry | Supporting equality face is the hull of tight points; convexity, extremeness, full ambient dimension and codimension-one facet/rank equivalence |
| One output record | Correct invalid/empty/supported outcomes, signed dimension and actual binary affine basis |
| Bounded normals | Original-column nonsingular minor existence for independent rows; given a pivot block, explicit integer kernel basis and logarithmic coefficient-bit bound |
| Parameter | q<=K+1 for actual distinct positive coefficients on normalized items |
| Remaining | General bounded normal generator, original-input preprocessing, executable/costed rank and ILP, full FPT theorem and compression |

The rank and ILP contracts are assumptions, not verified implementations. The bounded pivot normals have not yet replaced the older unrestricted classical normal choice. Call counts are not total runtime. Same-session review only; theorem counts are not completion percentages. `complete_paper` and `complete_FPT_complexity` remain false.

## Evidence and continuation

- Exact successful logs: `logs/verified_basis_20261017/`.
- Source/artifact hashes: `docs/source_hashes_basis_20261017.json`.
- Scope: `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Statement review: `docs/REVIEW_BASIS_20261017.md`.
- Next: `docs/NEXT_AFTER_BASIS_20261017.md`; detailed integration plan: `docs/PIVOT_INTEGRATION_PLAN_20261017.md`.
- Chinese report: `docs/PROGRESS_BASIS_20261017.md`.
- Ledger: `docs/session_basis_20261017.json`; active 41.35 minutes this round, cumulative recorded 223.74. Earlier unlogged preparation is unknown; session gaps are excluded.

Run `python3 scripts/environment_gate.py` for all eight verification commands. Earlier checkpoints remain preserved. Historical comments in frozen preparation files do not describe current acceptance. The original manuscript is `reference/mor34_fpt_proof.tex`.
