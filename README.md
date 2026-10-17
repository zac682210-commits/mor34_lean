# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 17, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39013099048), source `4fa9921b96a39227868c5957b0f6491eb9f05491`. All eight commands pass; **426 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`). No `sorryAx` or project axiom. Frozen model and targets unchanged.

The preferred `boundedPipeline` returns the verified normalized output contract while using bounded integer affine equations in every cell search. Its output includes invalid witnesses, signed empty-face dimension, supported-face dimension/facet decision and a searched affine basis of actual tight binary points. Explicit correct ILP and exact-rank solvers remain assumed.

| Scope | Status |
| --- | --- |
| Structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span proved |
| Normal equations | Arbitrary finite count selections; complete zero-set description and coefficient-bit bound proved |
| Actual recursive searches | Bounded family integrated; all intermediate states, strict query offsets and parity substitution bounded |
| Normalized output | Full solver-relative invalid/empty/supported output contract proved |
| Pivot enumeration | Sound/complete finite search with at most d^r attempts, relative to determinant evaluator |
| Original input | Grouping/sorting existence, item bijection, feasible/tight/valid predicate preservation, raw parameter and computed signed tight-face dimension transport proved |
| Still open | Complete raw output/basis/facet wrapper; executable normal generation; total encoding and cost model; primitive rank/ILP and full FPT/compression foundations |

The bounded normal family still uses classical row/pivot choices; the finite pivot search is not yet the generator. Call counts and coefficient sizes do not establish total runtime. `complete_paper`, `complete_algorithm_correctness`, and `complete_FPT_complexity` remain false. This is same-session review; theorem counts are not completion percentages.

## Evidence and continuation

- Exact logs: `logs/verified_normals_20261017/`.
- Source/artifact hashes: `docs/source_hashes_normals_20261017.json`.
- Scope: `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Review: `docs/REVIEW_NORMALS_20261017.md`.
- Next: `docs/NEXT_AFTER_NORMALS_20261017.md`.
- Chinese report: `docs/PROGRESS_NORMALS_20261017.md`.
- Ledger: `docs/session_normals_20261017.json`; 40.18 active minutes this round, 263.92 cumulative recorded minutes. Older unlogged preparation is unknown.

Run `python3 scripts/environment_gate.py` for the eight verification commands. Earlier checkpoints are preserved. Historical comments in frozen files do not describe current acceptance. Reference manuscript: `reference/mor34_fpt_proof.tex`.
