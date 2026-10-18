# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 18, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39098124607), source `16228d3a902a737a3d94a14cda9da53e668c1521`. All eight commands pass; **523 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`). No `sorryAx` or project axiom. Frozen model and targets unchanged.

`original_input_output_contract` now starts from the original integer data and paper hypotheses, normalizes it, runs the bounded pipeline and returns a correct original-coordinate output. Explicit correct ILP and exact-rank primitives remain assumed.

| Scope | Status |
| --- | --- |
| Structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span proved |
| Original-input output | Invalid witness, empty-face dimension −1, supported-face dimension, geometric facet decision, tight-point affine basis proved relative to solvers |
| Query encoding | Actual count/parity/forced/violation rows have integer bounds; dense coefficient payload bounded, including every recursive cell-search state |
| Small determinant | Concrete recursive evaluation, exact pivot search, arithmetic trace and intermediate partial-sum bits proved |
| Still open | Executable normalization/normal generator, complete serialization and cost composition, primitive rank/ILP implementations, full FPT/compression foundations |

Classical choices remain. The concrete pivot search is not yet the bounded normal generator. Dense payload sizes exclude wire-format headers; arithmetic-operation charges do not establish bit runtime. The extrema implementation uses finite scanning, not the paper's sharper binary-search call bound. `complete_paper`, unconditional `complete_algorithm_correctness`, and `complete_FPT_complexity` remain false. Same-session review only; theorem counts are not completion percentages.

## Evidence and continuation

- Exact logs: `logs/verified_raw_20261018/`.
- Source/artifact hashes: `docs/source_hashes_raw_20261018.json`.
- Scope: `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Review: `docs/REVIEW_RAW_20261018.md`.
- Next: `docs/NEXT_AFTER_RAW_20261018.md`.
- Chinese report: `docs/PROGRESS_RAW_20261018.md`.
- Ledger: `docs/session_raw_20261018.json`; 40.05 active minutes this round, 303.97 cumulative recorded minutes. Older unlogged preparation is unknown.

Run `python3 scripts/environment_gate.py` for the eight verification commands. Earlier checkpoints are preserved. Historical comments in frozen files do not describe current acceptance. Reference manuscript: `reference/mor34_fpt_proof.tex`.
