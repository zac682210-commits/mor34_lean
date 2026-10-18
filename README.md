# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Scope and verified checkpoint — October 18, 2026

**Current scope: newly contributed proofs and applications of established tools.** ILP, exact rational rank and Frank–Tardos internals, sorting, and compiler-backend costs are excluded. Their conclusions remain explicit external contracts.

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39132112914), source `db3c7304a794a15024422d0587468255031210db`. Nine commands pass; **910 named declarations** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` or project axiom. Fifteen existing runtime smoke checks pass. Frozen model/targets unchanged.

| Scope | Status |
| --- | --- |
| New structure and correctness | Pairing, exchanges, quotient dimensions, affine cells and full augmented span checked |
| Original-input output | Dimension, facet decision and returned basis checked using one generic dense integer solver and exact rank |
| Component corollary | `C≤(3q+1)2^q` for actual components; original K wrapper checked |
| Compression application | Feasible/tight sets, validity, geometry, output and K preserved; `≤18(n+1)^4` payload |
| Concrete request costs | Retained residual reads, evaluated integer arrays, parity transform, row enumeration, actual size and local solver cost checked |
| Bit-cost ingredients | All AST intermediate sizes and weighted evaluation bound checked; full caller substitution remains |
| Remaining in scope | One phase-complete FPT time derivation, including preprocessing and output data movement |

`complete_FPT_complexity` and `complete_paper` remain false. Compression conditional on a total-cost premise is not a completed runtime proof. The implemented extrema scan is linear, not the manuscript's sharper binary-search call expression. The six-item illustration is not separately certified. Same-session review only; theorem counts are not completion percentages.

## Evidence and continuation

- Logs: `logs/verified_dense_20261018/`.
- Source/artifact hashes: `docs/source_hashes_dense_20261018.json`.
- Scope: `docs/SCOPE_NEW_PROOFS_20261018.md`, `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Review: `docs/DENSE_PIPELINE_REVIEW_20261018.md`.
- Next: `docs/NEXT_DENSE_20261018.md`.
- Chinese report: `docs/PROGRESS_DENSE_20261018.md`.
- Ledger: `docs/session_dense_20261018.json`; 41.43 active minutes this round, 508.99 cumulative recorded minutes. Earlier unlogged preparation remains unknown.

Run `python3 scripts/environment_gate.py` for the nine-command gate. Earlier checkpoints and legacy interfaces are preserved. Reference manuscript: `reference/mor34_fpt_proof.tex`.
