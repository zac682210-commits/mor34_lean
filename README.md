# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Scope and verified checkpoint — October 18, 2026

**Current scope: newly contributed proofs and applications of established tools.** ILP, exact rational rank and Frank–Tardos internals, and compiler-backend costs are excluded by the user's instruction. Their mathematical conclusions remain explicit external contracts.

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39113325809), source `e7c2ab38c192b515f54c02d8963f9c038748de74`. Nine commands pass; **662 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` or project axiom. Fifteen runtime smoke checks pass. Frozen model/targets unchanged.

| Scope | Status |
| --- | --- |
| New structure and correctness | Pairing, exchanges, quotient dimensions, affine cells, full augmented span and original-input output verified relative to solver specifications |
| Component corollary | C≤(3q+1)2^q for actual components; original K wrapper checked |
| Compression application | Feasible/tight sets, validity, geometry, complete output and K preserved; ≤18(n+1)^4 payload |
| Cost ingredients | Actual ILP quartic payload; rank quadratic payload and actual ordered-list call bound; counted solver composition and explicit parameter factors |
| Remaining in scope | Complete mathematical reference-algorithm phase-cost combination for the FPT time theorem |
| Outside scope | Reimplementing established primitives and verifying compiled runtime costs |

`complete_FPT_complexity` and `complete_paper` remain false. Compression cost substitution does not discharge its assumed total-cost premise. The implemented extrema scan differs from the paper's sharper binary-search call expression. The six-item illustration is not separately certified. Same-session review only; theorem counts are not completion percentages.

## Evidence and continuation

- Logs: `logs/verified_newproofs_20261018/`.
- Source/artifact hashes: `docs/source_hashes_newproofs_20261018.json`.
- Scope: `docs/SCOPE_NEW_PROOFS_20261018.md`, `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Review: `docs/REVIEW_NEW_PROOFS_20261018.md`.
- Next: `docs/NEXT_NEW_PROOFS_20261018.md`.
- Chinese report: `docs/PROGRESS_NEW_PROOFS_20261018.md`.
- Ledger: `docs/session_newproofs_20261018.json`; 40.20 active minutes this round, 385.80 cumulative recorded minutes. Earlier unlogged preparation unknown.

Run `python3 scripts/environment_gate.py` for the nine-command gate. Earlier checkpoints and legacy interfaces are preserved. Reference manuscript: `reference/mor34_fpt_proof.tex`.
