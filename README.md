# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

## Completed scope — October 18, 2026

**The newly contributed proofs and applications of established algorithms are complete in the declared mathematical reference cost model.** Established ILP, exact rank, Frank–Tardos, elementary arithmetic and sorting remain explicit local contracts, as requested. Their implementations and compiler/backend operational costs are outside scope.

[Verified source](https://github.com/zac682210-commits/mor34_lean/tree/8951a2f5c5a64a477e907991b7653698d11ec440) · [Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39146901961) · [Chinese completion report](docs/PROGRESS_EXECUTION_20261018.md) · [Cost model](docs/COST_MODEL_20261018.md)

Nine commands pass; **1154 named declarations** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or custom project axiom. Fifteen existing runtime smoke checks pass. The downloaded artifact digest, dependency manifest, remote source blobs and three frozen model/target files have been checked.

| Mathematical scope | Result |
| --- | --- |
| New structural proofs | Pairing, feasible exchanges, quotient dimension, affine cells and full augmented span |
| Original output | Validity witness, empty-face convention, dimension, facet decision and tight affine basis |
| Additional corollary | Actual exchange-component bound `C <= (3q+1)2^q` |
| Whole reference execution | Recognition, support/extrema/cells, normal matrices, integer requests, exchanges, rank and output relabeling |
| FPT application | Explicit `(K+7)^(C*(K+1)) (n+L+2)^e`, with fixed input exponent |
| Compression | Two actual FT calls and normalization; original parameter and output preserved |
| Unit-cost consequence | Magnitude-independent arithmetic-operation bound, under the standard strongly polynomial FT contract |

Start with `MOR34/CompleteCompressedExecution.lean` and `MOR34/StrongPreparationCost.lean`, then follow `docs/source_map.json`. `MOR34/WeightedRunInterface.lean` lists the local primitive contracts. There is no assumption of a total core or whole-program runtime.

The cost model is a mathematical reference algorithm, not verified backend timing. The extrema implementation uses linear scans, preserving the claimed FPT class; it does not claim the manuscript's binary-search call count. The six-item illustrative example is not separately certified. This remains same-session verification, not independent peer review.

## Reproduce

Run `python3 scripts/environment_gate.py` with the pinned Lean toolchain and Mathlib dependency. The CI workflow uses this same script. Logs are retained in `logs/verified_execution_20261018/`; artifact and source hashes are in `docs/execution_verified_metadata.json` and `docs/source_hashes_execution_20261018.json`.

Development branch: `codex/mor34-formalization`. No merge, release or external publication is part of this update. Historical checkpoints remain for traceability; `docs/ACCEPTANCE.json` is authoritative for current scope.

Recorded active work this execution: 96.93 minutes; cumulative recorded active work: 645.96 minutes. Unrecorded earlier preparation is not retroactively estimated. See `docs/session_execution_20261018.json`.
