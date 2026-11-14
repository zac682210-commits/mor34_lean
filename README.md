# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin; v0.1 October 13, v0.2 October 19, 2026).

## Completed scope — October 18, 2026

**The newly contributed proofs and applications of established algorithms are complete in the declared mathematical reference cost model.** Established ILP, exact rank, Frank–Tardos, elementary arithmetic and sorting remain explicit local contracts, as requested. Their implementations and compiler/backend operational costs are outside scope.

[Verified source](https://github.com/zac682210-commits/mor34_lean/tree/8951a2f5c5a64a477e907991b7653698d11ec440) · [Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39146901961) · [Chinese completion report](docs/PROGRESS_EXECUTION_20261018.md) · [Cost model](docs/COST_MODEL_20261018.md)

**Source snapshot versus status documentation (clarified November 14, 2026).** The verified commit `8951a2f5c5a64a477e907991b7653698d11ec440` identifies the Lean source checked by CI. Its historical README and `docs/ACCEPTANCE.json` still describe earlier checkpoints; they are not the final status record. The completion record was added in [`e650b8c`](https://github.com/zac682210-commits/mor34_lean/commit/e650b8cadeb2c1bcb7081ece132983d18bf7cb1e), and the manuscript correspondence was added in [`294158b`](https://github.com/zac682210-commits/mor34_lean/commit/294158b4a2771580c5c9a0578cb370bd0c10f583). Those intervening commits change documentation and retained evidence, not Lean source. Use this development branch's README and [acceptance record](docs/ACCEPTANCE.json) for the current scope; use the verified source link for the compiled statements.

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

In the acceptance record, `complete_FPT_complexity`, `new_applications_complete`, and `new_paper_proofs_complete` are true **within this conditional scope**. The broader `complete_paper`, `complete_algorithm_correctness`, `full_self_contained_formalization_complete`, and `compiled_runtime_model_verified` flags remain false; they must not be read as unfinished new-proof obligations or changed to claims that the external primitive algorithms have been verified.

The cost model is a mathematical reference algorithm, not verified backend timing. The extrema implementation uses linear scans, preserving the claimed FPT class; manuscript v0.2 now states those scans, replacing v0.1's binary-search call count. The six-item illustrative example is not separately certified. This remains same-session verification, not independent peer review.

## Manuscript correspondence — October 19, 2026

[Detailed correspondence and unformalized external results (Chinese)](docs/PAPER_ALIGNMENT_20261019.md) · [Machine-readable declaration index](docs/paper_alignment_20261019.json) · [Reproducible manuscript v0.2 patch](reference/mor34_v0.2.patch).

The revised manuscript describes the actual linear extrema scans, finite augmented-normal search and retained-point rank extraction. The main FPT bounds and theorem numbering are unchanged. The original v0.1 files in `reference/` remain frozen snapshots; apply the patch as described in the correspondence report to obtain v0.2. The final theorems remain conditional on explicit established local algorithms; no efficient solver-independent implementation is claimed.

## Reproduce

Run `python3 scripts/environment_gate.py` with the pinned Lean toolchain and Mathlib dependency. The CI workflow uses this same script. Logs are retained in `logs/verified_execution_20261018/`; artifact and source hashes are in `docs/execution_verified_metadata.json` and `docs/source_hashes_execution_20261018.json`.

Development branch: `codex/mor34-formalization`. No merge, release or external publication is part of this update. Historical checkpoints remain for traceability; `docs/ACCEPTANCE.json` is authoritative for current scope.

Recorded active work this execution: 96.93 minutes; cumulative recorded active work: 645.96 minutes. Unrecorded earlier preparation is not retroactively estimated. See `docs/session_execution_20261018.json`.
