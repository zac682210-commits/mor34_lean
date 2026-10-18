# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 18, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39101838969), source `27fe8ef3c050f91d3c81b2e39557dceee07a04a4`. All nine commands pass; **591 named theorems** pass the transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`). No `sorryAx` or project axiom. Fifteen separate runtime smoke checks pass. Frozen model and targets unchanged.

`executable_original_input_output_contract` uses computed raw grouping and sorting, finite integer normal search, deterministic support and returned-point enumeration, and rank-guided affine-basis extraction. Output is in original item coordinates. **Correct ILP and exact-rank primitives remain explicit assumptions.**

| Scope | Status |
| --- | --- |
| Structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span proved |
| Original-input output | Invalid witness, empty signed dimension, supported dimension, geometric facet decision, tight-point affine basis proved relative to solvers |
| Executable data path | Raw normalization, normal generator, support/returned-point enumeration, normalized output and relabeling compile as computable definitions |
| Cost components | Candidate-check accounting, recursive row payloads, determinant and annihilation intermediate bits proved |
| Still open | Operational costs of stored intermediate tables and complete bit-cost composition; primitive ILP/rank algorithms and compression foundations |

A mathematical call recurrence does not by itself bound callback invocations in compiled code: function-valued intermediates may need explicit materialization. Runtime smoke checks establish finite executions, not runtime complexity. Extrema use finite scanning, not the paper's sharper binary-search expression. `complete_paper`, unconditional `complete_algorithm_correctness`, and `complete_FPT_complexity` remain false. Same-session review only; theorem counts are not completion percentages.

## Evidence and continuation

- Logs: `logs/verified_executable_20261018/`.
- Source/artifact hashes: `docs/source_hashes_executable_20261018.json`.
- Scope: `docs/ACCEPTANCE.json`, `docs/source_map.json`.
- Review: `docs/REVIEW_EXECUTABLE_20261018.md`.
- Next: `docs/NEXT_AFTER_EXECUTABLE_20261018.md`.
- Chinese report: `docs/PROGRESS_EXECUTABLE_20261018.md`.
- Ledger: `docs/session_executable_20261018.json`; 41.63 active minutes this round, 345.60 cumulative recorded minutes. Older unlogged preparation is unknown.

Run `python3 scripts/environment_gate.py` for all nine commands. Earlier checkpoints and legacy interfaces are preserved. Reference manuscript: `reference/mor34_fpt_proof.tex`.
