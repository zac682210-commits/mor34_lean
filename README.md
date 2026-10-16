# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint (October 17, 2026, Asia/Shanghai)

[Successful CI run](https://github.com/zac682210-commits/mor34_lean/actions/runs/38931568115), commit `1ab49f5e6de4be6ad59dd31c2f34f09ebdbc6211`: the project compiles and **73 named theorems pass the transitive axiom audit**. The frozen model and original target declarations are unchanged.

| Paper obligation | Verified declarations |
| --- | --- |
| Prefixes retain counts and minimize weight | `counts_prefixSet`, `prefixMinimality`, `prefix_tight` |
| Lemma 2: exchange closure and interval components | `intervalExchange`, `connected_iff_cuts`, `componentLabel_interval` |
| Lemma 4: parity forces interior exchanges and connectivity | `pairingAtCut`, `interiorExchange`, `parity_interior_connected` |
| Lemma 3: actual exchange span equals kernel | `exchangeDirectionSpan_eq_ker` |
| Lemma 3: exchange dimension n-C | `exchangeDirectionSpan_finrank` |
| Lemma 3: tight points and prefixes have the same component image | `tight_image_eq_prefix_image` |
| Lemma 3: real affine-dimension identity | `tight_dimension_quotient` |

No `sorryAx` or project-specific axiom occurs in their transitive dependencies. The allowed standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is actual Lean checking, not an independent audit. Auxiliary-theorem counts are not a completion percentage.

**The complete paper theorem is not yet formalized.** Remaining: Lemma 5's actual parity-cell affine maps and cell count, the augmented span theorem, rational/real rank bridge, algorithm correctness, and FPT complexity. The component quotient is currently noncomputable mathematical infrastructure; it is not a certified executable recognition algorithm.

## Verification

Run `python3 scripts/environment_gate.py` from the repository root with elan and Python installed. GitHub Actions runs the same sequence on development-branch pushes: Lean startup, core theorem, Mathlib import, project build, and the named theorem axiom dependencies printed by `Check.lean`.

Raw successful output is retained in `logs/verified_structural_20261017/`; `docs/source_hashes_structural_20261017.json` records source and artifact hashes. Earlier evidence is preserved. Historical comments in initial preparation files do not describe the current verified status. Proposition definitions in `Targets.lean` and `PaperInterface.lean` are not counted as proofs.

## Reading and resuming

- `docs/source_map.json`: paper-to-formalization obligations and completion status.
- `docs/REVIEW_COMPONENTS_20261017.md`: mathematical statement correspondence.
- `docs/NEXT_AFFINE_CELLS.md`: precise next proof obligation, including required links to actual parity cells.
- `docs/session_20261016.json`, `session_core_20261016.json`, `session_structural_20261017.json`: actual-work ledger; inter-session idle time excluded.
- `reference/mor34_fpt_proof.tex`: reference manuscript.

The main new modules are `Components.lean`, `PrefixMinimality.lean`, `PartitionKernel.lean`, `ExchangeKernel.lean`, `TightDimension.lean`, and `PrefixQuotient.lean` under `MOR34/`.
