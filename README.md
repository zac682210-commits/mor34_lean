# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint (October 16, 2026)

[Successful CI run](https://github.com/zac682210-commits/mor34_lean/actions/runs/38916719328), commit `16888b3874da42274d9287f9731d6c67a61c0f8e`: the project compiles and four named theorems pass the axiom audit, including `MOR34.balancedSplit`. No `sorryAx` or project-specific axiom occurs in their transitive dependencies. The admitted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Original source comments about unchecked preparation scripts describe the prior checkpoint; current evidence is recorded here and in `docs/ACCEPTANCE.json`. The raw gate JSON retains an older scope label mentioning only three arithmetic scripts; the actual axiom log and allowlist also include `balancedSplit`.

## Verification

Run `python3 scripts/environment_gate.py` from the repository root with elan and Python installed. GitHub Actions runs the same gate sequence on development-branch pushes. It checks Lean startup, a core-only theorem, Mathlib import, the project build, and the axiom dependencies printed by `Check.lean`.

See `docs/ACCEPTANCE.json` for the recorded verification scope and `docs/FORMALIZATION_SCOPE.md` for the connection between the first finite-set theorem and the paper. Definitions in `MOR34/Targets.lean` and `MOR34/PaperInterface.lean` specify open goals; successfully compiling those definitions is not a proof of those goals.

The full paper theorem and its FPT running-time bound are not yet formalized. No claim of an independent formal proof audit is made.

## Layout

- `MOR34/Model.lean`: coefficient classes, feasibility, equality levels, prefixes and exchanges.
- `MOR34/PairingArithmetic.lean`: three arithmetic lemmas.
- `MOR34/BalancedSplit.lean`: finite-set equal split with prescribed pairs.
- `MOR34/Targets.lean`, `MOR34/PaperInterface.lean`: remaining specifications.
- `docs/source_map.json`: paper-to-formalization obligations.
- `reference/mor34_fpt_proof.tex`: mathematical reference manuscript.
