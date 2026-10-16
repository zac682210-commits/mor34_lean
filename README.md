# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint (October 16, 2026)

[Successful CI run](https://github.com/zac682210-commits/mor34_lean/actions/runs/38919230112), commit `8ac25e0cc6a5c28693b4f05c34e4bfff222896aa`: the project compiles and 24 named theorems pass the transitive axiom audit. The central results are:

- `MOR34.pairingAtCut`: exact frozen `PairingAtCutGoal`, including full coordinatewise parity and both outputs crossing the specified cut.
- `MOR34.intervalExchange`: paper Lemma 2's edge-closure assertion.
- `MOR34.interiorExchange`: paper Lemma 4's adjacent-cut assertion, exact frozen `InteriorExchangeGoal`.

No `sorryAx` or project-specific axiom occurs in their dependencies. The admitted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is actual Lean checking, not an independent proof audit.

**The complete paper theorem is not yet formalized.** Graph-component consequences, prefix minimality, quotient dimension, affine cells, algorithm correctness, and FPT complexity remain open. Counts of auxiliary theorems are not a completion percentage.

## Verification

Run `python3 scripts/environment_gate.py` from the repository root with elan and Python installed. GitHub Actions runs the same sequence on development-branch pushes. It checks Lean startup, a core-only theorem, Mathlib import, project build, and the axiom dependencies printed by `Check.lean`.

Raw successful output is retained in `logs/verified_core_20261016/`; `docs/source_hashes_core_20261016.json` records the source and artifact hashes. The older four-theorem evidence is preserved separately. Historical comments in the original preparation modules and the raw gate JSON's old scope label are superseded by this precise checkpoint description; the raw logs have not been rewritten.

`Targets.lean` and `PaperInterface.lean` contain proposition specifications. Compiling a proposition definition is not a proof; consult `docs/source_map.json` for the theorem implementing each completed target.

## Layout

- `MOR34/Model.lean`: grouped model, feasibility, equality levels, prefixes and exchanges.
- `MOR34/PrefixTools.lean`, `BalancedSplit.lean`, `ClassPairing.lean`: finite-set constructions.
- `MOR34/PairingAtCut.lean`: assembly across all coefficient classes.
- `MOR34/Exchange.lean`: feasibility-preserving swaps and interval edge closure.
- `MOR34/Accounting.lean`, `InteriorExchange.lean`: conservation identities and the parity-interior conclusion.
- `docs/FORMALIZATION_SCOPE.md`: paper alignment and outstanding obligations.
- `docs/session_20261016.json`, `docs/session_core_20261016.json`: actual-work time ledger.
- `reference/mor34_fpt_proof.tex`: mathematical reference manuscript.
