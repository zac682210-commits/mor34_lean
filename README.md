# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint — October 17, 2026

[Successful CI](https://github.com/zac682210-commits/mor34_lean/actions/runs/39001241694), source commit `4f88fe34dac90c933406986163f5f3cd634d8d07`. The entire project builds, and all **201 named theorems** pass the transitive axiom allowlist. No `sorryAx` or project axiom. Standard axioms allowed: `propext`, `Classical.choice`, `Quot.sound`. Frozen model and target files are unchanged.

Here n is the number of items, q is the number of distinct candidate-coefficient classes including a possible zero class, and r is the number of added rational linear inequalities.

| Obligation | Verified scope |
| --- | --- |
| Main structural proof | Pairing, exchange kernel, quotient dimension, affine cells, augmented span |
| Concrete integer certificate | At most n+(q+1)6^q rows; rational rank equals nonempty tight-set affine dimension plus one |
| Count ILP formulation | Exact equivalence, 2q integer variables, n+2q+r+3 inequalities; explicit parity substitution |
| Count basis search | Real affine independence and spanning, <=q+1 output points, <=2(q+1)^2 feasibility calls under explicit linear-solver contract |
| Cell-selection bridge | Original CellBasisSelection built from recursive search, conditional on attained extrema and sound/complete cell solvers |
| Integer normals | Bounded normal family proved to exist by quotient coordinates and denominator clearing |
| Validity/support | Exact reductions to original count prefixes and tight epigraph feasibility |
| Exchange reduction | Global witness, minimum cost, exact epigraph equivalent to original Exchange; empty residual set handled |
| Complete recognition procedure | Still open: edge-row translation, solver/cell/extrema assembly and outputs |
| Full FPT time | Still open: normal-generation bit cost, ILP foundations, compression and total runtime |

The count-basis theorem uses classical choices for normals. A logical oracle-call bound is **not** a verified executable FPT runtime. This remains a same-session statement review, not independent peer review. Theorem counts are not completion percentages.

## Evidence and continuation

- Raw successful logs: `logs/verified_encoding_20261017/`.
- Source/artifact hashes: `docs/source_hashes_encoding_20261017.json`.
- Current scope: `docs/ACCEPTANCE.json` and `docs/source_map.json`.
- Statement review: `docs/REVIEW_ENCODING_20261017.md`.
- Next step: `docs/NEXT_AFTER_ENCODING_20261017.md`.
- Chinese progress report: `docs/PROGRESS_ENCODING_20261017.md`.
- Time ledger: `docs/session_encoding_20261017.json`; this session 40.28 active minutes, cumulative recorded 142.14. Earlier unlogged preparation is unknown; gaps between sessions are excluded.

Run `python3 scripts/environment_gate.py` to execute the eight verification commands. Previous successful checkpoints and raw logs are preserved. Historical preparation comments are not the current acceptance status. The original manuscript is `reference/mor34_fpt_proof.tex`.
