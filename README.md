# MOR34 Lean formalization

Lean 4.19.0 formalization of *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges* (Zhiyan Lin, October 13, 2026).

Development branch: `codex/mor34-formalization`.

## Verified checkpoint (October 17, 2026, Asia/Shanghai)

[Successful CI run](https://github.com/zac682210-commits/mor34_lean/actions/runs/38937836257), commit `859936cd9876dd9b696e5112eb5a0d6cc0b033ed`: **119 named theorems pass the transitive axiom audit**, and the entire project builds. Frozen Model/Targets/PaperInterface files are unchanged.

The main structural endpoint is `small_retained_matrix`: for every well-formed grouped instance with nonempty tight set T, there exists a finite integer matrix with at most n+(q+1)6^q rows and n+1 columns whose rational rank equals dim(aff(T))+1. Here n is the number of items, q is the number of distinct candidate-coefficient classes (including a possible zero class), and T is the set of feasible binary points satisfying the candidate equality. Its rows are actual retained tight prefixes and actual adjacent exchange directions. Validity is checked separately by the future recognition algorithm.

| Paper obligation | Status |
| --- | --- |
| Prefix counts and minimum weight | Checked |
| Lemma 2: interval exchange components | Checked |
| Lemma 3: kernel, quotient and dimension identities | Checked |
| Lemma 4: parity-forced interior exchanges | Checked |
| Lemma 5: actual affine cells, cover and 6^q count | Checked |
| Theorem 8: augmented span and concrete retained matrix rank | Checked structural proof |
| Small count generators, at most q+1 per cell | Existence checked; construction algorithm open |
| Rational/real matrix rank and augmented affine dimension | Checked |
| Full recognition algorithm and empty/invalid branches | Open |
| FPT runtime and Frank–Tardos compression | Open |

No `sorryAx` or project-specific axiom occurs in the checked dependencies. Allowed standard axioms: `propext`, `Classical.choice`, `Quot.sound`. This is actual Lean checking, not an independent statement review; theorem counts are not completion percentages.

**The complete algorithmic complexity theorem is not yet formalized.** Classical existence of a small selection is not a verified executable ILP-based procedure.

## Verification and evidence

Run `python3 scripts/environment_gate.py`. GitHub Actions runs the same eight commands, including Lean startup, dependency resolution, Mathlib smoke test, project build, and the named-theorem axiom audit.

Raw successful output: `logs/verified_cells_20261017/`. Exact source and artifact hashes: `docs/source_hashes_cells_20261017.json`. Earlier checkpoints and logs are preserved.

## Reading and resuming

- `docs/PROOF_ROADMAP_20261017.md`: proof dependencies and the endpoint.
- `docs/REVIEW_CELLS_20261017.md`: correspondence with the manuscript and edge cases.
- `docs/source_map.json` and `docs/ACCEPTANCE.json`: verified scope and remaining obligations.
- `docs/NEXT_ALGORITHM_20261017.md`: next proof target and algorithm/complexity boundaries.
- `docs/session_cells_20261017.json`: this session 45.87 active minutes; cumulative recorded 101.85 minutes. Earlier unlogged preparation is unknown; inter-session idle time is excluded.
- `reference/mor34_fpt_proof.tex`: reference manuscript.

Historical comments in the initial preparation files are not current status. Proposition definitions in Targets.lean and PaperInterface.lean are not counted as proofs.
