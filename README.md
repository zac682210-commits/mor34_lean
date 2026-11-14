# MOR34 Lean formalization

The formalization and its maintained status documentation are on the [`codex/mor34-formalization` branch](https://github.com/zac682210-commits/mor34_lean/tree/codex/mor34-formalization).

- [Current README and theorem entry points](https://github.com/zac682210-commits/mor34_lean/blob/codex/mor34-formalization/README.md)
- [Current acceptance record](https://github.com/zac682210-commits/mor34_lean/blob/codex/mor34-formalization/docs/ACCEPTANCE.json)
- [Cost model and external algorithm conditions](https://github.com/zac682210-commits/mor34_lean/blob/codex/mor34-formalization/docs/COST_MODEL_20261018.md)
- [Manuscript correspondence and unformalized external results](https://github.com/zac682210-commits/mor34_lean/blob/codex/mor34-formalization/docs/PAPER_ALIGNMENT_20261019.md)

**Status:** the newly contributed general proofs and their applications are complete in the declared mathematical reference cost model, conditional on explicit established local algorithm contracts. ILP, exact rank, Frank–Tardos, elementary arithmetic and sorting implementations, and compiler/backend runtime verification are not included in that claim.

**Verification evidence:** [source `8951a2f`](https://github.com/zac682210-commits/mor34_lean/tree/8951a2f5c5a64a477e907991b7653698d11ec440) passed [GitHub Actions run 39146901961](https://github.com/zac682210-commits/mor34_lean/actions/runs/39146901961): nine commands and an axiom audit of 1154 named declarations. The current acceptance record explains the completed conditional scope and the broader flags that remain false.

The README and acceptance file *inside that historical source snapshot* still show earlier progress. Later documentation-only commits record the completed state without changing Lean source. Follow the maintained links above for status, and the frozen commit for the checked code.

This page is an entry point only; the formalization has not been merged into `main` by this documentation update. Status links clarified November 14, 2026.
