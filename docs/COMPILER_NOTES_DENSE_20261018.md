# Compiler notes for the dense checkpoint

All changes stayed on `codex/mor34-formalization`. No merge was performed.
The old accepted 803-declaration source and logs are preserved. Acceptance of
this checkpoint requires the final successful source/artifact verification.

Non-final iterations exposed ordinary elaboration/proof issues:

- `List.map_ofFn` required explicit `Function.comp_def` before finite sums
  matched. The evaluation proof was normalized accordingly.
- The quartic request estimate was factored into an explicit cubic inequality
  and a multiplication identity, instead of relying on nonlinear automation to
  discover the higher-degree factorization.
- An inline tactic continuation and an inductive constructor case were corrected
  in the intermediate-value proof. Addition bounds now use explicit monotone
  steps, avoiding a fragile nonlinear-power normalization.
- An exact rewrite already closed the cell-query length goal. A following
  `omega` caused a 'no goals to be solved' failure and was removed.

No theorem was replaced by `sorry`, an axiom, or a weaker frozen target.

CI timing matters for continuation: project compilation can finish quickly while
printing the transitive axiom dependencies takes several additional minutes.
Some run/step summaries are stale; full job logs are only downloadable after
completion and may temporarily return BlobNotFound. Do not infer build failure
from that transient download response and do not count CI-only waiting as work.
