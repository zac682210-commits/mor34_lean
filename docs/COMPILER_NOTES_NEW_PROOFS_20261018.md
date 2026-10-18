# Compiler diagnoses from this round

These notes preserve failed paths so later work does not repeat them. Exact
accepted source/run is in newproofs_verified_metadata.json. Failures below are
not mathematical counterexamples.

1. `Nat.lt_two_pow_self` has an implicit natural argument in the pinned library.
   Applying it positionally caused elaboration failure. Use the implicit value
   or a named argument and let the expected type determine it.
2. The positivity tactic did not close the natural inequality 1 <= (n+1)^3.
   `Nat.one_le_pow` with the explicit lower bound does.
3. A simplification list for the signed face dimension failed to rewrite both
   occurrences inside its conditional. Unfolding rawSignedDimension and then
   rewriting equality of the tight-point sets works directly.
4. The supported output branch needed both occurrences of RawDecision.Correct
   unfolded before transporting tightness, geometric face and facet predicates.
5. FacetComponentBound initially imported only FacetBridge, where DefinesFacet
   is not defined. Its theorem now states validity and the actual geometric
   codimension-one predicate explicitly. The raw-input wrapper subsequently
   uses the existing relabel_definesFacet bridge.
6. Broad `nlinarith` failed on a simple parameter-power call-budget inequality.
   The robust proof uses natural-number monotonicity term by term, then ring
   normalization. No inequality or parameter factor was weakened to conceal
   a missing estimate.
7. Rewriting computedReturnedSets_eq directly throughout an intermediate rank-
   call inequality also changed its left-hand algorithm expression. Attempting
   to use that inequality for the original algorithm forced Lean to unfold large
   definitions looking for definitional equality. Raising heartbeats alone did
   not fix the issue. The corrected proof first derives a separate list-length
   inequality and applies finiteBasisRankCalls_le to the unchanged actual list.
   This preserves propositional transport explicitly and compiles. A finite
   per-theorem heartbeat setting remains; no kernel checks are disabled.

8. Compact repeat/rewrite syntax left two parameter-power identities unsolved.
   The fix separates power-product simplification from exponent congruence and
   natural arithmetic, retaining the exact stated bounds.

All new named theorems are included exactly once in Check.lean and the fail-
closed transitive axiom allowlist. Frozen Model, Targets and PaperInterface
contents remain unchanged. Their original historical header comments have not
been edited; the current scope and evidence are described by the acceptance
record and README, rather than those initial-checkpoint comments.
