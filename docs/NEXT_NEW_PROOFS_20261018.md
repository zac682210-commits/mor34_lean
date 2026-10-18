# Remaining work under the user's new-proof-only scope

Authority: SCOPE_NEW_PROOFS_20261018.md. Do not resume the superseded goal of
implementing ILP, rational rank or Frank--Tardos, or proving Lean-backend costs.
Read ACCEPTANCE.json for the exact accepted commit before continuing.
The phase-by-phase mathematical derivation is in
REFERENCE_COST_DERIVATION_20261018.md; it is explicitly not yet a Lean total-time proof.

## One remaining main proof block

Assemble the manuscript-level FPT cost derivation for a reference algorithm that
stores each computed witness and normal family once. Reuse the proved output
correctness and row encodings. State external polynomial arithmetic, sorting,
exact rank and fixed-dimensional integer-programming costs explicitly.

Available checked ingredients (subject to the latest accepted head):

- rowSearchCalls_polynomial: support, extrema and cell solver-call budget is
  rowCallFactor(q)(n+1). This includes scanning extrema; do not claim the paper's
  sharper binary-search count for the executable implementation.
- counted_ilp_cost_bound: substitutes an external per-call polynomial cost into
  that budget, with input degree 4c+1 independent of q.
- computedPipeline_polynomial_payload: every generated cell ILP has dense signed
  integer payload <=168(n+L+2)^4 when input magnitudes are <=2^L.
- forcedSystem_polynomial_payload and violationSystem_polynomial_payload: the
  same bound is already instantiated with the actual forced/violation integer
  encodings. The proof establishes pairAllowed.card<=m_j<=n.
- allNormalCandidateCalls_bound: all parameter-sized normal searches together
  use at most 6^q(q+1)(q+2)(q+1)^(2(q+1)) candidate tests. Existing determinant
  and annihilation bounds control arithmetic sizes in rejected candidates too.
- computedReturnedBasis_rank_calls: count for the actual ordered returned family.
- binaryBasisSearch_rank_payload_states: every rank input has at most
  2(n+2)^2 dense integer bits, including the inserted candidate.
- counted_rank_cost_bound: inserting the external rank cost gives a degree
  2c+2 bound for this phase, with a separate q-dependent factor.
- adjacentPair_card and computedEdges_card: at most n adjacent pairs/edges.
- compression_cost_substitution: once the original total cost is established,
  inserting the independently proved compressed payload yields the n-only
  polynomial. It does not discharge the premise of the total cost theorem.

The remaining connection is a justified sum of phase budgets: preprocessing,
edge witnesses, finite construction/enumeration, normal tests, ILP, rank and
output. The model must describe this reference algorithm rather than define
its cost to be the desired upper bound. A small phase-cost record can accept
only standard primitive operation bounds; it must not assume the final FPT
bound. A mathematical reference program with verified semantic projection
suffices; no compiler operational semantics is requested.

ParameterFactors now proves rowCallFactor(q)<=(q+2)^(3q+5), and the normal
search factor<=(q+2)^(5q+4)<=(K+3)^(5K+9). Reuse these explicit bounds when
combining the external solver factor and the remaining phases. A looser
parameter-independent polynomial degree is acceptable; explicitly identify
any deviation from the manuscript's sharper oracle-call expression.

## Completion and evidence

Keep full_FPT_complexity false until the phase-composition statement is checked.
Keep the original code, models and target contracts unchanged. Every new named
theorem belongs in Check.lean and audit_axioms.py. Use GitHub Actions only;
verify the exact source head, retained artifact and transitive axiom audit.

The six-item illustration is not a separate formal facet certificate. It is
not used in the general theorem; either label it outside the formal theorem
scope or formalize it separately before claiming every statement in the paper.
