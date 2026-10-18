# Complete retained execution: mathematical review

This review covers the new source added after the 977-declaration checkpoint. Acceptance requires the final source/artifact audit recorded separately; this document alone does not assert a green build.

## Common output and cost path

`weightedNormalizedExecution` retains recognition, the returned point list, the final rank basis and a support witness. Both its correctness theorem and explicit cost inequality refer to this one definition. Invalid and empty branches are included. `RawNormalization.runWeighted` adds the actual output relabeling. `runPreparedWeighted` consumes the single retained result of two compression calls and normalization.

The predecessor `complete_reference_application` is deliberately retained as a reference-count theorem. Completion is based on the later weighted path, not on renaming that earlier result.

## Phase review

1. **Recognition.** The violation request is constructed once and passed to the generic dense solver. If there is no violating witness, the actual first-witness parity search runs. Invalid-witness point conversion has its local bounded-coordinate proof.
2. **Parity and extrema.** A support answer controls whether extrema and modes run. Upper/lower coordinate scans call weighted request construction and reuse their returned extrema. Linear scans are used; the proof claims the resulting FPT bound, not the manuscript's sharper binary-search call count.
3. **Cells and normals.** Each visited basis state emits its precise ordered augmented count matrix. The candidate search consumes that matrix. Candidate enumeration, unsuccessful candidates, arithmetic/comparison trace and final normal output are included. `PreparedNormalOperands` propagates the determinant and partial-sum envelope through the same reached query states.
4. **Integer requests.** Count, forced and violation rows are evaluated by the weighted expression interpreter. The actual parity transformation shares its stored coefficients. All three arrays equal the arrays used by the existing encoding/specification proofs, preserving both solver result and solver input-dependent cost.
5. **Exchange witnesses.** Adjacent indices are enumerated once. Each pair has one forced solve; its witness is retained, then both original and swapped points are emitted. The residual table is retained per request and not reconstructed per row.
6. **Final rank and basis.** Retained list length, including repetitions, is bounded. Ordering, matrix emission, rank on that matrix and collection are separately charged. Rank is never applied to an abstract matrix with unrelated input size.
7. **Raw output.** The decision witness and the complete returned basis are relabeled using the stored input equivalence. Cardinality and data-movement bounds apply to this same output.
8. **Preprocessing.** The two augmented coefficient vectors are compressed by two explicit calls. Sign preservation yields valid compressed hypotheses. Grouping/sorting is then invoked once. Parameter, original output and all compressed magnitudes are transported using proved application lemmas.

## Quantifiers and parameter dependence

`UniformPolynomial` excludes a polynomial degree that grows with q. `ParameterGrowth` and `SharpPolynomial` strengthen the factor to `(q+6)^(C*(q+1))`. Their closure proofs use only fixed powers. The standard `2q`-variable ILP factor is checked by `doubled_dimension_factor`. Final transport uses `q <= K+1`, giving `(K+7)^(C'*(K+1))`.

The local bounds in `WeightedRunBounds` concern arithmetic instructions, finite collection operations, exact rank and one integer solver input. There is no field assuming a total core, cell or complete algorithm runtime. The final cost theorem first invokes the proved phase sum, then applies polynomial closure.

## Compression models

The bit-time theorem charges the two external compression calls polynomially in original integer input length. The magnitude-independent arithmetic-time theorem instead uses the established strongly polynomial compression contract. These claims are separate: the latter does not remove the bit cost of reading large input integers.

## Deliberate external boundary

See `COST_MODEL_20261018.md`. Established ILP/rank/FT algorithms and routine arithmetic/sorting remain explicit local contracts, as authorized by the user. Backend execution costs and machine serialization are not verified. The normal `unit` is a local instruction price for the declared mathematical trace, not a runtime theorem about Lean's implementation.

## Mechanical corrections

Compilation corrections concern dependent `Option.get` equality, finite-set relabeling inverse laws, natural exponent casts, and safe tactic backtracking. The sharp-polynomial tactic must restore state and reject failed elaboration; every accepted result is subsequently audited for transitive axioms. Frozen model and target contracts remain unchanged. No failed compilation is counted as proof evidence.
