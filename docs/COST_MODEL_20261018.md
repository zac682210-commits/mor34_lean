# Cost model and external-result boundary

The requested scope is the newly contributed mathematics and its use of established algorithms (see `SCOPE_NEW_PROOFS_20261018.md`). The development uses a mathematical reference algorithm with explicit returned values and charges. It is not a verified machine implementation of Lean's evaluator or runtime.

## What is counted

The final weighted path retains its intermediate results. Its calls are: violation detection; parity support search; each supported parity's coordinate extrema; each cell's normal matrix preparation and scalar search; retained count-point emission; adjacent exchange witnesses; binary point construction; exact rank/basis selection; and restoration of original labels. Invalid and empty-face branches are included.

`weightedNormalizedExecution` is the common value-and-charge definition. `RawNormalization.runWeighted` adds actual relabeling. `runPreparedWeighted` adds a retained `chargedCompressionPreparation`, which invokes compression twice and normalization once. Output correctness and cost refer to these same definitions.

Integer row evaluation uses `IntegerArithmeticCharge` on the actual expression operands; parity compilation shares the already read coefficients and cost array. Exact equality of the resulting dense solver arrays preserves the established solver's *input-dependent* charge, rather than just its answer.

Normal generation consumes the matrix returned by `CountMatrixPreparation.emit`. Candidate enumeration, unsuccessful candidates, determinant computation, annihilation checking, and final normal materialization are charged by the existing reference trace. The `unit` allowance is a uniform **local instruction price** for that trace, covering integer arithmetic, comparisons, bounded indexing and local data access. It is not a supplied bound for the whole normal-generator, cell, or program. `PreparedNormalOperands` and its reached-state theorem connect the minor and partial-sum bounds to the actual emitted matrices. The global row arithmetic envelope also dominates the normal operand envelope.

Remaining small collection operations (count insertion/emission, binary-point construction, matrix emission, sorting/collection and relabeling) have local output specifications and local cost bounds. Treating these as established polynomial-time primitives is explicitly permitted by the user-approved scope. Their internals and machine-level serialization are not formalized here.

## Established algorithms supplied as local contracts

| Primitive | Contract used | Application proved here |
|---|---|---|
| Integer linear feasibility | Correct witness/infeasibility and fixed-degree polynomial cost in the actual dense input, with dimension factor | All three encodings, dimension `2q`, input lengths, reached query bounds and number/composition of calls |
| Exact integer/rational rank | Correct rank on the emitted binary matrix and polynomial input cost | Matrix preparation, rank scan, tight affine-basis correctness and retained list bounds |
| Integer arithmetic and comparisons | Polynomial local cost on bounded operands | Expression evaluation, normal/minor bounds, actual-state propagation and uniform exponent composition |
| Grouping, sorting and finite collections | Local polynomial construction and exact value specification | Their placement in the returned-data execution and preservation of output labels |
| Frank–Tardos compression | Bounded-sign preservation, coefficient bound, and separately a bit-time or strongly polynomial arithmetic-time local contract | Two concrete calls, preservation of hypotheses/parameter/output, normalized magnitude bounds and complete cost composition |

No new project axiom is introduced for these contracts: the theorems quantify over implementations satisfying them. This is different from claiming the primitive implementations have been verified.

## Uniform and sharp parameter bounds

`UniformPolynomial` places the input exponent before the parameter quantifier. `SharpPolynomial` strengthens the factor to `(q+6)^(C*(q+1))`, with fixed `C`. The closure proofs preserve both quantifier orders. `doubled_dimension_factor` checks the substitution of dimension `2q` in the standard ILP factor. `sharp_parameter_transport` converts `q <= K+1` to a factor `(K+7)^(C'*(K+1))`.

The bit-time and arithmetic-time compression consequences are deliberately distinct. The former charges compression as polynomial in the original integer input size. The latter uses the established strongly polynomial *arithmetic-operation* contract for compression and yields a magnitude-independent operation bound. It does not claim magnitude-independent bit time for reading arbitrarily long input integers.

## Acceptance boundary

A green compilation plus the transitive named-declaration axiom audit establishes the listed Lean statements. It does not establish an external library implementation, compiler operational correctness, formal equivalence of source code to a machine cost model, or independent peer review. Final status must cite the exact verified source commit and retained artifact, not just the most recent branch head.
