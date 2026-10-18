# Next checkpoint: global phase and bit-cost composition

Read ACCEPTANCE.json, SELECTION_PIPELINE_REVIEW_20261018.md and the session ledger.
Use the accepted source commit. Do not restart from an older source or redo the
core geometric proofs. Scope remains only newly contributed proofs/applications;
no subagents, merge, publication, or rebuilding established algorithm internals.

Finished this round: actual retained support/extrema/cell/mode/parity selection;
semantic and span connection; retained list length including repetitions;
selection-phase polynomial reference-cost derivation; generic charged rank scan;
remaining row literals; local row bit-weighted evaluation and polynomial bound;
concrete count/forced/violation constructor applications.

Next work order:

1. Define charged exchange/validity/output schedule using the existing dense
   forced/violation requests and stored exchange answers. Preserve actual choices
   and witnesses; do not substitute an unrelated subtotal.
2. Emit the binary rank input from the retained family, connect its concrete
   payload/construction bound to chargedRankBasis, then reuse existing rank
   correctness and dimension results. Do not reprove the rank algorithm.
3. Reuse weightedCountRow_polynomial, weightedForcedRow_polynomial and
   weightedViolationRow_polynomial rather than reproving their literal/node
   bounds. Instantiate extra query literals along reached normal-search states,
   connect parity transformation, and replace actual request evaluators. Lift
   normal arithmetic and collection operations too.
4. Compose preprocessing, table materialization, relabeling and compression with
   local sorting/FT interfaces. Prove uniform input exponent; q may affect only
   the parameter coefficient and fixed dimension of established solver contracts.

Important boundaries: DenseCellPrimitives N,D,J,E are local allowances. The
selection cost is not yet a bit-cost bound for the full original-input pipeline.
chargedRankBasis still requires a concrete matrix/input-construction adapter.
The extrema algorithm uses linear scans. Full FPT/new-applications/full-paper
flags remain false until every actual phase is connected.

Do not add a full-algorithm-cost field to a primitive record. Do not call a
conditional cost assumption a discharged complexity theorem. Keep Model.lean,
Targets.lean and PaperInterface.lean unchanged. The six-item illustration remains
outside acceptance. Record actual active time excluding CI-only waits, idle gaps
and historical unlogged work. Never infer elapsed research from run triggers.

Exact integration landmarks found in this round:

- denseNormalizedPipeline delegates to constructedNormalizedPipeline, not the
  older storedNormalizedPipeline. Preserve the constructed residual/witness path.
- adjacent_exchange_uses_one_solve and adjacentWitnessTable_length give one
  forced solve per adjacent pair and at most n pairs. Retain returned answers;
  edgePointsFromTable adds at most 2n points.
- Selection contributes at most (q+1)*6^q points before deduplication. Use that
  retained list bound when composing rank costs. Do not silently use a smaller
  deduplicated length for a loop that scans the original list.
- chargedRankBasis is generic: its rank callback must include binaryPointMatrix
  input emission. binaryMatrixPayload_bound supplies size, not construction time.
- Candidate normals have parameter-only enumeration counts. N in
  DenseCellPrimitives is specifically the stored-normal coefficient READ
  allowance passed to chargedOutsideQueries, not the normal-generation cost.
  Generation is separately charged by builtCountForms/builtCountFormBudget.
  Instantiate N from actual lookup costs and lift the generation arithmetic
  using normalWorkBits/determinant_signed_bits/normalCheck_signed_bits.
  counted_normal_bit_cost is still a subtotal, not a replacement for this
  actual-call connection. Do not introduce an unconnected normal budget.

Avoid unnecessary reimplementation in the bit-cost lift:

- weightedEvaluateRow_value is equality of the actual dense arrays (not only
  equality of their represented rational inequalities). Thus a weighted compiler
  can call the same dense solver on the same input list, preserving its value,
  branch, witnesses, and per-input solver bound.
- First define a weighted analogue of compileRetainedRow using the same
  retained constructor output. Its value equality can compose directly with
  builtCountRow_value / the forced and violation counterparts. Keep constructor
  reads and index enumeration outside the arithmetic node total.
- The current compileParityRow uses denseParityRow, which shares row.costs and
  reads each count coefficient once. A weighted lift must charge stored reads,
  multiplication, summation/subtraction and list writes. Merely applying the AST
  parityRowConstruction theorem does not establish this concrete routine's cost.
- Once the weighted dense request output equals the old request list, solver
  value equality permits the same reached-state proof. Prove the stronger local
  request bound there, then reuse the completed outer selection composition.
  Do not redo the parity/cell span proofs.
- For rank, input lists with repeated candidate points are allowed. Either
  preserve their original length bound in chargedRankBasis, or explicitly charge
  deduplication/sorting and prove equality with orderedBinarySets before using
  the old exact-output theorem. Span equality alone does not imply identical
  chosen bases, although it can establish an appropriately stated correctness
  contract without claiming identical output.
