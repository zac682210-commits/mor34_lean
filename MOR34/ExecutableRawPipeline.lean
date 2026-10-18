import MOR34.ExecutableNormalizedPipeline
import MOR34.RawInputPipeline

namespace MOR34
variable {n : ℕ}

/-- Executable after a concrete normalization is supplied. The construction of that
normalization and the primitive solvers remain separate obligations. -/
def RawNormalization.runExecutable {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) : RawOutput n :=
  relabelOutput N.itemEquiv (executableNormalizedPipeline N.model N.wellFormed
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.ranker)

theorem executableRawPipeline_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.runExecutable s).Correct a c b d := by
  have hh := relabelOutput_correct N.model N.itemEquiv a c N.weight_eq N.coefficient_eq _
    (executableNormalizedPipeline_correct N.model N.wellFormed s.solve s.solve_spec
      s.edgeSolve s.edge_spec s.violate s.violate_spec s.ranker)
  simpa only [N.capacity_eq, N.rhs_eq] using hh

theorem executableRawPipeline_facet {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.runExecutable s).decision.isFacet = true ↔ RawDefinesFacet a c b d :=
  raw_correct_output_facet _ _ _ _ _ (executableRawPipeline_correct N s).1

theorem executable_normalized_original_output_contract (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (s : RowPrimitives (normalizeRaw hn a c b d ha hb hab hc).model) :
    ((normalizeRaw hn a c b d ha hb hab hc).runExecutable s).Correct a c b d :=
  executableRawPipeline_correct _ s

theorem executableRawPipeline_dimension {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) (hv : RawValid a c b d) :
    (N.runExecutable s).decision.dimension = some (rawSignedDimension a c b d) := by
  have hv' : RawValid a c N.model.capacity N.model.rhs := by
    simpa only [N.capacity_eq, N.rhs_eq] using hv
  have hm : Valid N.model :=
    (relabel_valid N.model N.itemEquiv a c N.weight_eq N.coefficient_eq).mpr hv'
  change (relabelDecision N.itemEquiv (executableNormalizedPipeline N.model N.wellFormed
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.ranker).decision).dimension = _
  rw [relabelDecision_dimension, executableNormalizedPipeline_dimension N.model N.wellFormed hm
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.violate_spec s.ranker]
  have h := relabel_signed_dimension N.model hm N.itemEquiv a c N.weight_eq N.coefficient_eq
  simpa only [N.capacity_eq, N.rhs_eq] using congrArg some h.symm

end MOR34
