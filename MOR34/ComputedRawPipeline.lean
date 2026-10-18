import MOR34.ComputedNormalizedPipeline
import MOR34.RawInputPipeline

namespace MOR34
variable {n : ℕ}

/-- Raw output with finite computed normals. Raw normalization and other outer choices
remain separate; this does not claim an executable full solver. -/
noncomputable def RawNormalization.runComputed {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) : RawOutput n :=
  relabelOutput N.itemEquiv (computedNormalPipeline N.model N.wellFormed
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.ranker)

theorem computedRawPipeline_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.runComputed s).Correct a c b d := by
  have hh := relabelOutput_correct N.model N.itemEquiv a c N.weight_eq N.coefficient_eq _
    (computedNormalPipeline_correct N.model N.wellFormed s.solve s.solve_spec
      s.edgeSolve s.edge_spec s.violate s.violate_spec s.ranker)
  simpa only [N.capacity_eq, N.rhs_eq] using hh

theorem computedRawPipeline_facet {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.runComputed s).decision.isFacet = true ↔ RawDefinesFacet a c b d :=
  raw_correct_output_facet _ _ _ _ _ (computedRawPipeline_correct N s).1

theorem computed_original_input_output_contract (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (s : RowPrimitives (normalizeRaw hn a c b d ha hb hab hc).model) :
    ((normalizeRaw hn a c b d ha hb hab hc).runComputed s).Correct a c b d :=
  computedRawPipeline_correct _ s

end MOR34
