import MOR34.DenseViolationSolver
import MOR34.ExecutableNormalization

namespace MOR34
variable {n : ℕ}

/-- Raw-input interface with one generic dense integer solver and an exact-rank
primitive. No separate correctness oracle is assumed for our three encodings. -/
def RawNormalization.runDense {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (inputRead queryRead : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (ranker : ExactIntegerRank N.sizes) : RawOutput n :=
  relabelOutput N.itemEquiv
    (denseNormalizedPipeline N.model N.wellFormed inputRead queryRead solve hs ranker)

theorem denseRawPipeline_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (inputRead queryRead : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (ranker : ExactIntegerRank N.sizes) :
    (N.runDense inputRead queryRead solve hs ranker).Correct a c b d := by
  have hh := relabelOutput_correct N.model N.itemEquiv a c N.weight_eq N.coefficient_eq _
    (denseNormalizedPipeline_correct N.model N.wellFormed inputRead queryRead solve hs ranker)
  simpa only [N.capacity_eq,N.rhs_eq] using hh

theorem denseRawPipeline_facet {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (inputRead queryRead : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (ranker : ExactIntegerRank N.sizes) :
    (N.runDense inputRead queryRead solve hs ranker).decision.isFacet = true ↔ RawDefinesFacet a c b d :=
  raw_correct_output_facet _ _ _ _ _ (denseRawPipeline_correct N inputRead queryRead solve hs ranker).1

theorem dense_original_input_output_contract (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (inputRead queryRead : ℕ)
    (solve : List (DenseIntegerRow (normalizeRawExecutable hn a c b d ha hb hab hc).classes) →
      Option (IntegerRowSolution (normalizeRawExecutable hn a c b d ha hb hab hc).classes) × ℕ)
    (hs : DenseRowSolverSpec solve)
    (ranker : ExactIntegerRank (normalizeRawExecutable hn a c b d ha hb hab hc).sizes) :
    ((normalizeRawExecutable hn a c b d ha hb hab hc).runDense inputRead queryRead solve hs ranker).Correct a c b d :=
  denseRawPipeline_correct _ inputRead queryRead solve hs ranker

end MOR34
