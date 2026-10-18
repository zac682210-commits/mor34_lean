import MOR34.WeightedNormalizedExecution
import MOR34.CompleteReferenceApplication

namespace MOR34

theorem weightedNormalizedBudget_uniform (I BI H K : ℕ → ℕ) (c bc a d : ℕ) :
    UniformPolynomial (fun q n L => weightedNormalizedExecutionBudget q n L
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc
      (H q) a (K q*(n+L+2)^d) (K q*(n+L+2)^d)) := by
  unfold weightedNormalizedExecutionBudget weightedRecognitionBudget weightedReturnedFamilyBudget
    weightedSelectionExecutionBudget weightedEdgeExecutionBudget weightedViolationRequestBudget
    weightedForcedRequestBudget weightedBranchRowBudget finalBasisBudget binaryRankBudget
    retainedFamilyLength weightedParityBudget weightedExtremaBudget weightedModesBudget
    preparedWeightedCellBudget preparedCellStepBudget weightedCellQueryBudget
  uniform_polynomial

theorem weightedNormalizedBudget_mono (q n L N D I c J E C O BJ BE BI bc H a unit prep U : ℕ)
    (hN : N ≤ U) (hD : D ≤ U) (hJ : J ≤ U) (hE : E ≤ U)
    (hC : C ≤ U) (hO : O ≤ U) (hBJ : BJ ≤ U) (hBE : BE ≤ U)
    (hu : unit ≤ U) (hp : prep ≤ U) :
    weightedNormalizedExecutionBudget q n L N D I c J E C O BJ BE BI bc H a unit prep ≤
      weightedNormalizedExecutionBudget q n L U U I c U U U U U U BI bc H a U U := by
  unfold weightedNormalizedExecutionBudget weightedRecognitionBudget weightedReturnedFamilyBudget
    weightedSelectionExecutionBudget weightedEdgeExecutionBudget weightedViolationRequestBudget
    weightedForcedRequestBudget weightedBranchRowBudget finalBasisBudget binaryRankBudget
    retainedFamilyLength weightedParityBudget weightedExtremaBudget weightedModesBudget
    preparedWeightedCellBudget preparedCellStepBudget weightedCellQueryBudget
  gcongr

/-- The normal matrix preparation and per-instruction normal work are included
among local costs; the derived theorem does not assume a total algorithm cost. -/
structure WeightedExecutionLocalBounds {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) (C O BJ BE U : ℕ) : Prop where
  base : ExecutionLocalBounds P solve A.base C O BJ BE U
  normalUnit : A.unit ≤ U
  prepare : A.prepCost ≤ U

/-- The quantifiers make the uniformity requirement explicit: solver/rank and
local primitive exponents are chosen before the dimension q and instance. -/
theorem complete_weighted_application (I BI H K : ℕ → ℕ) (c bc a d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ,
    ∀ {q : ℕ} {m : Fin q → ℕ} (P : Model m) (hWF : WellFormed P) (R : ℕ)
      (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve),
      R ≤ Fintype.card (Item m)+1 → A.base.I = I q → A.base.c = c → A.H = H q → A.a = a →
    ∀ (ops : PointOperations m) (ranker : ExactIntegerRank m)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m)
      (C O BJ BE : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI q) bc →
      BinaryCollectionBounds setOps O BJ →
      WeightedExecutionLocalBounds P solve A C O BJ BE (K q*(Fintype.card (Item m)+A.base.L+2)^d) →
      (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.Correct P ∧
      (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).2 ≤
        F q*(Fintype.card (Item m)+A.base.L+2)^e := by
  obtain ⟨e,F,hF⟩ := weightedNormalizedBudget_uniform I BI H K c bc a d
  refine ⟨e,F,?_⟩
  intro q m P hWF R solve hs A hR hI hc hH ha ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  refine ⟨weightedNormalizedExecution_correct P hWF R solve hs A ops ranker rankOps setOps,?_⟩
  have hcost := weightedNormalizedExecution_cost P hWF R solve hs A hR ops ranker rankOps setOps
    C O BJ BE (BI q) bc ho hr hb
  rw [hI,hc,hH,ha] at hcost
  have hm := weightedNormalizedBudget_mono q (Fintype.card (Item m)) A.base.L A.base.N
    A.base.D (I q) c A.base.J A.base.E C O BJ BE (BI q) bc (H q) a A.unit A.prepCost
    (K q*(Fintype.card (Item m)+A.base.L+2)^d) hlocal.base.normalRead hlocal.base.decode
    hlocal.base.insertCount hlocal.base.emitCount hlocal.base.point hlocal.base.order
    hlocal.base.insertBinary hlocal.base.emitBinary hlocal.normalUnit hlocal.prepare
  exact hcost.trans (hm.trans (hF q _ A.base.L))

/-- The compression substitution now takes the cost of the actual retained
execution, whose bound is proved above. It does not assume a core-cost theorem. -/
theorem complete_compressed_weighted_application (I BI H K : ℕ → ℕ) (c bc a d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ,
    ∀ {q : ℕ} {m : Fin q → ℕ} (P : Model m) (hWF : WellFormed P) (R : ℕ)
      (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve),
      R ≤ Fintype.card (Item m)+1 → A.base.I = I q → A.base.c = c → A.H = H q → A.a = a →
      A.base.L ≤ 18*(Fintype.card (Item m)+1)^4 →
    ∀ (ops : PointOperations m) (ranker : ExactIntegerRank m)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m)
      (C O BJ BE : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI q) bc →
      BinaryCollectionBounds setOps O BJ →
      WeightedExecutionLocalBounds P solve A C O BJ BE (K q*(Fintype.card (Item m)+A.base.L+2)^d) →
      (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.Correct P ∧
      (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).2 ≤
        F q*(Fintype.card (Item m)+1)^e := by
  obtain ⟨e,F,hF⟩ := complete_weighted_application I BI H K c bc a d
  refine ⟨4*e,fun q => F q*20^e,?_⟩
  intro q m P hWF R solve hs A hR hI hc hH ha hL ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  have hh := hF P hWF R solve hs A hR hI hc hH ha ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  exact ⟨hh.1,compression_cost_substitution_two _ A.base.L (F q) e _ hL hh.2⟩

end MOR34
