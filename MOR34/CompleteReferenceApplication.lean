import MOR34.UniformPolynomialBudget

namespace MOR34

/-- A common envelope for elementary callbacks. Integer feasibility and rank
have their own dimension factor and fixed polynomial exponent. -/
structure ExecutionLocalBounds {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : DenseCellPrimitives P solve) (C O BJ BE U : ℕ) : Prop where
  normalRead : A.N ≤ U
  decode : A.D ≤ U
  insertCount : A.J ≤ U
  emitCount : A.E ≤ U
  point : C ≤ U
  order : O ≤ U
  insertBinary : BJ ≤ U
  emitBinary : BE ≤ U

/-- The quantifiers make the uniformity requirement explicit: solver/rank and
local primitive exponents are chosen before the dimension q and instance. -/
theorem complete_reference_application (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ,
    ∀ {q : ℕ} {m : Fin q → ℕ} (P : Model m) (hWF : WellFormed P) (R : ℕ)
      (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve),
      R ≤ Fintype.card (Item m)+1 → A.I = I q → A.c = c →
    ∀ (ops : PointOperations m) (ranker : ExactIntegerRank m)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m)
      (C O BJ BE : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI q) bc →
      BinaryCollectionBounds setOps O BJ →
      ExecutionLocalBounds P solve A C O BJ BE (K q*(Fintype.card (Item m)+A.L+2)^d) →
      (chargedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.Correct P ∧
      (chargedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).2 ≤
        F q*(Fintype.card (Item m)+A.L+2)^e := by
  obtain ⟨e,F,hF⟩ := normalizedExecutionBudget_fpt I BI K c bc d
  refine ⟨e,F,?_⟩
  intro q m P hWF R solve hs A hR hI hc ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  refine ⟨chargedNormalizedExecution_correct P hWF R solve hs A ops ranker rankOps setOps,?_⟩
  have hcost := chargedNormalizedExecution_cost P hWF R solve hs A hR ops ranker rankOps setOps
    C O BJ BE (BI q) bc ho hr hb
  rw [hI,hc] at hcost
  exact hcost.trans (hF q _ A.L A.N A.D A.J A.E C O BJ BE hlocal.normalRead
    hlocal.decode hlocal.insertCount hlocal.emitCount hlocal.point hlocal.order
    hlocal.insertBinary hlocal.emitBinary)

/-- The compression substitution now takes the cost of the actual retained
execution, whose bound is proved above. It does not assume a core-cost theorem. -/
theorem complete_compressed_reference_application (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ,
    ∀ {q : ℕ} {m : Fin q → ℕ} (P : Model m) (hWF : WellFormed P) (R : ℕ)
      (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve),
      R ≤ Fintype.card (Item m)+1 → A.I = I q → A.c = c →
      A.L ≤ 18*(Fintype.card (Item m)+1)^4 →
    ∀ (ops : PointOperations m) (ranker : ExactIntegerRank m)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m)
      (C O BJ BE : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI q) bc →
      BinaryCollectionBounds setOps O BJ →
      ExecutionLocalBounds P solve A C O BJ BE (K q*(Fintype.card (Item m)+A.L+2)^d) →
      (chargedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.Correct P ∧
      (chargedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).2 ≤
        F q*(Fintype.card (Item m)+1)^e := by
  obtain ⟨e,F,hF⟩ := complete_reference_application I BI K c bc d
  refine ⟨4*e,fun q => F q*20^e,?_⟩
  intro q m P hWF R solve hs A hR hI hc hL ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  have hh := hF P hWF R solve hs A hR hI hc ops ranker rankOps setOps C O BJ BE ho hr hb hlocal
  exact ⟨hh.1,compression_cost_substitution_two _ A.L (F q) e _ hL hh.2⟩

end MOR34
