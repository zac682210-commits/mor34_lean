import MOR34.WeightedCellExecution
import MOR34.UniformPolynomialBudget

namespace MOR34

def weightedCellLoopBudget (q n L N D I c J H a : ℕ) : ℕ :=
  (q+1)*(chargedCellStepBudget q N (weightedCellQueryBudget q n L D I c H a)+J+1)+1

theorem weightedCellLoopBudget_uniform (I H K : ℕ → ℕ) (c a d : ℕ) :
    UniformPolynomial (fun q n L => weightedCellLoopBudget q n L
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c (K q*(n+L+2)^d) (H q) a) := by
  unfold weightedCellLoopBudget chargedCellStepBudget weightedCellQueryBudget
  uniform_polynomial

theorem weightedCellLoopBudget_mono (q n L N D I c J H a U : ℕ)
    (hN : N ≤ U) (hD : D ≤ U) (hJ : J ≤ U) :
    weightedCellLoopBudget q n L N D I c J H a ≤
      weightedCellLoopBudget q n L U U I c U H a := by
  unfold weightedCellLoopBudget chargedCellStepBudget weightedCellQueryBudget
  gcongr

/-- The arithmetic exponent is fixed before q. This is a bound for the actual
weighted cell-loop schedule, rather than for an isolated row evaluator. -/
theorem weightedCellLoopBudget_fpt (I H K : ℕ → ℕ) (c a d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ, ∀ q n L N D J,
      N ≤ K q*(n+L+2)^d → D ≤ K q*(n+L+2)^d → J ≤ K q*(n+L+2)^d →
      weightedCellLoopBudget q n L N D (I q) c J (H q) a ≤ F q*(n+L+2)^e := by
  obtain ⟨e,F,hF⟩ := weightedCellLoopBudget_uniform I H K c a d
  exact ⟨e,F,fun q n L N D J hN hD hJ =>
    (weightedCellLoopBudget_mono q n L N D (I q) c J (H q) a _ hN hD hJ).trans (hF q n L)⟩

end MOR34
