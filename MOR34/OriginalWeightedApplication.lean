import MOR34.WeightedRawExecution
import MOR34.OriginalReferenceApplication

namespace MOR34

def rawWeightedBudget (q n L N D I c J E C O BJ BE BI bc H a unit prep RC RE RJ : ℕ) : ℕ :=
  weightedNormalizedExecutionBudget q n L N D I c J E C O BJ BE BI bc H a unit prep+
    RC+RE+(n+1)*(RC+1)+RJ+3

theorem rawWeightedBudget_uniform (I BI H K : ℕ → ℕ) (c bc aexp d : ℕ) :
    UniformPolynomial (fun q n L =>
      rawWeightedBudget q n L (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc (H q) aexp (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)) := by
  unfold rawWeightedBudget
  apply uniformPolynomial_add
  · apply uniformPolynomial_add
    · apply uniformPolynomial_add
      · apply uniformPolynomial_add
        · apply uniformPolynomial_add
          · exact weightedNormalizedBudget_uniform I BI H K c bc aexp d
          · uniform_polynomial
        · uniform_polynomial
      · uniform_polynomial
    · uniform_polynomial
  · uniform_polynomial

/-- This theorem includes restoration of the original point labels. It is
a weighted reference result relative to local arithmetic and data primitives. -/
theorem original_weighted_application (I BI H K : ℕ → ℕ) (c bc aexp d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ, ∀ {n : ℕ} {a v : Fin n → ℤ} {b rhs : ℤ}
      (N : RawNormalization a v b rhs) (R : ℕ)
      (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives N.model solve),
      R ≤ n+1 → A.base.I = I N.classes → A.base.c = c → A.H = H N.classes → A.a = aexp →
    ∀ (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
      (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n)
      (C O BJ BE RC RE RJ : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI N.classes) bc →
      BinaryCollectionBounds setOps O BJ → RelabelLocalBounds N.itemEquiv point basis RC RE RJ →
      WeightedExecutionLocalBounds N.model solve A C O BJ BE (K N.classes*(n+A.base.L+2)^d) →
      RC ≤ K N.classes*(n+A.base.L+2)^d → RE ≤ K N.classes*(n+A.base.L+2)^d →
      RJ ≤ K N.classes*(n+A.base.L+2)^d →
      (N.runWeighted R solve hs A ops ranker rankOps setOps point basis).1.Correct a v b rhs ∧
      (N.runWeighted R solve hs A ops ranker rankOps setOps point basis).2 ≤
        F (((Finset.univ.image v).filter (fun z => 0 < z)).card)*(n+A.base.L+2)^e := by
  obtain ⟨e,F,hF⟩ := rawWeightedBudget_uniform I BI H K c bc aexp d
  refine ⟨e,parameterMajorant F,?_⟩
  intro n a v b rhs N R solve hs A hR hI hc hH ha ops ranker rankOps setOps point basis
    C O BJ BE RC RE RJ ho hr hb hl hlocal hRC hRE hRJ
  refine ⟨weightedRawExecution_correct N R solve hs A ops ranker rankOps setOps point basis,?_⟩
  have hx := weightedRawExecution_cost N R solve hs A hR ops ranker rankOps setOps point basis
    C O BJ BE (BI N.classes) bc RC RE RJ ho hr hb hl
  rw [hI,hc,hH,ha] at hx
  have hn := weightedNormalizedBudget_mono N.classes n A.base.L A.base.N A.base.D (I N.classes) c
    A.base.J A.base.E C O BJ BE (BI N.classes) bc (H N.classes) aexp A.unit A.prepCost (K N.classes*(n+A.base.L+2)^d)
    hlocal.base.normalRead hlocal.base.decode hlocal.base.insertCount hlocal.base.emitCount
    hlocal.base.point hlocal.base.order hlocal.base.insertBinary hlocal.base.emitBinary hlocal.normalUnit hlocal.prepare
  have hm := Nat.mul_le_mul_left (n+1) (Nat.add_le_add_right hRC 1)
  have hraw := hF N.classes n A.base.L
  dsimp only [rawWeightedBudget] at hraw
  have hbound := parameterMajorant_le F N.classes
    (((Finset.univ.image v).filter (fun z => 0 < z)).card) (rawNormalization_parameter N)
  have hlast := Nat.mul_le_mul_right ((n+A.base.L+2)^e) hbound
  omega

end MOR34
