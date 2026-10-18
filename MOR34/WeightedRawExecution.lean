import MOR34.CompleteWeightedApplication
import MOR34.ChargedRawExecution

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

/-- The original item labeling is restored after the single retained normalized
execution. The full output (witness, dimension, facet flag and basis) is moved. -/
def RawNormalization.runWeighted {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (R : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives N.model solve)
    (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
    (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n) :
    RawOutput n × ℕ :=
  let core := weightedNormalizedExecution N.model N.wellFormed R solve hs A ops ranker rankOps setOps
  let out := chargedRelabelOutput N.itemEquiv point basis core.1
  (out.1,core.2+out.2+1)

theorem weightedRawExecution_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (R : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives N.model solve)
    (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
    (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n) :
    (N.runWeighted R solve hs A ops ranker rankOps setOps point basis).1.Correct a c b d := by
  have hh := relabelOutput_correct N.model N.itemEquiv a c N.weight_eq N.coefficient_eq _
    (weightedNormalizedExecution_correct N.model N.wellFormed R solve hs A ops ranker rankOps setOps)
  simpa only [RawNormalization.runWeighted,chargedRelabelOutput_value,N.capacity_eq,N.rhs_eq] using hh

theorem weightedRawExecution_cost {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (R : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives N.model solve) (hR : R ≤ n+1)
    (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
    (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n)
    (C O BJ BE BI bc RC RE RJ : ℕ) (ho : PointOperationBounds ops C)
    (hr : BinaryRankBounds ranker rankOps BE BI bc) (hc : BinaryCollectionBounds setOps O BJ)
    (hl : RelabelLocalBounds N.itemEquiv point basis RC RE RJ) :
    (N.runWeighted R solve hs A ops ranker rankOps setOps point basis).2 ≤
      weightedNormalizedExecutionBudget N.classes n A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E C O BJ BE BI bc A.H A.a A.unit A.prepCost+
        RC+RE+(n+1)*(RC+1)+RJ+3 := by
  have hn : Fintype.card (Item N.sizes) = n := by simpa using Fintype.card_congr N.itemEquiv
  have hcore := weightedNormalizedExecution_cost N.model N.wellFormed R solve hs A
    (by simpa only [hn] using hR) ops ranker rankOps setOps C O BJ BE BI bc ho hr hc
  have hcard := weightedNormalizedExecution_basis_card N.model N.wellFormed R solve hs A
    ops ranker rankOps setOps
  rw [hn] at hcore hcard
  have hout := chargedRelabelOutput_cost N.itemEquiv point basis RC RE RJ hl _ hcard
  dsimp only [RawNormalization.runWeighted]
  omega

end MOR34
