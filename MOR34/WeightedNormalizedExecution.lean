import MOR34.WeightedReturnedFamily

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Every branch and all supported-face phases belong to this one execution.
The recognition answer, selected points, exchange witnesses and basis are retained. -/
def weightedNormalizedExecution (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ops : PointOperations m) (ranker : ExactIntegerRank m)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m) :
    NormalizedOutput m × ℕ :=
  let recognition := weightedDenseRecognition A.arith P A.base.R A.base.D solve ops
  match recognition.1 with
  | .invalid t => (⟨.invalid t,∅⟩,recognition.2+1)
  | .empty => (⟨.empty,∅⟩,recognition.2+1)
  | .supported z =>
    let family := weightedReturnedFamily P hWF R solve hs A ops
    let basis := chargedFinalBasis ranker rankOps setOps family.1
    let witness := ops.makePrefix z
    (⟨.supported witness.1 (basis.1.card-1)
       (decide (basis.1.card=Fintype.card (Item m))),basis.1⟩,
      recognition.2+family.2+basis.2+witness.2+basis.1.card+3)

theorem weightedNormalizedExecution_value (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ops : PointOperations m) (ranker : ExactIntegerRank m)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m) :
    (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1 =
      constructedNormalizedPipeline P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs) (denseForcedOracle P R solve)
        (chargedDenseViolationSolve P A.base.R solve).1 ranker := by
  simp only [weightedNormalizedExecution,
    weightedDenseRecognition_value,chargedFinalBasis_value,weightedReturnedFamily_value,
    ops.makePrefix_value,constructedNormalizedPipeline,constructedReturnedSets_eq P hWF _ _ _
      (denseForcedOracle_spec P R solve hs)]
  cases executableRecognitionBranch (m := m) (chargedDenseViolationSolve P A.base.R solve).1
    (denseCountOracle P A.base.R solve) <;> rfl

theorem weightedNormalizedExecution_correct (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ops : PointOperations m) (ranker : ExactIntegerRank m)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m) :
    (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.Correct P := by
  rw [weightedNormalizedExecution_value]
  exact constructedNormalizedPipeline_correct P hWF _ (denseCountOracle_spec P A.base.R solve hs)
    _ (denseForcedOracle_spec P R solve hs) _ (denseViolation_spec P A.base.R solve hs) ranker

theorem weightedNormalizedExecution_basis_card (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ops : PointOperations m) (ranker : ExactIntegerRank m)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m) :
    (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).1.basis.card ≤
      Fintype.card (Item m)+1 := by
  dsimp only [weightedNormalizedExecution]
  split
  · simp
  · simp
  · rw [chargedFinalBasis_value]
    exact (binaryBasisSearch_correct _ _ (fun B => ranker.correct _)).2.1

def weightedNormalizedExecutionBudget (q n L N D I c J E C O BJ BE BI bc H a unit prep : ℕ) : ℕ :=
  weightedRecognitionBudget q n L D I c C H a+weightedReturnedFamilyBudget q n L N D I c J E C H a unit prep+
    finalBasisBudget n (retainedFamilyLength q n) O BJ BE BI bc+C+n+4

theorem weightedNormalizedExecution_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (hR : R ≤ Fintype.card (Item m)+1)
    (ops : PointOperations m) (ranker : ExactIntegerRank m)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations m)
    (C O BJ BE BI bc : ℕ) (ho : PointOperationBounds ops C)
    (hr : BinaryRankBounds ranker rankOps BE BI bc) (hc : BinaryCollectionBounds setOps O BJ) :
    (weightedNormalizedExecution P hWF R solve hs A ops ranker rankOps setOps).2 ≤
      weightedNormalizedExecutionBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E C O BJ BE BI bc A.H A.a A.unit A.prepCost := by
  have hrec := weightedDenseRecognition_cost P hWF solve hs A ops C ho
  have hf := weightedReturnedFamily_cost P hWF R solve hs A hR ops C ho
  have hl := weightedReturnedFamily_length P hWF R solve hs A ops
  have hb := chargedFinalBasis_cost ranker rankOps setOps _ O BJ BE BI bc hr hc _ hl
  have hcard : (chargedFinalBasis ranker rankOps setOps
      (weightedReturnedFamily P hWF R solve hs A ops).1).1.card ≤ Fintype.card (Item m)+1 := by
    rw [chargedFinalBasis_value]
    exact (binaryBasisSearch_correct _ _ (fun B => ranker.correct _)).2.1
  dsimp only [weightedNormalizedExecution]
  split
  · unfold weightedNormalizedExecutionBudget
    omega
  · unfold weightedNormalizedExecutionBudget
    omega
  · rename_i z hz
    have hcorrect := executableRecognitionBranch_correct P hWF
      (chargedDenseViolationSolve P A.base.R solve).1 (denseViolation_spec P A.base.R solve hs)
      (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs)
    rw [← weightedDenseRecognition_value A.arith P A.base.R A.base.D solve ops,hz] at hcorrect
    have hp := ho.prefix_cost z hcorrect.2.1
    unfold weightedNormalizedExecutionBudget
    omega

end MOR34
