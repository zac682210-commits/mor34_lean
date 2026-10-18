import MOR34.WeightedSelection
import MOR34.WeightedBranchRequests

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedDenseSupport (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    Option (Counts q) × ℕ :=
  let parities := chargedFinFunctions q 2
  let out := chargedFirstWitness (fun ε => weightedDenseListQuery arith P R D solve ε []) parities.1
  (out.1,parities.2+out.2+1)

theorem weightedDenseSupport_value (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    (weightedDenseSupport arith P R D solve).1 = executableSupportSearch (denseCountOracle P R solve) := by
  simp only [weightedDenseSupport,chargedFirstWitness_value,chargedFinFunctions_value,
    weightedDenseListQuery_value,executableSupportSearch,executableParityList]

theorem weightedDenseSupport_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) :
    (weightedDenseSupport A.arith P A.base.R A.base.D solve).2 ≤ functionEnumerationBudget q 2+
      2^q*(weightedCellQueryBudget q (Fintype.card (Item m)) A.base.L A.base.D A.base.I A.base.c A.H A.a+1)+2 := by
  let U := weightedCellQueryBudget q (Fintype.card (Item m)) A.base.L A.base.D A.base.I A.base.c A.H A.a
  have hc (ε : Parity q) : (weightedDenseListQuery A.arith P A.base.R A.base.D solve ε []).2 ≤ U :=
    weightedDenseListQuery_cost P hWF solve A.base A.arith A.H A.a A.arithmetic_bound
      ε [] (by simp) (by simp)
  have hh := chargedFirstWitness_cost (fun ε => weightedDenseListQuery A.arith P A.base.R A.base.D solve ε [])
    (chargedFinFunctions q 2).1 U (fun ε _ => hc ε)
  have hn := firstWitness_calls_le (fun ε => (weightedDenseListQuery A.arith P A.base.R A.base.D solve ε []).1)
    (chargedFinFunctions q 2).1
  have hl : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hl] at hn
  have hs := hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (U+1) hn) 1)
  have he := chargedFinFunctions_cost q 2
  dsimp only [weightedDenseSupport]
  change _ ≤ functionEnumerationBudget q 2+2^q*(U+1)+2
  omega

def weightedDenseRecognition (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : RecognitionBranch m × ℕ :=
  let violation := weightedDenseViolationSolve arith P R solve
  match violation.1 with
  | some s => let t := ops.invalid s.1
              (.invalid t.1,violation.2+t.2+1)
  | none => let support := weightedDenseSupport arith P R D solve
            (match support.1 with | none => .empty | some z => .supported z,
             violation.2+support.2+1)

theorem weightedDenseRecognition_value (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (weightedDenseRecognition arith P R D solve ops).1 =
      executableRecognitionBranch (m := m) (chargedDenseViolationSolve P R solve).1
        (denseCountOracle P R solve) := by
  simp only [weightedDenseRecognition,executableRecognitionBranch,weightedDenseSupport_value,weightedDenseViolationSolve_value]
  cases (chargedDenseViolationSolve P R solve).1 <;> simp only [ops.invalid_value]
  · cases executableSupportSearch (denseCountOracle P R solve) <;> rfl

def weightedRecognitionBudget (q n L D I c C H a : ℕ) : ℕ :=
  weightedViolationRequestBudget q n L H a+I*(180*(n+L+2)^4)^c+functionEnumerationBudget q 2+
    2^q*(weightedCellQueryBudget q n L D I c H a+1)+C+4

theorem weightedDenseRecognition_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ops : PointOperations m) (C : ℕ) (hops : PointOperationBounds ops C) :
    (weightedDenseRecognition A.arith P A.base.R A.base.D solve ops).2 ≤
      weightedRecognitionBudget q (Fintype.card (Item m)) A.base.L A.base.D A.base.I A.base.c C A.H A.a := by
  have hv := (weightedDenseBranchSolve_cost P hWF 0 solve A (by omega)).1
  have hsup := weightedDenseSupport_cost P hWF solve A
  dsimp only [weightedDenseRecognition]
  split
  · rename_i s he
    have hb := ((violationRows_iff P s.1 s.2).mp ((denseViolation_spec P A.base.R solve hs).found s (by simpa only [weightedDenseViolationSolve_value] using he))).1.1
    have ho := hops.invalid s.1 hb
    unfold weightedRecognitionBudget
    omega
  · unfold weightedRecognitionBudget
    omega

end MOR34
