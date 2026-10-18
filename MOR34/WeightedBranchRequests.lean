import MOR34.WeightedPipelinePrimitives
import MOR34.WeightedRemainingRequests
import MOR34.ChargedExchangeExecution

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedBranchRowBudget (n L H a : ℕ) : ℕ :=
  (12*(H*(2000*(n+L+2)^4)^a)+5)*(n+L+2)

def weightedViolationRequestBudget (q n L H a : ℕ) : ℕ :=
  2048*(n+1)^4+(n+2*q+2)*weightedBranchRowBudget n L H a

def weightedForcedRequestBudget (q n L H a : ℕ) : ℕ :=
  521*(n+1)^3+(2*n+2*q+6)*weightedBranchRowBudget n L H a

/-- The two remaining request families use the same arithmetic envelope as
count requests. This bound prices every evaluated retained row. -/
theorem weightedBranchRows_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) :
    (∀ k, (weightedEvaluateRow A.arith (violationRowConstruction P k)).2 ≤
      weightedBranchRowBudget (Fintype.card (Item m)) A.base.L A.H A.a) ∧
    (∀ j u v k, (weightedEvaluateRow A.arith (forcedRowConstruction P j u v k)).2 ≤
      weightedBranchRowBudget (Fintype.card (Item m)) A.base.L A.H A.a) := by
  let n := Fintype.card (Item m)
  let S := n+A.base.L+2
  let K := A.H*(2000*S^4)^A.a
  have hpow : S^3 ≤ S^4 := pow_le_pow_right₀ (by dsimp [S]; omega) (by decide)
  have hen : 170*S^3 ≤ 2000*S^4 := by omega
  have ha : A.arith.Bounded (170*S^3) (K*(170*S^3)^0) := by
    simpa only [pow_zero,mul_one] using IntegerArithmeticCharge.Bounded.mono A.arith A.arithmetic_bound hen
  have toNatAbs (z : ℤ) (hz : |z| ≤ (A.base.M : ℤ)) : z.natAbs ≤ A.base.M := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (A.base.M : ℤ) by simpa only [Int.natCast_natAbs] using hz)
  have hq := coefficient_classes_le_items P hWF
  have hm := fun j => class_size_le_items (m := m) j
  constructor
  · intro k
    have h := weightedViolationRow_polynomial P n A.base.L A.base.M K 0 hq hm
      A.base.magnitude_pos A.base.magnitude_bits (fun i => toNatAbs _ (A.base.weights i))
      (fun j => toNatAbs _ (A.base.coefficients j)) (toNatAbs _ A.base.rhs)
      (toNatAbs _ A.base.capacity) A.arith ha k
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,pow_zero,mul_one,
      weightedBranchRowBudget,K,S,n] using h
  · intro j u v k
    have h := weightedForcedRow_polynomial P j u v n A.base.L A.base.M K 0 hq hm
      A.base.magnitude_pos A.base.magnitude_bits (fun i => toNatAbs _ (A.base.weights i))
      (fun j => toNatAbs _ (A.base.coefficients j)) (toNatAbs _ A.base.rhs)
      (toNatAbs _ A.base.capacity) A.arith ha k
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,pow_zero,mul_one,
      weightedBranchRowBudget,K,S,n] using h

theorem weightedBranchRequests_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) (hR : R ≤ Fintype.card (Item m)+1) :
    (weightedCompiledViolationRequest A.arith P A.base.R).2 ≤
      weightedViolationRequestBudget q (Fintype.card (Item m)) A.base.L A.H A.a ∧
    ∀ j u v, (weightedCompiledForcedRequest A.arith P j u v R).2 ≤
      weightedForcedRequestBudget q (Fintype.card (Item m)) A.base.L A.H A.a := by
  have hr := weightedBranchRows_cost P hWF solve A
  constructor
  · have h := weightedViolationRequest_cost A.arith P A.base.R _ hr.1
    have hb := compiledViolationRequest_cost P hWF A.base.R A.base.read_bound
    unfold weightedViolationRequestBudget
    omega
  · intro j u v
    have h := weightedForcedRequest_cost A.arith P j u v R _ (hr.2 j u v)
    have hb := compiledForcedRequest_cost P hWF j u v R hR
    have hp : (pairAllowed u v).card ≤ Fintype.card (Item m) :=
      (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans
        (class_size_le_items j)
    rw [forcedRowIndexList_length] at h
    unfold weightedForcedRequestBudget
    nlinarith

def weightedDenseForcedSolve (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (j : Fin q) (u v : Fin (m j)) : Option (IntegerRowSolution q) × ℕ :=
  let req := weightedCompiledForcedRequest arith P j u v R
  let out := solve req.1
  (out.1,req.2+out.2+1)

def weightedDenseViolationSolve (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    Option (IntegerRowSolution q) × ℕ :=
  let req := weightedCompiledViolationRequest arith P R
  let out := solve req.1
  (out.1,req.2+out.2+1)

theorem weightedDenseForcedSolve_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (j : Fin q) (u v : Fin (m j)) :
    (weightedDenseForcedSolve arith P R solve j u v).1 = denseForcedOracle P R solve j u v := by
  simp only [weightedDenseForcedSolve,weightedCompiledForcedRequest_value,denseForcedOracle,chargedDenseForcedSolve]

theorem weightedDenseViolationSolve_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    (weightedDenseViolationSolve arith P R solve).1 = (chargedDenseViolationSolve P R solve).1 := by
  simp only [weightedDenseViolationSolve,weightedCompiledViolationRequest_value,chargedDenseViolationSolve]

theorem weightedDenseBranchSolve_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) (hR : R ≤ Fintype.card (Item m)+1) :
    (weightedDenseViolationSolve A.arith P A.base.R solve).2 ≤
      weightedViolationRequestBudget q (Fintype.card (Item m)) A.base.L A.H A.a+
        A.base.I*(180*(Fintype.card (Item m)+A.base.L+2)^4)^A.base.c+1 ∧
    ∀ j u v, (weightedDenseForcedSolve A.arith P R solve j u v).2 ≤
      weightedForcedRequestBudget q (Fintype.card (Item m)) A.base.L A.H A.a+
        A.base.I*(180*(Fintype.card (Item m)+A.base.L+2)^4)^A.base.c+1 := by
  have hh := weightedBranchRequests_cost P hWF R solve A hR
  constructor
  · have hi := actualViolationSolver_cost P hWF A.base.M A.base.L A.base.magnitude_pos A.base.magnitude_bits
      A.base.weights A.base.coefficients A.base.capacity A.base.rhs A.base.R A.base.I A.base.c solve A.base.solver_cost
    dsimp only [weightedDenseViolationSolve]
    rw [weightedCompiledViolationRequest_value]
    omega
  · intro j u v
    have hi := actualForcedSolver_cost P hWF A.base.M A.base.L A.base.magnitude_pos A.base.magnitude_bits
      A.base.weights A.base.coefficients A.base.capacity A.base.rhs j u v R A.base.I A.base.c solve A.base.solver_cost
    have hb := hh.2 j u v
    dsimp only [weightedDenseForcedSolve]
    rw [weightedCompiledForcedRequest_value]
    omega

end MOR34
