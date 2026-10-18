import MOR34.ChargedParityFamily

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def chargedDenseSupport (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    Option (Counts q) × ℕ :=
  let parities := chargedFinFunctions q 2
  let out := chargedFirstWitness (fun ε => chargedDenseListQuery P R D solve ε []) parities.1
  (out.1,parities.2+out.2+1)

theorem chargedDenseSupport_value (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    (chargedDenseSupport P R D solve).1 = executableSupportSearch (denseCountOracle P R solve) := by
  simp only [chargedDenseSupport,chargedFirstWitness_value,chargedFinFunctions_value,
    chargedDenseListQuery_value,executableSupportSearch,executableParityList]

theorem chargedDenseSupport_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : DenseCellPrimitives P solve) :
    (chargedDenseSupport P A.R A.D solve).2 ≤ functionEnumerationBudget q 2+
      2^q*(denseCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c+1)+2 := by
  let U := denseCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c
  have hc (ε : Parity q) : (chargedDenseListQuery P A.R A.D solve ε []).2 ≤ U :=
    chargedDenseListQuery_cost P hWF A.R A.D A.I A.c A.M A.L A.read_bound
      A.magnitude_pos A.magnitude_bits A.weights A.coefficients A.capacity A.rhs solve A.solver_cost
      ε [] (by simp) (by simp)
  have hh := chargedFirstWitness_cost (fun ε => chargedDenseListQuery P A.R A.D solve ε [])
    (chargedFinFunctions q 2).1 U (fun ε _ => hc ε)
  have hn := firstWitness_calls_le (fun ε => (chargedDenseListQuery P A.R A.D solve ε []).1)
    (chargedFinFunctions q 2).1
  have hl : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hl] at hn
  have hs := hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (U+1) hn) 1)
  have he := chargedFinFunctions_cost q 2
  dsimp only [chargedDenseSupport]
  change _ ≤ functionEnumerationBudget q 2+2^q*(U+1)+2
  omega

/-- Local decoding/finite-set construction callbacks; no phase cost is assumed. -/
structure PointOperations (m : Fin q → ℕ) where
  makePrefix : Counts q → Finset (Item m) × ℕ
  makePrefix_value : ∀ z, (makePrefix z).1 = prefixSet z
  forced : (j : Fin q) → Fin (m j) → Fin (m j) → (Fin q → ℤ) → Finset (Item m) × ℕ
  forced_value : ∀ j u v z, (forced j u v z).1 = forcedSet j u v (decodeCounts z)
  invalid : (Fin q → ℤ) → Finset (Item m) × ℕ
  invalid_value : ∀ z, (invalid z).1 = prefixSet (decodeCounts z)
  swap : AdjacentPair m → Finset (Item m) → Finset (Item m) × ℕ
  swap_value : ∀ e S, (swap e S).1 = swapAtAdjacent e S

/-- Bounds are imposed only on finite coordinates, as actually returned by the
correct integer solvers. Unused epigraph coordinates are not read. -/
structure PointOperationBounds (ops : PointOperations m) (C : ℕ) : Prop where
  prefix_cost : ∀ z, BoundedCounts (m := m) z → (ops.makePrefix z).2 ≤ C
  forced : ∀ j u v z, IntegerCountBounds (m := m) z → (ops.forced j u v z).2 ≤ C
  invalid : ∀ z, IntegerCountBounds (m := m) z → (ops.invalid z).2 ≤ C
  swap : ∀ e S, (ops.swap e S).2 ≤ C

def chargedDenseRecognition (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : RecognitionBranch m × ℕ :=
  let violation := chargedDenseViolationSolve P R solve
  match violation.1 with
  | some s => let t := ops.invalid s.1
              (.invalid t.1,violation.2+t.2+1)
  | none => let support := chargedDenseSupport P R D solve
            (match support.1 with | none => .empty | some z => .supported z,
             violation.2+support.2+1)

theorem chargedDenseRecognition_value (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (chargedDenseRecognition P R D solve ops).1 =
      executableRecognitionBranch (m := m) (chargedDenseViolationSolve P R solve).1
        (denseCountOracle P R solve) := by
  simp only [chargedDenseRecognition,executableRecognitionBranch,chargedDenseSupport_value]
  cases (chargedDenseViolationSolve P R solve).1 <;> simp only [ops.invalid_value]
  · cases executableSupportSearch (denseCountOracle P R solve) <;> rfl

def recognitionBudget (q n L D I c C : ℕ) : ℕ :=
  2048*(n+1)^4+I*(180*(n+L+2)^4)^c+functionEnumerationBudget q 2+
    2^q*(denseCellQueryBudget q n L D I c+1)+C+4

theorem chargedDenseRecognition_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (ops : PointOperations m) (C : ℕ) (hops : PointOperationBounds ops C) :
    (chargedDenseRecognition P A.R A.D solve ops).2 ≤
      recognitionBudget q (Fintype.card (Item m)) A.L A.D A.I A.c C := by
  have hi := actualViolationSolver_cost P hWF A.M A.L A.magnitude_pos A.magnitude_bits
    A.weights A.coefficients A.capacity A.rhs A.R A.I A.c solve A.solver_cost
  have hv := chargedDenseViolationSolve_cost P hWF A.R solve _ A.read_bound hi
  have hsup := chargedDenseSupport_cost P hWF solve A
  dsimp only [chargedDenseRecognition]
  split
  · rename_i s he
    have hb := ((violationRows_iff P s.1 s.2).mp ((denseViolation_spec P A.R solve hs).found s he)).1.1
    have ho := hops.invalid s.1 hb
    unfold recognitionBudget
    omega
  · unfold recognitionBudget
    omega

end MOR34
