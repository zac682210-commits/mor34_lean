import MOR34.ChargedModeFamily

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Local assumptions for the cell-selection phase. Each cost premise concerns
an established solver or one finite-collection operation, never the composed
algorithm. Scalar charges R, D, N are still arithmetic reference allowances. -/
structure DenseCellPrimitives (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) where
  R : ℕ
  D : ℕ
  N : ℕ
  I : ℕ
  c : ℕ
  J : ℕ
  E : ℕ
  M : ℕ
  L : ℕ
  read_bound : R ≤ 4*(Fintype.card (Item m)+1)^2
  magnitude_pos : 1 ≤ M
  magnitude_bits : M ≤ 2^L
  weights : ∀ i, |P.weight i| ≤ (M : ℤ)
  coefficients : ∀ j, |P.coefficient j| ≤ (M : ℤ)
  capacity : |P.capacity| ≤ (M : ℤ)
  rhs : |P.rhs| ≤ (M : ℤ)
  solver_cost : DenseSolverCostBound solve I c
  put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ
  put_value : ∀ z B, (put z B).1 = insert z B
  put_cost : ∀ z B, B.card ≤ q+1 → BoundedCounts (m := m) z →
    (∀ x ∈ B, BoundedCounts (m := m) x) → (put z B).2 ≤ J
  serialize : Finset (Counts q) → List (Counts q) × ℕ
  serialize_value : ∀ B, (serialize B).1.toFinset = B
  serialize_length : ∀ B, (serialize B).1.length = B.card
  serialize_cost : ∀ B, B.card ≤ q+1 →
    (∀ x ∈ B, BoundedCounts (m := m) x) → (serialize B).2 ≤ E

def chargedDenseModes (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : DenseCellPrimitives P solve) (ε : Parity q) (e : ParityExtrema P ε) :
    List (Counts q) × ℕ :=
  chargedModeFamily (fun mode => chargedDenseCellBasis P A.R A.D A.N solve ε e mode A.put) A.serialize

theorem chargedDenseModes_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (chargedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs) ε hn)).1.toFinset =
      Finset.univ.biUnion (fun mode =>
        (computedCellSelection P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs)).basis ε hn mode) := by
  rw [chargedDenseModes,chargedModeFamily_value _ _ A.serialize_value]
  simp only [chargedDenseCellBasis_value P hWF A.R A.D A.N solve hs ε hn _ _ A.put_value]

theorem chargedDenseModes_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (chargedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs) ε hn)).2 ≤
      functionEnumerationBudget q 3+3^q*
        (denseCellLoopBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J+A.E+q+3)+1 := by
  let e := rowSearchedExtrema P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs) ε hn
  let cell := fun mode => chargedDenseCellBasis P A.R A.D A.N solve ε e mode A.put
  let S := computedCellSelection P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs)
  have hv (mode : CellMode q) : (cell mode).1 = S.basis ε hn mode :=
    chargedDenseCellBasis_value P hWF A.R A.D A.N solve hs ε hn mode _ A.put_value
  have hsmall (mode : CellMode q) : (cell mode).1.card ≤ q+1 := by
    rw [hv]
    exact computedCellSelection_small P hWF _ _ ε hn mode
  have hbound (mode : CellMode q) : ∀ x ∈ (cell mode).1, BoundedCounts (m := m) x := by
    intro x hx
    rw [hv] at hx
    exact (S.contained ε hn mode hx).1.1
  have hh := chargedModeFamily_cost cell A.serialize
    (denseCellLoopBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J) A.E (q+1)
    (fun mode => chargedDenseCellBasis_cost P hWF solve hs A.R A.D A.N A.I A.c A.J
      A.read_bound A.solver_cost A.M A.L A.magnitude_pos A.magnitude_bits
      A.weights A.coefficients A.capacity A.rhs ε hn mode A.put A.put_value A.put_cost)
    (fun mode => A.serialize_cost _ (hsmall mode) (hbound mode))
    (fun mode => by rw [A.serialize_length]; exact hsmall mode)
  simpa only [Nat.add_assoc] using hh

theorem chargedDenseModes_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (chargedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs) ε hn)).1.length ≤ 3^q*(q+1) := by
  apply chargedModeFamily_length
  intro mode
  rw [A.serialize_length,chargedDenseCellBasis_value P hWF A.R A.D A.N solve hs ε hn mode _ A.put_value]
  exact computedCellSelection_small P hWF _ _ ε hn mode

end MOR34
