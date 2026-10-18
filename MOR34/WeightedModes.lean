import MOR34.WeightedPipelinePrimitives

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedDenseModes (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) (ε : Parity q) (e : ParityExtrema P ε) :
    List (Counts q) × ℕ :=
  chargedModeFamily (fun mode => preparedWeightedCell P solve A ε e mode) A.base.serialize

theorem weightedDenseModes_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (weightedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs) ε hn)).1.toFinset =
      Finset.univ.biUnion (fun mode =>
        (computedCellSelection P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs)).basis ε hn mode) := by
  rw [weightedDenseModes,chargedModeFamily_value _ _ A.base.serialize_value]
  simp only [preparedWeightedCell_value P hWF solve hs A ε hn _]

theorem weightedDenseModes_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (weightedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs) ε hn)).2 ≤
      functionEnumerationBudget q 3+3^q*
        (preparedWeightedCellBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.H A.a A.unit A.prepCost+A.base.E+q+3)+1 := by
  let e := rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs) ε hn
  let cell := fun mode => preparedWeightedCell P solve A ε e mode
  let S := computedCellSelection P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs)
  have hv (mode : CellMode q) : (cell mode).1 = S.basis ε hn mode :=
    preparedWeightedCell_value P hWF solve hs A ε hn mode
  have hsmall (mode : CellMode q) : (cell mode).1.card ≤ q+1 := by
    rw [hv]
    exact computedCellSelection_small P hWF _ _ ε hn mode
  have hbound (mode : CellMode q) : ∀ x ∈ (cell mode).1, BoundedCounts (m := m) x := by
    intro x hx
    rw [hv] at hx
    exact (S.contained ε hn mode hx).1.1
  have hh := chargedModeFamily_cost cell A.base.serialize
    (preparedWeightedCellBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.H A.a A.unit A.prepCost) A.base.E (q+1)
    (fun mode => preparedWeightedCell_cost P hWF solve hs A ε hn mode)
    (fun mode => A.base.serialize_cost _ (hsmall mode) (hbound mode))
    (fun mode => by rw [A.base.serialize_length]; exact hsmall mode)
  simpa only [Nat.add_assoc] using hh

theorem weightedDenseModes_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (weightedDenseModes P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs) ε hn)).1.length ≤ 3^q*(q+1) := by
  apply chargedModeFamily_length
  intro mode
  rw [A.base.serialize_length,preparedWeightedCell_value P hWF solve hs A ε hn mode]
  exact computedCellSelection_small P hWF _ _ ε hn mode

end MOR34
