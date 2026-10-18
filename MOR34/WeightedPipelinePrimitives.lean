import MOR34.PreparedCellExecution
import MOR34.WeightedExtrema

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Only local arithmetic, matrix preparation, collection and established solver
contracts are stored here. No total cell/selection/algorithm cost is assumed. -/
structure WeightedPipelinePrimitives (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) where
  base : DenseCellPrimitives P solve
  arith : IntegerArithmeticCharge
  H : ℕ
  a : ℕ
  arithmetic_bound : arith.Bounded (2000*(Fintype.card (Item m)+base.L+2)^4)
    (H*(2000*(Fintype.card (Item m)+base.L+2)^4)^a)
  prep : CountMatrixPreparation q
  unit : ℕ
  normal_arithmetic_bound : arith.Bounded (normalWorkBits q (Fintype.card (Item m))) unit
  prepCost : ℕ
  preparation_bound : ∀ B : Finset (Counts q), B.card ≤ q+1 →
    (∀ z ∈ B, BoundedCounts (m := m) z) → (prep.emit B).2 ≤ prepCost

def preparedWeightedCell (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : WeightedPipelinePrimitives P solve) (ε : Parity q) (e : ParityExtrema P ε)
    (mode : CellMode q) : Finset (Counts q) × ℕ :=
  preparedCellBasis A.prep A.unit A.base.N
    (weightedDenseCellQuery A.arith P A.base.R A.base.D solve ε e mode) A.base.put

def preparedWeightedCellBudget (q n L N D I c J H a unit E : ℕ) : ℕ :=
  (q+1)*(preparedCellStepBudget q unit E N (weightedCellQueryBudget q n L D I c H a)+J+1)+1

theorem preparedWeightedCell_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    (preparedWeightedCell P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs) ε hn) mode).1 =
      (computedCellSelection P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs)).basis ε hn mode := by
  rw [preparedWeightedCell,preparedCellBasis_value _ _ _ _ _ A.base.put_value,computedCellSelection_basis]
  simp only [weightedDenseCellQuery_value]

theorem preparedWeightedCell_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    (preparedWeightedCell P solve A ε
      (rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs) ε hn) mode).2 ≤
      preparedWeightedCellBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I
        A.base.c A.base.J A.H A.a A.unit A.prepCost := by
  let e := rowSearchedExtrema P hWF (denseCountOracle P A.base.R solve)
    (denseCountOracle_spec P A.base.R solve hs) ε hn
  have hquery : (fun t => (weightedDenseCellQuery A.arith P A.base.R A.base.D solve ε e mode t).1) =
      rowCellOracle (denseCountOracle P A.base.R solve) ε e mode :=
    funext (weightedDenseCellQuery_value A.arith P A.base.R A.base.D solve ε e mode)
  apply preparedCellBasis_cost_on_states A.prep (parityCellSet P ε e mode)
  · rw [hquery]
    exact rowCellOracle_spec P hWF _ (denseCountOracle_spec P A.base.R solve hs) ε e mode
  · exact A.base.put_value
  · intro z B hcard hz hB
    exact A.base.put_cost z B hcard hz.1.1 (fun x hx => (hB hx).1.1)
  · intro B hcard hB
    exact A.preparation_bound B hcard (fun x hx => (hB hx).1.1)
  · rw [hquery]
    exact weightedCellQuery_cost_on_states P hWF solve hs A.base.R A.base.D A.base.I A.base.c
      A.base.M A.base.L A.H A.a A.base.read_bound A.base.solver_cost A.base.magnitude_pos
      A.base.magnitude_bits A.base.weights A.base.coefficients A.base.capacity A.base.rhs
      A.arith A.arithmetic_bound ε hn mode

end MOR34
