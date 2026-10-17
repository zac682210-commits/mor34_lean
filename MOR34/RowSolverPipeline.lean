import MOR34.ParitySolver
import MOR34.SearchedExtrema
import MOR34.RetainedMatrix

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def rowBaseOracle
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) (ε : Parity q) :=
  restrictedQueryOracle (parityListSolver solve ε) []

theorem rowBaseOracle_spec (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) :
    LinearOracleSpec {z | TightParity P ε z} (rowBaseOracle solve ε) :=
  unrestrictedQueryOracle_spec _ _ (parityListSolver_spec P hWF solve hs ε)

def rowSearchedExtrema (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    ParityExtrema P ε :=
  searchedParityExtrema P ε (rowBaseOracle solve ε) (rowBaseOracle_spec P hWF solve hs ε) hn

def rowCellOracle (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (ε : Parity q) {P : Model m} (e : ParityExtrema P ε) (mode : CellMode q) :=
  restrictedQueryOracle (parityListSolver solve ε) (cellQueries e.low e.high mode)

theorem rowCellOracle_spec (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) :
    LinearOracleSpec (parityCellSet P ε e mode) (rowCellOracle solve ε e mode) :=
  parityCellOracle_spec P ε e mode _ (parityListSolver_spec P hWF solve hs ε)

/-- The explicit row solver supplies both attained extrema and every cell search.
Integer normals remain classical; adjacency enumeration and total runtime are not asserted. -/
theorem row_solver_cell_selection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q), ∃ S : CellBasisSelection P,
      S.extrema = rowSearchedExtrema P hWF solve hs ∧
      (∀ ε hn mode, S.basis ε hn mode = basisSearch
        (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms)
        (q + 1) ∅) ∧
      (∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) ∧
      (∀ ε hn mode, AffineIndependent ℝ (fun z : S.basis ε hn mode => countReal z.val)) ∧
      (∀ ε hn mode, linearBasisCalls
        (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms (q + 1) ∅ ≤
          2 * (q + 1) ^ 2) := by
  exact oracle_cell_basis_selection P (rowSearchedExtrema P hWF solve hs)
    (fun ε hn mode => rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
    (fun ε hn mode => rowCellOracle_spec P hWF solve hs ε _ mode)

/-- Rank correctness for the selected matrix produced using the row-solver cell searches.
The matrix still uses the mathematically specified adjacent-edge set. -/
theorem row_solver_retained_matrix (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (hT : (tightPointSet P).Nonempty) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q), ∃ S : CellBasisSelection P,
      S.extrema = rowSearchedExtrema P hWF solve hs ∧
      (∀ ε hn mode, S.basis ε hn mode = basisSearch
        (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms)
        (q + 1) ∅) ∧
      Fintype.card (RetainedRowIndex P S) ≤ Fintype.card (Item m) + (q + 1) * 6 ^ q ∧
      ((retainedMatrix P S).map (Int.castRingHom ℚ)).rank =
        Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  obtain ⟨forms, S, hex, hb, hc, _, _⟩ := row_solver_cell_selection P hWF solve hs
  exact ⟨forms, S, hex, hb, retainedRowIndex_card P S hc, retained_matrix_rational_rank P hWF S hT⟩

end MOR34
