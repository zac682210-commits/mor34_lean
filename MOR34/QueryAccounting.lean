import MOR34.RowSolverPipeline
import MOR34.RecognitionBranches

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The sum of actual basis-search calls over the cells in one nonempty parity class. -/
noncomputable def rowCellCalls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (ε : Parity q) : ℕ := by
  classical
  exact if hn : ∃ z, TightParity P ε z then
    ∑ mode : CellMode q, linearBasisCalls
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms (q + 1) ∅
    else 0

theorem rowCellCalls_le (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q + 1) (ε : Parity q) :
    rowCellCalls P hWF solve hs forms ε ≤ 2 * (q + 1) ^ 2 * 3 ^ q := by
  classical
  unfold rowCellCalls
  split_ifs with hn
  · calc
      _ ≤ ∑ _mode : CellMode q, (2 * (q + 1) ^ 2) := by
        apply Finset.sum_le_sum
        intro mode _
        have hh := linearBasisCalls_le
          (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
          forms (q + 1) hsize (q + 1) ∅
        nlinarith
      _ = _ := by simp [CellMode, Nat.mul_comm]
  · exact Nat.zero_le _

theorem all_rowCellCalls_le (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q + 1) :
    (∑ ε : Parity q, rowCellCalls P hWF solve hs forms ε) ≤ 2 * (q + 1) ^ 2 * 6 ^ q := by
  calc
    _ ≤ ∑ _ε : Parity q, (2 * (q + 1) ^ 2 * 3 ^ q) :=
      Finset.sum_le_sum (fun ε _ => rowCellCalls_le P hWF solve hs forms hsize ε)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Nat.nsmul_eq_mul, Parity]
      rw [show (6 : ℕ) = 2 * 3 from rfl, mul_pow]
      ring

/-- An upper budget for the validity, support, extrema and cell phases.
It excludes edge discovery, normal construction, matrix rank and the work inside an ILP call.
The extrema term scans all parities, safely overcounting empty ones. -/
noncomputable def rowSearchCalls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) : ℕ :=
  1 + firstWitnessCalls (fun ε => parityListSolver solve ε []) (parityList q) +
    (∑ ε : Parity q, extremaSearchCalls (m := m) (rowBaseOracle solve ε)) +
    ∑ ε : Parity q, rowCellCalls P hWF solve hs forms ε

theorem rowSearchCalls_le (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q + 1) :
    rowSearchCalls P hWF solve hs forms ≤
      1 + 2 ^ q + 2 * (Fintype.card (Item m) + q) * 2 ^ q + 2 * (q + 1) ^ 2 * 6 ^ q := by
  have h₁ := supportSearch_calls_le solve
  have h₂ := all_parity_extrema_calls_le (m := m) (rowBaseOracle solve)
  have h₃ := all_rowCellCalls_le P hWF solve hs forms hsize
  unfold rowSearchCalls
  omega

/-- Coefficients in a cell call encode 3q cell rows and one separating query. -/
theorem cell_solver_row_count (l h : Counts q) (mode : CellMode q) (a : IntegerQuery q) :
    Fintype.card (CountRow m (a :: cellQueries l h mode).length) =
      Fintype.card (Item m) + 5 * q + 4 := by
  rw [countRow_card, List.length_cons, cellQueries_length]
  omega

end MOR34
