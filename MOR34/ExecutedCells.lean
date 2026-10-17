import MOR34.RowSolverPipeline
import MOR34.QueryAccounting

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Check the actual row-solver answer before entering a parity's cell search.
There is no decision procedure for a mathematical nonemptiness proposition here. -/
def executedCell (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (ε : Parity q) (mode : CellMode q) : Finset (Counts q) :=
  if h : (parityListSolver solve ε []).isSome then
    let z := (parityListSolver solve ε []).get h
    let hn : ∃ w, TightParity P ε w :=
      ⟨z, ((parityListSolver_spec P hWF solve hs ε).found [] z (Option.some_get h).symm).1⟩
    basisSearch (linearSpanOracle
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms) (q + 1) ∅
  else ∅

/-- The executable case split agrees with the structural selection, including empty parities. -/
theorem executedCell_eq_selectionCell (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (S : CellBasisSelection P)
    (hb : ∀ ε hn mode, S.basis ε hn mode = basisSearch
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms)
      (q + 1) ∅) (i : CellIndex q) :
    executedCell P hWF solve hs forms i.1 i.2 = selectionCell P S i := by
  classical
  cases he : parityListSolver solve i.1 [] with
  | none =>
    have hn : ¬ ∃ z, TightParity P i.1 z := by
      rintro ⟨z, hz⟩
      exact (parityListSolver_spec P hWF solve hs i.1).done [] he z hz (by simp [QueryAll])
    simp [executedCell, he, selectionCell, hn]
  | some z =>
    have hn : ∃ w, TightParity P i.1 w :=
      ⟨z, ((parityListSolver_spec P hWF solve hs i.1).found [] z he).1⟩
    simpa [executedCell, he, selectionCell, hn] using (hb i.1 hn i.2).symm

/-- One nonemptiness check per parity, hoisted outside the mode enumeration. -/
noncomputable def executedParity (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (ε : Parity q) : Finset (Counts q) :=
  if h : (parityListSolver solve ε []).isSome then
    let z := (parityListSolver solve ε []).get h
    let hn : ∃ w, TightParity P ε w :=
      ⟨z, ((parityListSolver_spec P hWF solve hs ε).found [] z (Option.some_get h).symm).1⟩
    let e := rowSearchedExtrema P hWF solve hs ε hn
    Finset.univ.biUnion (fun mode : CellMode q => basisSearch
      (linearSpanOracle (rowCellOracle solve ε e mode) forms) (q + 1) ∅)
  else ∅

theorem executedParity_eq_cells (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (ε : Parity q) :
    executedParity P hWF solve hs forms ε =
      Finset.univ.biUnion (fun mode : CellMode q => executedCell P hWF solve hs forms ε mode) := by
  classical
  cases he : parityListSolver solve ε [] <;> simp [executedParity, executedCell, he]
  ext z
  simp

noncomputable def executedSelection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) : Finset (Counts q) :=
  Finset.univ.biUnion (executedParity P hWF solve hs forms)

theorem executedSelection_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (S : CellBasisSelection P)
    (hb : ∀ ε hn mode, S.basis ε hn mode = basisSearch
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms)
      (q + 1) ∅) :
    executedSelection P hWF solve hs forms = selectionFinset P S := by
  classical
  ext z
  simp only [executedSelection, selectionFinset, Finset.mem_biUnion, Finset.mem_univ,
    true_and, executedParity_eq_cells]
  constructor
  · rintro ⟨ε, hz⟩
    obtain ⟨mode, hm⟩ := hz
    exact ⟨(ε, mode), by rwa [← executedCell_eq_selectionCell P hWF solve hs forms S hb]⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.1, i.2, ?_⟩
    rwa [executedCell_eq_selectionCell P hWF solve hs forms S hb]
end MOR34
