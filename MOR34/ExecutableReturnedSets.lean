import MOR34.ComputedNormalizedPipeline
import MOR34.OrderedBinarySets
import MOR34.StoredExtrema

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def computedParityFamily (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q)) (ε : Parity q) : Finset (Counts q) :=
  if h : (parityListSolver solve ε []).isSome then
    let z := (parityListSolver solve ε []).get h
    let hn : ∃ w, TightParity P ε w :=
      ⟨z, ((parityListSolver_spec P hWF solve hs ε).found [] z (Option.some_get h).symm).1⟩
    let e := storedParityExtrema (rowSearchedExtrema P hWF solve hs ε hn)
    Finset.univ.biUnion (fun mode : CellMode q => basisSearch
      (linearSpanOracle (rowCellOracle solve ε e mode) forms) (q + 1) ∅)
  else ∅
theorem computedParityFamily_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (forms : Finset (Counts q) → List (IntegerForm q)) (ε : Parity q) :
    computedParityFamily P hWF solve hs forms ε = executedParity P hWF solve hs forms ε := by
  simp only [computedParityFamily, executedParity, storedParityExtrema_eq]

def computedSelectionFamily (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : Finset (Counts q) :=
  Finset.univ.biUnion (computedParityFamily P hWF solve hs computedCountForms)

theorem computedSelectionFamily_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    computedSelectionFamily P hWF solve hs = selectionFinset P (computedCellSelection P hWF solve hs) := by
  rw [← computedCellSelection_executed]
  simp only [computedSelectionFamily, executedSelection, computedParityFamily_eq]

def computedReturnedSets (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) : Finset (Finset (Item m)) :=
  (computedSelectionFamily P hWF solve hs).image prefixSet ∪
    Finset.univ.image (computedEdgeWitness P hWF edgeSolve he) ∪
    Finset.univ.image (computedEdgeSwap P hWF edgeSolve he)

theorem computedReturnedSets_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) :
    computedReturnedSets P hWF solve hs edgeSolve he =
      returnedSets P hWF (computedCellSelection P hWF solve hs) edgeSolve he := by
  simp only [computedReturnedSets, computedSelectionFamily_eq, returnedSets]

end MOR34
