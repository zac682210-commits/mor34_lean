import MOR34.ComputedCellPipeline
import MOR34.SignedDimension
import MOR34.ExecutedCells

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Normalized output using the executable Cramer-form family in every cell search.
Other pipeline components (returned-point enumeration and rank interface) are unchanged. -/
noncomputable def computedNormalPipeline (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  let S := computedCellSelection P hWF solve hs
  match computedRecognition P S edgeSolve ranker.evaluate violate solve with
  | .invalid t => ⟨.invalid t, ∅⟩
  | .empty => ⟨.empty, ∅⟩
  | .supported t d b =>
    ⟨.supported t d b, binaryBasisSearch (returnedSets P hWF S edgeSolve he).toList
      (fun B => ranker.evaluate (binaryPointMatrix B))⟩


/-- Same mathematical output contract, now for the bounded normal-family pipeline. -/
theorem computedNormalPipeline_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (computedNormalPipeline P hWF solve hs edgeSolve he violate ranker).Correct P := by
  classical
  let S := computedCellSelection P hWF solve hs
  have hc := computedRecognition_correct P hWF S edgeSolve he
    ranker.evaluate ranker.correct violate hv solve hs
  have hr : ∀ B : Finset (Finset (Item m)),
      ranker.evaluate (binaryPointMatrix B) = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank :=
    fun B => ranker.correct _
  change (match computedRecognition P S edgeSolve ranker.evaluate violate solve with
    | .invalid t => (⟨.invalid t, ∅⟩ : NormalizedOutput m)
    | .empty => ⟨.empty, ∅⟩
    | .supported t d b => ⟨.supported t d b,
      binaryBasisSearch (returnedSets P hWF S edgeSolve he).toList
        (fun B => ranker.evaluate (binaryPointMatrix B))⟩).Correct P
  cases ho : computedRecognition P S edgeSolve ranker.evaluate violate solve with
  | invalid t =>
    rw [ho] at hc
    exact ⟨hc, rfl⟩
  | empty =>
    rw [ho] at hc
    exact ⟨hc, rfl⟩
  | supported t d b =>
    rw [ho] at hc
    have hT : (tightPointSet P).Nonempty := ⟨pointVector t, t, hc.2.1, rfl⟩
    have hb := searched_returned_basis P hWF S edgeSolve he
      (fun B => ranker.evaluate (binaryPointMatrix B)) hr
    have hcard := searched_returned_basis_card P hWF S edgeSolve he
      (fun B => ranker.evaluate (binaryPointMatrix B)) hr hT
    have hd : d = Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) := by
      rw [hc.2.2.1, candidateFace_vectorSpan P hc.1]
    exact ⟨hc, hb.1, hb.2.2.1, hb.2.2.2, by simpa [hd] using hcard⟩

theorem computedNormalPipeline_dimension (P : Model m) (hWF : WellFormed P) (hv : Valid P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hviol : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (computedNormalPipeline P hWF solve hs edgeSolve he violate ranker).decision.dimension =
      some (candidateFaceDimension P) :=
  correct_output_dimension P _
    (computedNormalPipeline_correct P hWF solve hs edgeSolve he violate hviol ranker).1 hv

theorem computedNormalPipeline_facet (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hviol : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (computedNormalPipeline P hWF solve hs edgeSolve he violate ranker).decision.isFacet = true ↔ DefinesFacet P :=
  correct_output_facet P _
    (computedNormalPipeline_correct P hWF solve hs edgeSolve he violate hviol ranker).1

theorem computedCellSelection_executed (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    executedSelection P hWF solve hs computedCountForms =
      selectionFinset P (computedCellSelection P hWF solve hs) :=
  executedSelection_eq P hWF solve hs computedCountForms _
    (computedCellSelection_basis P hWF solve hs)

end MOR34
