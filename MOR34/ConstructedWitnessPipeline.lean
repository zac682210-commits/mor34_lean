import MOR34.AllResidualTables

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The exchange table uses the explicitly generated successor list. -/
def constructedWitnessTable
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    List (AdjacentPair m × Option (Finset (Item m))) :=
  (chargedAdjacentIndices m).1.map (fun e : AdjacentPair m =>
    (e, exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2))

theorem constructedWitnessTable_length
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    (constructedWitnessTable solve).length ≤ Fintype.card (Item m) := by
  simpa [constructedWitnessTable] using (chargedAdjacentIndices_length (m := m))

theorem constructedEdgePoints_mem
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (S : Finset (Item m)) :
    S ∈ edgePointsFromTable (constructedWitnessTable solve) ↔
      ∃ (e : AdjacentPair m) (W : Finset (Item m)),
        exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2 = some W ∧
          (S = W ∨ S = swapAtAdjacent e W) := by
  simp only [edgePointsFromTable, constructedWitnessTable, List.flatMap_map, List.mem_flatMap]
  constructor
  · rintro ⟨e,_,he⟩
    cases hw : exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2 with
    | none => simp [hw] at he
    | some W => exact ⟨e,W,hw,by simpa [hw] using he⟩
  · rintro ⟨e,W,hw,he⟩
    exact ⟨e,chargedAdjacentIndices_complete e,by simpa [hw] using he⟩

theorem constructedEdgePoints_eq_stored
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    (edgePointsFromTable (constructedWitnessTable solve)).toFinset =
      (edgePointsFromTable (adjacentWitnessTable solve)).toFinset := by
  ext S
  simp only [List.mem_toFinset, constructedEdgePoints_mem, storedEdgePoints_mem]

theorem constructedReturnedSets_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) :
    (computedSelectionFamily P hWF solve hs).image prefixSet ∪
      (edgePointsFromTable (constructedWitnessTable edgeSolve)).toFinset =
      computedReturnedSets P hWF solve hs edgeSolve he := by
  rw [constructedEdgePoints_eq_stored]
  exact storedReturnedSets_eq P hWF solve hs edgeSolve he

def constructedNormalizedPipeline (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  match executableRecognitionBranch (m := m) violate solve with
  | .invalid t => ⟨.invalid t, ∅⟩
  | .empty => ⟨.empty, ∅⟩
  | .supported z =>
    let table := constructedWitnessTable edgeSolve
    let family := (computedSelectionFamily P hWF solve hs).image prefixSet ∪
      (edgePointsFromTable table).toFinset
    let B := binaryBasisSearch (orderedBinarySets family)
      (fun B => ranker.evaluate (binaryPointMatrix B))
    ⟨.supported (prefixSet z) (B.card-1) (decide (B.card = Fintype.card (Item m))), B⟩

theorem constructedNormalizedPipeline_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) :
    constructedNormalizedPipeline P hWF solve hs edgeSolve violate ranker =
      storedNormalizedPipeline P hWF solve hs edgeSolve violate ranker := by
  cases ho : executableRecognitionBranch (m := m) violate solve <;>
    simp only [constructedNormalizedPipeline, storedNormalizedPipeline, ho,
      constructedEdgePoints_eq_stored] <;> rfl

theorem constructedNormalizedPipeline_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (constructedNormalizedPipeline P hWF solve hs edgeSolve violate ranker).Correct P := by
  rw [constructedNormalizedPipeline_eq]
  exact storedNormalizedPipeline_correct P hWF solve hs edgeSolve he violate hv ranker

end MOR34
