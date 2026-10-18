import MOR34.ExecutableReturnedSets
import MOR34.OracleCostComposition
import MOR34.NormalSearchCost
import MOR34.ExecutableRawPipeline

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def adjacentPairKey (e : AdjacentPair m) : List ℕ := [e.val.1.val,e.val.2.1.val]

theorem adjacentPairKey_injective : Function.Injective (adjacentPairKey (m := m)) := by
  rintro ⟨⟨j,u,v⟩,h⟩ ⟨⟨k,w,t⟩,h'⟩ he
  change [j.val,u.val] = [k.val,w.val] at he
  have hj : j = k := Fin.ext (List.cons.inj he).1
  subst k
  have hu : u = w := Fin.ext (List.cons.inj (List.cons.inj he).2).1
  subst w
  change u.val+1 = v.val at h
  change u.val+1 = t.val at h'
  have hv : v = t := Fin.ext (by omega)
  subst t
  rfl

def adjacentPairLE (e f : AdjacentPair m) : Prop := adjacentPairKey e ≤ adjacentPairKey f

instance : DecidableRel (adjacentPairLE (m := m)) := fun e f =>
  inferInstanceAs (Decidable (adjacentPairKey e ≤ adjacentPairKey f))
instance : IsTrans (AdjacentPair m) adjacentPairLE where
  trans _ _ _ hab hbc := le_trans hab hbc
instance : IsAntisymm (AdjacentPair m) adjacentPairLE where
  antisymm _ _ hab hba := adjacentPairKey_injective (le_antisymm hab hba)
instance : IsTotal (AdjacentPair m) adjacentPairLE where
  total e f := le_total (adjacentPairKey e) (adjacentPairKey f)

/-- Evaluate each adjacent exchange once; later phases consume these answers. -/
def adjacentWitnessTable
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    List (AdjacentPair m × Option (Finset (Item m))) :=
  (Finset.univ.sort adjacentPairLE).map (fun e : AdjacentPair m =>
    (e, exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2))

def swapAtAdjacent (e : AdjacentPair m) (S : Finset (Item m)) : Finset (Item m) :=
  insert ⟨e.val.1,e.val.2.1⟩ (S.erase ⟨e.val.1,e.val.2.2⟩)

def edgePointsFromTable (T : List (AdjacentPair m × Option (Finset (Item m)))) :
    List (Finset (Item m)) :=
  T.flatMap fun p => match p.2 with
    | none => []
    | some S => [S, swapAtAdjacent p.1 S]

theorem adjacentWitnessTable_length
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    (adjacentWitnessTable solve).length ≤ Fintype.card (Item m) := by
  simpa [adjacentWitnessTable] using adjacentPair_card m

theorem edgePointsFromTable_length
    (T : List (AdjacentPair m × Option (Finset (Item m)))) :
    (edgePointsFromTable T).length ≤ 2*T.length := by
  unfold edgePointsFromTable
  apply (flatMap_length_bound T _ 2 ?_).trans_eq (by ring)
  intro p _
  cases p.2 <;> simp

theorem storedEdgePoints_length
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    (edgePointsFromTable (adjacentWitnessTable solve)).length ≤ 2*Fintype.card (Item m) :=
  (edgePointsFromTable_length _).trans (Nat.mul_le_mul_left 2 (adjacentWitnessTable_length solve))

theorem storedEdgePoints_mem
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (S : Finset (Item m)) :
    S ∈ edgePointsFromTable (adjacentWitnessTable solve) ↔
      ∃ (e : AdjacentPair m) (W : Finset (Item m)),
        exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2 = some W ∧
          (S = W ∨ S = swapAtAdjacent e W) := by
  simp only [edgePointsFromTable, adjacentWitnessTable, List.flatMap_map, List.mem_flatMap,
    Finset.mem_sort, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he⟩
    cases hw : exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2 with
    | none => simp [hw] at he
    | some W => exact ⟨e, W, hw, by simpa [hw] using he⟩
  · rintro ⟨e,W,hw,he⟩
    exact ⟨e, by simpa [hw] using he⟩

/-- The stored answers yield exactly the original returned exchange pair family. -/
theorem storedEdgePoints_eq (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    (edgePointsFromTable (adjacentWitnessTable solve)).toFinset =
      Finset.univ.image (computedEdgeWitness P hWF solve hs) ∪
      Finset.univ.image (computedEdgeSwap P hWF solve hs) := by
  ext S
  simp only [List.mem_toFinset, storedEdgePoints_mem, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e,W,hw,hS⟩
    have he : e ∈ computedEdges solve := by
      simp only [computedEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        exchangeDecision, hw, Option.isSome_some]
    let e' : computedEdges solve := ⟨e,he⟩
    have hW : computedEdgeWitness P hWF solve hs e' = W := by
      have hh := computedEdgeWitness_result P hWF solve hs e'
      rw [hw] at hh
      exact (Option.some.inj hh).symm
    rcases hS with rfl | rfl
    · exact Or.inl ⟨e',hW⟩
    · exact Or.inr ⟨e',by simp only [computedEdgeSwap, hW]; rfl⟩
  · rintro (⟨e,he⟩ | ⟨e,he⟩)
    · exact ⟨e.val, computedEdgeWitness P hWF solve hs e,
        computedEdgeWitness_result P hWF solve hs e, Or.inl he.symm⟩
    · exact ⟨e.val, computedEdgeWitness P hWF solve hs e,
        computedEdgeWitness_result P hWF solve hs e, Or.inr he.symm⟩

/-- Finite data storage preserves the exact returned set, not merely its span. -/
theorem storedReturnedSets_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) :
    (computedSelectionFamily P hWF solve hs).image prefixSet ∪
      (edgePointsFromTable (adjacentWitnessTable edgeSolve)).toFinset =
      computedReturnedSets P hWF solve hs edgeSolve he := by
  rw [storedEdgePoints_eq P hWF edgeSolve he]
  simp only [computedReturnedSets, Finset.union_assoc]

/-- The table construction has exactly one entry per adjacent pair. Each entry
uses one forced-row solve since its two indices are strictly ordered. -/
theorem adjacent_exchange_uses_one_solve
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (e : AdjacentPair m) :
    exchangeWitness solve e.val.1 e.val.2.1 e.val.2.2 =
      (solve e.val.1 e.val.2.1 e.val.2.2).map
        (fun s => forcedSet e.val.1 e.val.2.1 e.val.2.2 (decodeCounts s.1)) := by
  have hlt : e.val.2.1 < e.val.2.2 := by
    have hh := e.property
    change e.val.2.1.val < e.val.2.2.val
    omega
  simp only [exchangeWitness, if_pos hlt]

/-- Includes all stored edge solves in addition to support, extrema, and cell solves. -/
theorem all_solver_calls_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q+1) :
    rowSearchCalls P hWF solve hs forms + Fintype.card (AdjacentPair m) ≤
      (rowCallFactor q+1)*(Fintype.card (Item m)+1) := by
  have h₁ := rowSearchCalls_polynomial P hWF solve hs forms hsize
  have h₂ := adjacentPair_card m
  nlinarith


/-- Supported branch with the exchange answer table retained once. -/
def storedNormalizedPipeline (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  match executableRecognitionBranch (m := m) violate solve with
  | .invalid t => ⟨.invalid t, ∅⟩
  | .empty => ⟨.empty, ∅⟩
  | .supported z =>
    let table := adjacentWitnessTable edgeSolve
    let family := (computedSelectionFamily P hWF solve hs).image prefixSet ∪
      (edgePointsFromTable table).toFinset
    let B := binaryBasisSearch (orderedBinarySets family)
      (fun B => ranker.evaluate (binaryPointMatrix B))
    ⟨.supported (prefixSet z) (B.card-1) (decide (B.card = Fintype.card (Item m))), B⟩

theorem storedNormalizedPipeline_eq (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) :
    storedNormalizedPipeline P hWF solve hs edgeSolve violate ranker =
      executableNormalizedPipeline P hWF solve hs edgeSolve he violate ranker := by
  cases ho : executableRecognitionBranch (m := m) violate solve <;>
    simp only [storedNormalizedPipeline, executableNormalizedPipeline, ho, computedReturnedBasis,
      storedReturnedSets_eq P hWF solve hs edgeSolve he] <;> rfl

theorem storedNormalizedPipeline_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (storedNormalizedPipeline P hWF solve hs edgeSolve violate ranker).Correct P := by
  rw [storedNormalizedPipeline_eq P hWF solve hs edgeSolve he]
  exact executableNormalizedPipeline_correct P hWF solve hs edgeSolve he violate hv ranker

def RawNormalization.runStored {n : ℕ} {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) : RawOutput n :=
  relabelOutput N.itemEquiv (storedNormalizedPipeline N.model N.wellFormed
    s.solve s.solve_spec s.edgeSolve s.violate s.ranker)

theorem storedRawPipeline_eq {n : ℕ} {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    N.runStored s = N.runExecutable s := by
  unfold RawNormalization.runStored RawNormalization.runExecutable
  rw [storedNormalizedPipeline_eq N.model N.wellFormed s.solve s.solve_spec s.edgeSolve s.edge_spec]

theorem storedRawPipeline_correct {n : ℕ} {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.runStored s).Correct a c b d := by
  rw [storedRawPipeline_eq]
  exact executableRawPipeline_correct N s

end MOR34
