import MOR34.StoredEdgeWitnesses
import MOR34.ComputedRankPayload
import MOR34.ParameterFactors

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Length of a binary vector's explicit nested coordinate encoding. -/
theorem binarySetKey_coordinate_count (S : Finset (Item m)) :
    ((binarySetKey S).map List.length).sum = Fintype.card (Item m) := by
  simp [binarySetKey, Function.comp_def, List.sum_ofFn, Item, Fintype.card_sigma]

/-- A deliberately simple pairwise comparison implementation needs a fixed
polynomial number of coordinate visits. This is a count of its prescribed
comparison schedule, independent of a backend's sort implementation. -/
def allPairsCoordinateWork (n points : ℕ) : ℕ := points*points*(n+1)

theorem returnedFamily_pairwise_work (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) :
    allPairsCoordinateWork (Fintype.card (Item m))
      (computedReturnedSets P hWF solve hs edgeSolve he).card ≤
      (((q+1)*6^q+2)^2)*(Fintype.card (Item m)+1)^3 := by
  have hlen : (computedReturnedSets P hWF solve hs edgeSolve he).card ≤
      (q+1)*6^q+2*Fintype.card (Item m) := by
    rw [computedReturnedSets_eq]
    exact returnedSets_card P hWF (computedCellSelection P hWF solve hs) edgeSolve he
      (computedCellSelection_small P hWF solve hs)
  have hp : (computedReturnedSets P hWF solve hs edgeSolve he).card ≤
      ((q+1)*6^q+2)*(Fintype.card (Item m)+1) := by
    apply hlen.trans
    have hh := Nat.le_mul_of_pos_right ((q+1)*6^q)
      (show 0 < Fintype.card (Item m)+1 by omega)
    nlinarith
  unfold allPairsCoordinateWork
  calc
    _ ≤ (((q+1)*6^q+2)*(Fintype.card (Item m)+1))*
        (((q+1)*6^q+2)*(Fintype.card (Item m)+1))*(Fintype.card (Item m)+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hp hp)
    _ = _ := by ring

/-- Preallocation/emission of every vector uses the same fixed-degree envelope. -/
theorem returnedFamily_coordinate_work (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) :
    (computedReturnedSets P hWF solve hs edgeSolve he).card*(Fintype.card (Item m)+1) ≤
      ((q+1)*6^q+2)*(Fintype.card (Item m)+1)^2 := by
  have hlen : (computedReturnedSets P hWF solve hs edgeSolve he).card ≤
      (q+1)*6^q+2*Fintype.card (Item m) := by
    rw [computedReturnedSets_eq]
    exact returnedSets_card P hWF (computedCellSelection P hWF solve hs) edgeSolve he
      (computedCellSelection_small P hWF solve hs)
  have hp : (q+1)*6^q+2*Fintype.card (Item m) ≤
      ((q+1)*6^q+2)*(Fintype.card (Item m)+1) := by
    have hh := Nat.le_mul_of_pos_right ((q+1)*6^q)
      (show 0 < Fintype.card (Item m)+1 by omega)
    nlinarith
  exact (Nat.mul_le_mul_right _ (hlen.trans hp)).trans_eq (by ring)

end MOR34
