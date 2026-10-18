import MOR34.ChargedExchangeExecution
import MOR34.ChargedBinaryRank

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def retainedFamilyLength (q n : ℕ) : ℕ := (q+1)*6^q+2*n

def chargedReturnedFamily (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ops : PointOperations m) :
    List (Finset (Item m)) × ℕ :=
  let selected := chargedDenseSelection P hWF solve hs A
  let prefixes := chargedMap ops.makePrefix selected.1
  let edges := chargedDenseEdges P R solve ops
  (prefixes.1++edges.1,selected.2+prefixes.2+edges.2+prefixes.1.length+1)

theorem chargedReturnedFamily_value (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ops : PointOperations m) :
    (chargedReturnedFamily P hWF R solve hs A ops).1.toFinset =
      computedReturnedSets P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs)
        (denseForcedOracle P R solve) (denseForcedOracle_spec P R solve hs) := by
  simp only [chargedReturnedFamily,List.toFinset_append,chargedMap_value,ops.makePrefix_value,
    chargedDenseEdges_value]
  have hp : ((chargedDenseSelection P hWF solve hs A).1.map (fun z => prefixSet (m := m) z)).toFinset =
      (chargedDenseSelection P hWF solve hs A).1.toFinset.image (prefixSet (m := m)) := by
    ext S
    simp
  rw [hp,chargedDenseSelection_value]
  exact constructedReturnedSets_eq P hWF _ _ _ (denseForcedOracle_spec P R solve hs)

theorem chargedReturnedFamily_length (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ops : PointOperations m) :
    (chargedReturnedFamily P hWF R solve hs A ops).1.length ≤ retainedFamilyLength q (Fintype.card (Item m)) := by
  have hsel := chargedDenseSelection_length P hWF solve hs A
  have he := (edgePointsFromTable_length (constructedWitnessTable (denseForcedOracle P R solve))).trans
    (Nat.mul_le_mul_left 2 (constructedWitnessTable_length (denseForcedOracle P R solve)))
  simp only [chargedReturnedFamily,List.length_append,chargedMap_value,List.length_map,chargedDenseEdges_value]
  unfold retainedFamilyLength
  omega

def selectionExecutionBudget (q n L N D I c J E : ℕ) : ℕ :=
  functionEnumerationBudget q 2+2^q*(denseParityBudget q n L N D I c J E+3^q*(q+1)+1)+1

def returnedFamilyBudget (q n L N D I c J E C : ℕ) : ℕ :=
  selectionExecutionBudget q n L N D I c J E+(q+1)*6^q*(C+2)+edgeExecutionBudget n L I c C+1

theorem chargedReturnedFamily_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (hR : R ≤ Fintype.card (Item m)+1) (ops : PointOperations m) (C : ℕ)
    (ho : PointOperationBounds ops C) :
    (chargedReturnedFamily P hWF R solve hs A ops).2 ≤
      returnedFamilyBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E C := by
  have hs' := chargedDenseSelection_cost P hWF solve hs A
  have hl := chargedDenseSelection_length P hWF solve hs A
  have hp := chargedMap_cost ops.makePrefix (chargedDenseSelection P hWF solve hs A).1 C
    (fun z hz => ho.prefix_cost z (chargedDenseSelection_points P hWF solve hs A z hz).1)
  have hp' := hp.trans (Nat.mul_le_mul_right (C+1) hl)
  have he := chargedDenseEdges_cost P hWF R solve hs A hR ops C ho
  dsimp only [chargedReturnedFamily]
  simp only [chargedMap_value,List.length_map]
  unfold returnedFamilyBudget selectionExecutionBudget
  nlinarith

end MOR34
