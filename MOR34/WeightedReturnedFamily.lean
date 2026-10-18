import MOR34.WeightedExchange
import MOR34.ChargedReturnedFamily
import MOR34.ChargedBinaryRank

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedReturnedFamily (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ops : PointOperations m) :
    List (Finset (Item m)) × ℕ :=
  let selected := weightedDenseSelection P hWF solve hs A
  let prefixes := chargedMap ops.makePrefix selected.1
  let edges := weightedDenseEdges A.arith P R solve ops
  (prefixes.1++edges.1,selected.2+prefixes.2+edges.2+prefixes.1.length+1)

theorem weightedReturnedFamily_value (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ops : PointOperations m) :
    (weightedReturnedFamily P hWF R solve hs A ops).1.toFinset =
      computedReturnedSets P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs)
        (denseForcedOracle P R solve) (denseForcedOracle_spec P R solve hs) := by
  simp only [weightedReturnedFamily,List.toFinset_append,chargedMap_value,ops.makePrefix_value,
    weightedDenseEdges_value]
  have hp : ((weightedDenseSelection P hWF solve hs A).1.map (fun z => prefixSet (m := m) z)).toFinset =
      (weightedDenseSelection P hWF solve hs A).1.toFinset.image (prefixSet (m := m)) := by
    ext S
    simp
  rw [hp,weightedDenseSelection_value]
  exact constructedReturnedSets_eq P hWF _ _ _ (denseForcedOracle_spec P R solve hs)

theorem weightedReturnedFamily_length (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ops : PointOperations m) :
    (weightedReturnedFamily P hWF R solve hs A ops).1.length ≤ retainedFamilyLength q (Fintype.card (Item m)) := by
  have hsel := weightedDenseSelection_length P hWF solve hs A
  have he := (edgePointsFromTable_length (constructedWitnessTable (denseForcedOracle P R solve))).trans
    (Nat.mul_le_mul_left 2 (constructedWitnessTable_length (denseForcedOracle P R solve)))
  simp only [weightedReturnedFamily,List.length_append,chargedMap_value,List.length_map,weightedDenseEdges_value]
  unfold retainedFamilyLength
  omega

def weightedSelectionExecutionBudget (q n L N D I c J E H a unit prep : ℕ) : ℕ :=
  functionEnumerationBudget q 2+2^q*(weightedParityBudget q n L N D I c J E H a unit prep+3^q*(q+1)+1)+1

def weightedReturnedFamilyBudget (q n L N D I c J E C H a unit prep : ℕ) : ℕ :=
  weightedSelectionExecutionBudget q n L N D I c J E H a unit prep+(q+1)*6^q*(C+2)+weightedEdgeExecutionBudget q n L I c C H a+1

theorem weightedReturnedFamily_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (hR : R ≤ Fintype.card (Item m)+1) (ops : PointOperations m) (C : ℕ)
    (ho : PointOperationBounds ops C) :
    (weightedReturnedFamily P hWF R solve hs A ops).2 ≤
      weightedReturnedFamilyBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E C A.H A.a A.unit A.prepCost := by
  have hs' := weightedDenseSelection_cost P hWF solve hs A
  have hl := weightedDenseSelection_length P hWF solve hs A
  have hp := chargedMap_cost ops.makePrefix (weightedDenseSelection P hWF solve hs A).1 C
    (fun z hz => ho.prefix_cost z (weightedDenseSelection_points P hWF solve hs A z hz).1)
  have hp' := hp.trans (Nat.mul_le_mul_right (C+1) hl)
  have he := weightedDenseEdges_cost P hWF R solve hs A hR ops C ho
  dsimp only [weightedReturnedFamily]
  simp only [chargedMap_value,List.length_map]
  unfold weightedReturnedFamilyBudget weightedSelectionExecutionBudget
  nlinarith

end MOR34
