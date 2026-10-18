import MOR34.WeightedRecognition

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedAdjacentWitness (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) (e : AdjacentPair m) : Option (Finset (Item m)) × ℕ :=
  let out := weightedDenseForcedSolve arith P R solve e.val.1 e.val.2.1 e.val.2.2
  match out.1 with
  | none => (none,out.2+1)
  | some s => let S := ops.forced e.val.1 e.val.2.1 e.val.2.2 s.1
              (some S.1,out.2+S.2+1)

theorem weightedAdjacentWitness_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) (e : AdjacentPair m) :
    (weightedAdjacentWitness arith P R solve ops e).1 =
      exchangeWitness (denseForcedOracle P R solve) e.val.1 e.val.2.1 e.val.2.2 := by
  rw [adjacent_exchange_uses_one_solve]
  simp only [weightedAdjacentWitness,weightedDenseForcedSolve_value]
  cases denseForcedOracle P R solve e.val.1 e.val.2.1 e.val.2.2 <;>
    simp [ops.forced_value]

def weightedWitnessTable (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : List (AdjacentPair m × Option (Finset (Item m))) × ℕ :=
  let indices := chargedAdjacentIndices m
  let out := chargedMap (fun e => let w := weightedAdjacentWitness arith P R solve ops e
                                 ((e,w.1),w.2)) indices.1
  (out.1,indices.2+out.2+1)

theorem weightedWitnessTable_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (weightedWitnessTable arith P R solve ops).1 = constructedWitnessTable (denseForcedOracle P R solve) := by
  simp only [weightedWitnessTable,chargedMap_value,weightedAdjacentWitness_value,constructedWitnessTable]

def weightedDenseEdges (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : List (Finset (Item m)) × ℕ :=
  let T := weightedWitnessTable arith P R solve ops
  let E := chargedEdgePoints ops T.1
  (E.1,T.2+E.2+1)

theorem weightedDenseEdges_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (weightedDenseEdges arith P R solve ops).1 =
      edgePointsFromTable (constructedWitnessTable (denseForcedOracle P R solve)) := by
  simp only [weightedDenseEdges,chargedEdgePoints_value,weightedWitnessTable_value]

def weightedEdgeExecutionBudget (q n L I c C H a : ℕ) : ℕ :=
  8*(n+1)^2+n*(weightedForcedRequestBudget q n L H a+I*(180*(n+L+2)^4)^c+C+3)+n*(C+4)+2

theorem weightedDenseEdges_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (hR : R ≤ Fintype.card (Item m)+1)
    (ops : PointOperations m) (C : ℕ) (hops : PointOperationBounds ops C) :
    (weightedDenseEdges A.arith P R solve ops).2 ≤ weightedEdgeExecutionBudget q (Fintype.card (Item m)) A.base.L A.base.I A.base.c C A.H A.a := by
  let n := Fintype.card (Item m)
  have he (e : AdjacentPair m) : (weightedAdjacentWitness A.arith P R solve ops e).2 ≤
      weightedForcedRequestBudget q n A.base.L A.H A.a+A.base.I*(180*(n+A.base.L+2)^4)^A.base.c+C+2 := by
    have hv := (weightedDenseBranchSolve_cost P hWF R solve A hR).2 e.val.1 e.val.2.1 e.val.2.2
    dsimp only [weightedAdjacentWitness]
    split
    · dsimp only [n] at *
      omega
    · rename_i s h
      have hb := ((forcedRows_iff P e.val.1 e.val.2.1 e.val.2.2 s.1 s.2).mp
        ((denseForcedOracle_spec P R solve hs).found _ _ _ s (by simpa only [weightedDenseForcedSolve_value] using h))).1
      have ho := hops.forced e.val.1 e.val.2.1 e.val.2.2 s.1 hb
      dsimp only [n] at *
      omega
  have hm := chargedMap_cost (fun e => let w := weightedAdjacentWitness A.arith P R solve ops e
                                     ((e,w.1),w.2)) (chargedAdjacentIndices m).1
    (weightedForcedRequestBudget q n A.base.L A.H A.a+A.base.I*(180*(n+A.base.L+2)^4)^A.base.c+C+2) (fun e _ => he e)
  have hl : (chargedAdjacentIndices m).1.length ≤ n := chargedAdjacentIndices_length
  have hm' := hm.trans (Nat.mul_le_mul_right _ hl)
  have hind := chargedAdjacentIndices_cost n (coefficient_classes_le_items P hWF)
    (fun j => class_size_le_items j)
  change (chargedAdjacentIndices m).2 ≤ 8*(n+1)^2 at hind
  have hedge := chargedEdgePoints_cost ops C hops (weightedWitnessTable A.arith P R solve ops).1
  have ht : (weightedWitnessTable A.arith P R solve ops).1.length ≤ n := by
    rw [weightedWitnessTable_value]
    exact constructedWitnessTable_length _
  have hedge' := hedge.trans (Nat.mul_le_mul_right (C+4) ht)
  dsimp only [weightedDenseEdges,weightedWitnessTable] at ⊢
  unfold weightedEdgeExecutionBudget
  change _ ≤ 8*(n+1)^2+n*(weightedForcedRequestBudget q n A.base.L A.H A.a+A.base.I*(180*(n+A.base.L+2)^4)^A.base.c+C+3)+n*(C+4)+2
  dsimp only [weightedWitnessTable,n] at hedge'
  dsimp only [n] at *
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

end MOR34
