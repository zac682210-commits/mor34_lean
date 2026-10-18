import MOR34.ChargedRecognitionExecution

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def chargedAdjacentWitness (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) (e : AdjacentPair m) : Option (Finset (Item m)) × ℕ :=
  let out := chargedDenseForcedSolve P R solve e.val.1 e.val.2.1 e.val.2.2
  match out.1 with
  | none => (none,out.2+1)
  | some s => let S := ops.forced e.val.1 e.val.2.1 e.val.2.2 s.1
              (some S.1,out.2+S.2+1)

theorem chargedAdjacentWitness_value (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) (e : AdjacentPair m) :
    (chargedAdjacentWitness P R solve ops e).1 =
      exchangeWitness (denseForcedOracle P R solve) e.val.1 e.val.2.1 e.val.2.2 := by
  rw [adjacent_exchange_uses_one_solve]
  simp only [chargedAdjacentWitness,denseForcedOracle]
  cases (chargedDenseForcedSolve P R solve e.val.1 e.val.2.1 e.val.2.2).1 <;>
    simp [ops.forced_value]

def chargedWitnessTable (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : List (AdjacentPair m × Option (Finset (Item m))) × ℕ :=
  let indices := chargedAdjacentIndices m
  let out := chargedMap (fun e => let w := chargedAdjacentWitness P R solve ops e
                                 ((e,w.1),w.2)) indices.1
  (out.1,indices.2+out.2+1)

theorem chargedWitnessTable_value (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (chargedWitnessTable P R solve ops).1 = constructedWitnessTable (denseForcedOracle P R solve) := by
  simp only [chargedWitnessTable,chargedMap_value,chargedAdjacentWitness_value,constructedWitnessTable]

def chargedEdgePoints (ops : PointOperations m)
    (T : List (AdjacentPair m × Option (Finset (Item m)))) : List (Finset (Item m)) × ℕ :=
  chargedFlatMap (fun p => match p.2 with
    | none => ([],1)
    | some S => let out := ops.swap p.1 S
                ([S,out.1],out.2+1)) T

theorem chargedEdgePoints_value (ops : PointOperations m)
    (T : List (AdjacentPair m × Option (Finset (Item m)))) :
    (chargedEdgePoints ops T).1 = edgePointsFromTable T := by
  simp only [chargedEdgePoints,chargedFlatMap_value,edgePointsFromTable]
  congr 1
  funext p
  cases p.2 <;> simp [ops.swap_value]

theorem chargedEdgePoints_cost (ops : PointOperations m) (C : ℕ)
    (hops : PointOperationBounds ops C)
    (T : List (AdjacentPair m × Option (Finset (Item m)))) :
    (chargedEdgePoints ops T).2 ≤ T.length*(C+4) := by
  apply (chargedFlatMap_cost _ T (C+1) 2 ?_ ?_).trans_eq (by ring)
  · intro p _
    cases h : p.2 with
    | none => simp [h]
    | some S => simpa only [h] using Nat.add_le_add_right (hops.swap p.1 S) 1
  · intro p _
    cases p.2 <;> simp

def chargedDenseEdges (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) : List (Finset (Item m)) × ℕ :=
  let T := chargedWitnessTable P R solve ops
  let E := chargedEdgePoints ops T.1
  (E.1,T.2+E.2+1)

theorem chargedDenseEdges_value (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ops : PointOperations m) :
    (chargedDenseEdges P R solve ops).1 =
      edgePointsFromTable (constructedWitnessTable (denseForcedOracle P R solve)) := by
  simp only [chargedDenseEdges,chargedEdgePoints_value,chargedWitnessTable_value]

def edgeExecutionBudget (n L I c C : ℕ) : ℕ :=
  8*(n+1)^2+n*(521*(n+1)^3+I*(180*(n+L+2)^4)^c+C+3)+n*(C+4)+2

theorem chargedDenseEdges_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (hR : R ≤ Fintype.card (Item m)+1)
    (ops : PointOperations m) (C : ℕ) (hops : PointOperationBounds ops C) :
    (chargedDenseEdges P R solve ops).2 ≤ edgeExecutionBudget (Fintype.card (Item m)) A.L A.I A.c C := by
  let n := Fintype.card (Item m)
  have he (e : AdjacentPair m) : (chargedAdjacentWitness P R solve ops e).2 ≤
      521*(n+1)^3+A.I*(180*(n+A.L+2)^4)^A.c+C+2 := by
    have hi := actualForcedSolver_cost P hWF A.M A.L A.magnitude_pos A.magnitude_bits
      A.weights A.coefficients A.capacity A.rhs e.val.1 e.val.2.1 e.val.2.2 R A.I A.c solve A.solver_cost
    have hv := chargedDenseForcedSolve_cost P hWF R solve e.val.1 e.val.2.1 e.val.2.2 _ hR hi
    dsimp only [chargedAdjacentWitness]
    split
    · omega
    · rename_i s h
      have hb := ((forcedRows_iff P e.val.1 e.val.2.1 e.val.2.2 s.1 s.2).mp
        ((denseForcedOracle_spec P R solve hs).found _ _ _ s h)).1
      have ho := hops.forced e.val.1 e.val.2.1 e.val.2.2 s.1 hb
      omega
  have hm := chargedMap_cost (fun e => let w := chargedAdjacentWitness P R solve ops e
                                     ((e,w.1),w.2)) (chargedAdjacentIndices m).1
    (521*(n+1)^3+A.I*(180*(n+A.L+2)^4)^A.c+C+2) (fun e _ => he e)
  have hl : (chargedAdjacentIndices m).1.length ≤ n := chargedAdjacentIndices_length
  have hm' := hm.trans (Nat.mul_le_mul_right _ hl)
  have hind := chargedAdjacentIndices_cost n (coefficient_classes_le_items P hWF)
    (fun j => class_size_le_items j)
  have hedge := chargedEdgePoints_cost ops C hops (chargedWitnessTable P R solve ops).1
  have ht : (chargedWitnessTable P R solve ops).1.length ≤ n := by
    rw [chargedWitnessTable_value]
    exact constructedWitnessTable_length _
  have hedge' := hedge.trans (Nat.mul_le_mul_right (C+4) ht)
  dsimp only [chargedDenseEdges,chargedWitnessTable] at ⊢
  unfold edgeExecutionBudget
  change _ ≤ 8*(n+1)^2+n*(521*(n+1)^3+A.I*(180*(n+A.L+2)^4)^A.c+C+3)+n*(C+4)+2
  dsimp only [chargedWitnessTable] at hedge'
  omega

end MOR34
