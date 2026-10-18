import MOR34.WeightedSharedParity
import MOR34.DenseViolationSolver

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedCompileRetainedRow (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) : DenseIntegerRow q × ℕ :=
  let out := weightedEvaluateRow A row.1
  (out.1,row.2+out.2)

theorem weightedCompileRetainedRow_value (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) :
    (weightedCompileRetainedRow A row).1 = (compileRetainedRow row).1 := by
  exact weightedEvaluateRow_value A row.1

def sharedWeightedCompileParityRow (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) : DenseIntegerRow q × ℕ :=
  let original := weightedCompileRetainedRow A row
  let out := sharedWeightedDenseParityRow A original.1 ε
  (out.1,original.2+out.2+1)

theorem sharedWeightedCompileParityRow_value (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) :
    (sharedWeightedCompileParityRow A row ε).1 = (compileParityRow row ε).1 := by
  simp only [sharedWeightedCompileParityRow,sharedWeightedDenseParityRow_value,
    weightedCompileRetainedRow_value,compileParityRow]

def weightedCompiledCountRequest (A : IntegerArithmeticCharge) (P : Model m)
    (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ) : List (DenseIntegerRow q) × ℕ :=
  let indices := countRowIndexList m L.length
  let out := chargedMap (fun k => sharedWeightedCompileParityRow A
    (builtCountRow P (fun i j => (L.get i).coefficient j) (fun i => (L.get i).bound) R k) ε) indices
  (out.1,out.2+8*indices.length+q+1)

theorem weightedCompiledCountRequest_value (A : IntegerArithmeticCharge) (P : Model m)
    (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ) :
    (weightedCompiledCountRequest A P ε L R).1 = (compiledCountRequest P ε L R).1 := by
  simp only [weightedCompiledCountRequest,compiledCountRequest,chargedMap_value,
    sharedWeightedCompileParityRow_value]

def weightedCompiledViolationRequest (A : IntegerArithmeticCharge) (P : Model m) (R : ℕ) :
    List (DenseIntegerRow q) × ℕ :=
  let indices := violationRowIndexList m
  let out := chargedMap (fun k => weightedCompileRetainedRow A (builtViolationRow P R k)) indices
  (out.1,out.2+8*indices.length+q+1)

theorem weightedCompiledViolationRequest_value (A : IntegerArithmeticCharge) (P : Model m) (R : ℕ) :
    (weightedCompiledViolationRequest A P R).1 = (compiledViolationRequest P R).1 := by
  simp only [weightedCompiledViolationRequest,compiledViolationRequest,chargedMap_value,
    weightedCompileRetainedRow_value]

def weightedCompiledForcedRequest (A : IntegerArithmeticCharge) (P : Model m)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) : List (DenseIntegerRow q) × ℕ :=
  let table := chargedResidualWeights P j u v R
  let indices := forcedRowIndexList j u v
  let out := chargedMap (fun k => weightedCompileRetainedRow A
    (retainedForcedRow P j u v table.1 (P.weight ⟨j,v⟩,R) R k)) indices
  (out.1,table.2+out.2+8*indices.length+q+2)

theorem weightedCompiledForcedRequest_value (A : IntegerArithmeticCharge) (P : Model m)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    (weightedCompiledForcedRequest A P j u v R).1 = (compiledForcedRequest P j u v R).1 := by
  simp only [weightedCompiledForcedRequest,compiledForcedRequest,retainedForcedSystem,
    chargedMap_value,weightedCompileRetainedRow_value]

/-- Exact dense-array equality preserves both the selected solver witness and
its input-dependent external bit-cost contract. -/
theorem weightedRequests_solver_inputs (A : IntegerArithmeticCharge) (P : Model m)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ) (j : Fin q) (u v : Fin (m j)) :
    solve (weightedCompiledCountRequest A P ε L R).1 = solve (compiledCountRequest P ε L R).1 ∧
    solve (weightedCompiledViolationRequest A P R).1 = solve (compiledViolationRequest P R).1 ∧
    solve (weightedCompiledForcedRequest A P j u v R).1 = solve (compiledForcedRequest P j u v R).1 := by
  simp only [weightedCompiledCountRequest_value,weightedCompiledViolationRequest_value,
    weightedCompiledForcedRequest_value,and_self]

end MOR34
