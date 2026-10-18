import MOR34.ForcedRowEnumeration
import MOR34.ConstructedWitnessPipeline

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- External fixed-dimension integer feasibility, on concrete integer arrays.
This is a local solver contract, not a total runtime premise. -/
structure DenseRowSolverSpec
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) : Prop where
  found : ∀ rows, (∀ row ∈ rows, row.WellSized) → ∀ s,
    (solve rows).1 = some s → ∀ row ∈ rows, row.value.Holds s.1 s.2
  done : ∀ rows, (∀ row ∈ rows, row.WellSized) →
    (solve rows).1 = none → ∀ z y, ¬ ∀ row ∈ rows, row.value.Holds z y

/-- Each requested exchange constructs its residual table once, then passes it
to all its rows. The input read budget R remains an explicit primitive contract. -/
def compiledForcedRequest (P : Model m) (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    List (DenseIntegerRow q) × ℕ :=
  let table := chargedResidualWeights P j u v R
  let out := retainedForcedSystem P j u v table.1 (P.weight ⟨j,v⟩,R) R
  (out.1,table.2+out.2+1)

theorem compiledForcedRequest_sized (P : Model m) (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    ∀ row ∈ (compiledForcedRequest P j u v R).1, row.WellSized :=
  retainedForcedSystem_sized P j u v _ _ R

theorem compiledForcedRequest_iff (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (z y : Fin q → ℤ) :
    (∀ row ∈ (compiledForcedRequest P j u v R).1, row.value.Holds z y) ↔
      ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y :=
  retainedForcedSystem_iff P j u v _ _ R rfl rfl z y

theorem compiledForcedRequest_cost (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) (hR : R ≤ Fintype.card (Item m)+1) :
    (compiledForcedRequest P j u v R).2 ≤ 521*(Fintype.card (Item m)+1)^3 := by
  let n := Fintype.card (Item m)
  have ht := residual_table_polynomial_work P j u v n R (class_size_le_items j) hR
  have hc := retainedForcedSystem_cost P hWF j u v
    (chargedResidualWeights P j u v R).1 (P.weight ⟨j,v⟩,R) R rfl rfl hR hR
  have hp : (n+1)^2 ≤ (n+1)^3 := pow_le_pow_right' (by omega) (by decide)
  have hone : 1 ≤ (n+1)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [compiledForcedRequest]
  change _ ≤ 521*(n+1)^3
  nlinarith

def chargedDenseForcedSolve (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (j : Fin q) (u v : Fin (m j)) : Option (IntegerRowSolution q) × ℕ :=
  let request := compiledForcedRequest P j u v R
  let result := solve request.1
  (result.1,request.2+result.2+1)

def denseForcedOracle (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (j : Fin q) (u v : Fin (m j)) : Option (IntegerRowSolution q) :=
  (chargedDenseForcedSolve P R solve j u v).1

theorem denseForcedOracle_spec (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) : ForcedRowSolverSpec P (denseForcedOracle P R solve) := by
  constructor
  · intro j u v s h
    exact (compiledForcedRequest_iff P j u v R s.1 s.2).mp
      (hs.found _ (compiledForcedRequest_sized P j u v R) s h)
  · intro j u v h z y hh
    exact hs.done _ (compiledForcedRequest_sized P j u v R) h z y
      ((compiledForcedRequest_iff P j u v R z y).mpr hh)

theorem chargedDenseForcedSolve_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (j : Fin q) (u v : Fin (m j)) (U : ℕ) (hR : R ≤ Fintype.card (Item m)+1)
    (hU : (solve (compiledForcedRequest P j u v R).1).2 ≤ U) :
    (chargedDenseForcedSolve P R solve j u v).2 ≤
      521*(Fintype.card (Item m)+1)^3+U+1 := by
  have hh := compiledForcedRequest_cost P hWF j u v R hR
  dsimp only [chargedDenseForcedSolve]
  omega

/-- The dense-array adapter is now a caller of the full output procedure,
including its exchange witnesses, affine basis, dimension and facet decision. -/
theorem denseForced_normalized_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (R : ℕ)
    (dense : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hd : DenseRowSolverSpec dense)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (constructedNormalizedPipeline P hWF solve hs (denseForcedOracle P R dense) violate ranker).Correct P :=
  constructedNormalizedPipeline_correct P hWF solve hs (denseForcedOracle P R dense)
    (denseForcedOracle_spec P R dense hd) violate hv ranker

end MOR34
