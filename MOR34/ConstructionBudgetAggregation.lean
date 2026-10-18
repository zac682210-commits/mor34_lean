import MOR34.MaterializedViolationRows
import MOR34.AllResidualTables
import MOR34.EnumerationParameterBound

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem builtForcedRows_common_budget (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) (hR : R ≤ Fintype.card (Item m)+1) :
    (∑ k : ForcedRow m j u v, (builtForcedRow P j u v R k).2) ≤
      768*(Fintype.card (Item m)+1)^4 := by
  have hp : (Fintype.card (Item m)+1)^3 ≤ (Fintype.card (Item m)+1)^4 :=
    pow_le_pow_right' (by omega) (by decide)
  exact (builtForcedRows_total_cost P hWF j u v R hR).trans
    (Nat.mul_le_mul (by decide) hp)

/-- Uniform row-construction allowance across the already proved complete
solver-call budget. This is a budget lemma, not total-execution coverage. -/
theorem allRowConstruction_budget (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    (rowSearchCalls P hWF solve hs computedCountForms+Fintype.card (AdjacentPair m))*
      (768*(Fintype.card (Item m)+1)^4) ≤
      (768*(rowCallFactor q+1))*(Fintype.card (Item m)+1)^5 := by
  have hh := all_solver_calls_bound P hWF solve hs computedCountForms
    (fun B => (computedCountForms_length B).le)
  calc
    _ ≤ ((rowCallFactor q+1)*(Fintype.card (Item m)+1))*
        (768*(Fintype.card (Item m)+1)^4) := Nat.mul_le_mul_right _ hh
    _ = _ := by ring

def constructionPhaseFactor (q : ℕ) : ℕ :=
  18+768*(rowCallFactor q+1)+builtNormalParameter q

/-- The sum covers residual-table construction, the row-construction allowance,
and normal arithmetic/key generation. Missing phases are not hidden in this
expression; bit-cost units, solver/rank costs and other data movement are separate. -/
theorem constructionPhase_budget (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (R : ℕ) (hR : R ≤ Fintype.card (Item m)+1) :
    (chargedAllResidualTables P R).2 +
      (rowSearchCalls P hWF solve hs computedCountForms+Fintype.card (AdjacentPair m))*
        (768*(Fintype.card (Item m)+1)^4) +
      (allNormalArithmeticCharge P hWF solve hs+allNormalEnumerationCharge P hWF solve hs) ≤
      constructionPhaseFactor q*(Fintype.card (Item m)+1)^5 := by
  let t := Fintype.card (Item m)+1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htab := (chargedAllResidualTables_cost P hWF R hR).trans
    (Nat.mul_le_mul_left 18 (pow_le_pow_right' ht (by decide : 3 ≤ 5)))
  have hrows := allRowConstruction_budget P hWF solve hs
  have hn := (arithmetic_and_enumeration_parameter_bound P hWF solve hs).trans
    (Nat.le_mul_of_pos_right (builtNormalParameter q) (by positivity : 0 < t^5))
  calc
    _ ≤ 18*t^5+(768*(rowCallFactor q+1))*t^5+builtNormalParameter q*t^5 :=
      Nat.add_le_add (Nat.add_le_add htab hrows) hn
    _ = _ := by unfold constructionPhaseFactor; ring

end MOR34
