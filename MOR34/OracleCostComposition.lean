import MOR34.PolynomialPayload
import MOR34.QueryAccounting
import MOR34.NormalSearchCost

namespace MOR34

/-- Parameter factor for the already established support/extrema/cell call budget. -/
def rowCallFactor (q : ℕ) : ℕ := 1+6*2^q+2*(q+1)^2*6^q

variable {q : ℕ} {m : Fin q → ℕ}

theorem rowSearchCalls_polynomial (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q+1) :
    rowSearchCalls P hWF solve hs forms ≤ rowCallFactor q*(Fintype.card (Item m)+1) := by
  have hh := rowSearchCalls_le P hWF solve hs forms hsize
  have hq := coefficient_classes_le_items P hWF
  have hmul := Nat.mul_le_mul_right (2*2^q) hq
  have hn : 0 ≤ Fintype.card (Item m)*(2*(q+1)^2*6^q) := Nat.zero_le _
  unfold rowCallFactor
  nlinarith

/-- Substitution of the supplied fixed-dimension solver's per-call cost bound.
This charges only the phases in rowSearchCalls; other algorithm phases are separate. -/
theorem counted_ilp_cost_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q+1)
    (L I c perCall : ℕ)
    (hcost : perCall ≤ I*(168*(Fintype.card (Item m)+L+2)^4)^c) :
    rowSearchCalls P hWF solve hs forms * perCall ≤
      (rowCallFactor q*I*168^c)*(Fintype.card (Item m)+L+2)^(4*c+1) := by
  have hc := rowSearchCalls_polynomial P hWF solve hs forms hsize
  have hn : Fintype.card (Item m)+1 ≤ Fintype.card (Item m)+L+2 := by omega
  calc
    _ ≤ (rowCallFactor q*(Fintype.card (Item m)+L+2))*
        (I*(168*(Fintype.card (Item m)+L+2)^4)^c) :=
      Nat.mul_le_mul (hc.trans (Nat.mul_le_mul_left _ hn)) hcost
    _ = _ := by rw [mul_pow, ← pow_mul, pow_succ]; ring

noncomputable def allNormalCandidateCalls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : ℕ := by
  classical
  exact ∑ ε : Parity q, if hn : ∃ z, TightParity P ε z then
    ∑ mode : CellMode q, normalBasisCandidateCalls
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) (q+1) ∅
    else 0

/-- The complete family of small normal searches has parameter-only candidate count. -/
theorem allNormalCandidateCalls_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    allNormalCandidateCalls P hWF solve hs ≤
      6^q*((q+1)*((q+2)*(q+1)^(2*(q+1)))) := by
  classical
  unfold allNormalCandidateCalls
  calc
    _ ≤ ∑ _ε : Parity q, ∑ _mode : CellMode q,
        ((q+1)*((q+2)*(q+1)^(2*(q+1)))) := by
      apply Finset.sum_le_sum
      intro ε _
      split_ifs with hn
      · exact Finset.sum_le_sum (fun mode _ => computedCellSelection_normal_checks P hWF solve hs ε hn mode)
      · exact Nat.zero_le _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.nsmul_eq_mul, Parity, CellMode]
      rw [show (6:ℕ)=2*3 from rfl, mul_pow]
      ring

end MOR34
