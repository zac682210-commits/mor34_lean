import MOR34.TracedNormalEnumeration
import MOR34.AggregateArithmeticCost

namespace MOR34

/-- All keys are constructed once at every visited basis state. The recursion
uses the actual oracle answer, including early termination. -/
def normalEnumerationCharge {q : ℕ} (solve : IntegerQuery q → Option (Counts q)) :
    ℕ → Finset (Counts q) → ℕ
  | 0,_ => 0
  | r+1,B => (chargedNormalKeys (orderedCounts B).length (q+1)).2 +
      match linearSpanOracle solve computedCountForms B with
      | none => 0
      | some z => normalEnumerationCharge solve r (insert z B)

theorem normalEnumerationCharge_bound {q : ℕ}
    (solve : IntegerQuery q → Option (Counts q)) (fuel : ℕ) (B : Finset (Counts q))
    (hB : B.card+fuel ≤ q+1) :
    normalEnumerationCharge solve fuel B ≤ fuel*normalKeyBuildBudget (q+1) := by
  induction fuel generalizing B with
  | zero => simp [normalEnumerationCharge]
  | succ r ih =>
      have hs : (orderedCounts B).length ≤ q+1 := by rw [orderedCounts_length]; omega
      have hk := chargedNormalKeys_cost (orderedCounts B).length (q+1) hs
      cases he : linearSpanOracle solve computedCountForms B with
      | none => simp only [normalEnumerationCharge, he, add_zero]; nlinarith
      | some z =>
          have hnext : (insert z B).card+r ≤ q+1 := by
            have hh := Finset.card_insert_le z B
            omega
          have hi := ih (insert z B) hnext
          simp only [normalEnumerationCharge, he]
          nlinarith

variable {q : ℕ} {m : Fin q → ℕ}

noncomputable def allNormalEnumerationCharge (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : ℕ := by
  classical
  exact ∑ ε : Parity q, if hn : ∃ z, TightParity P ε z then
    ∑ mode : CellMode q, normalEnumerationCharge
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) (q+1) ∅
    else 0

theorem allNormalEnumerationCharge_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    allNormalEnumerationCharge P hWF solve hs ≤ 6^q*(q+1)*normalKeyBuildBudget (q+1) := by
  classical
  unfold allNormalEnumerationCharge
  calc
    _ ≤ ∑ _ε : Parity q, ∑ _mode : CellMode q, ((q+1)*normalKeyBuildBudget (q+1)) := by
      apply Finset.sum_le_sum
      intro ε _
      split_ifs with hn
      · exact Finset.sum_le_sum (fun mode _ => normalEnumerationCharge_bound _ _ _ (by simp))
      · exact Nat.zero_le _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.nsmul_eq_mul, Parity, CellMode]
      rw [show (6:ℕ)=2*3 from rfl, mul_pow]
      ring

def builtNormalParameter (q : ℕ) : ℕ :=
  (q+4)^(6*q+13)+6^q*(q+1)*normalKeyBuildBudget (q+1)

theorem arithmetic_and_enumeration_parameter_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    allNormalArithmeticCharge P hWF solve hs + allNormalEnumerationCharge P hWF solve hs ≤
      builtNormalParameter q :=
  Nat.add_le_add (allNormalArithmeticCharge_parameter P hWF solve hs)
    (allNormalEnumerationCharge_bound P hWF solve hs)

end MOR34
