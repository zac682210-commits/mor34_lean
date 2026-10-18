import MOR34.PivotCost
import MOR34.NormalSearchCost
import MOR34.ParameterFactors

namespace MOR34

/-- Arithmetic and comparison charge for one explicitly evaluated Cramer entry.
Submatrix access and bit operations are separate charges. -/
def columnNormalCharge {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (c : Fin r ↪ Fin d) (j k : Fin d) : ℕ :=
  (if k = j then (tracedLaplaceDet r (M.submatrix id c)).2 else 0) +
    (∑ i : Fin r, if c i = k then
      (tracedLaplaceDet r ((M.submatrix id c).updateCol i (fun a => M a j))).2 else 0) +
    2*r+2

/-- A dimension-only bound on every minor's recursive arithmetic. -/
theorem minor_arithmetic_bound (r d : ℕ) (hr : r ≤ d)
    (M : Matrix (Fin r) (Fin r) ℤ) :
    (tracedLaplaceDet r M).2 ≤ (d+3)^2*d.factorial := by
  exact ((tracedLaplaceDet_cost r M).trans (laplaceArithmeticBudget_bound r)).trans
    (Nat.mul_le_mul (pow_le_pow_left' (by omega) 2) (Nat.factorial_le hr))

theorem columnNormalCharge_bound {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (c : Fin r ↪ Fin d) (hr : r ≤ d) (j k : Fin d) :
    columnNormalCharge M c j k ≤ (d+1)*((d+3)^2*d.factorial+2) := by
  have h₁ : (if k = j then (tracedLaplaceDet r (M.submatrix id c)).2 else 0) ≤
      (d+3)^2*d.factorial := by
    split_ifs
    · exact minor_arithmetic_bound r d hr _
    · exact Nat.zero_le _
  have h₂ : (∑ i : Fin r, if c i = k then
      (tracedLaplaceDet r ((M.submatrix id c).updateCol i (fun a => M a j))).2 else 0) ≤
      r*((d+3)^2*d.factorial) := by
    calc
      _ ≤ ∑ _i : Fin r, ((d+3)^2*d.factorial) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact minor_arithmetic_bound r d hr _
        · exact Nat.zero_le _
      _ = _ := by simp
  unfold columnNormalCharge
  have hmul := Nat.mul_le_mul_right ((d+3)^2*d.factorial+2) hr
  nlinarith

/-- This follows the branches of tryNormalKey, including rejected candidates.
A stored table of all normal entries is charged once. -/
def normalKeyCharge {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (k : NormalSearchKey s d) : ℕ :=
  k.rank.val^2+1 + if hi : Function.Injective k.cols then
    let c : Fin k.rank.val ↪ Fin d := ⟨k.cols, hi⟩
    let R := M.submatrix k.rows id
    (tracedLaplaceDet k.rank.val (R.submatrix id c)).2+1 +
      if laplaceDet k.rank.val (R.submatrix id c) ≠ 0 then
        (∑ j : Fin d, ∑ l : Fin d, columnNormalCharge R c j l) +
        ∑ _i : Fin s, ∑ _j : Fin d, (2*d+1)
      else 0
  else 0

def normalKeyBudget (d : ℕ) : ℕ :=
  d^2+1 + ((d+3)^2*d.factorial+1) +
    d*d*((d+1)*((d+3)^2*d.factorial+2)) + d*d*(2*d+1)

theorem normalKeyCharge_bound {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (hs : s ≤ d) (k : NormalSearchKey s d) : normalKeyCharge M k ≤ normalKeyBudget d := by
  have hr : k.rank.val ≤ d := by omega
  have hp := pow_le_pow_left' hr 2
  by_cases hi : Function.Injective k.cols
  · simp only [normalKeyCharge, dif_pos hi]
    have hd' := minor_arithmetic_bound k.rank.val d hr
      ((M.submatrix k.rows id).submatrix id k.cols)
    have hc : (∑ j : Fin d, ∑ l : Fin d,
        columnNormalCharge (M.submatrix k.rows id) ⟨k.cols, hi⟩ j l) ≤
        d*d*((d+1)*((d+3)^2*d.factorial+2)) := by
      calc
        _ ≤ ∑ _j : Fin d, ∑ _l : Fin d,
            (d+1)*((d+3)^2*d.factorial+2) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
            (fun l _ => columnNormalCharge_bound _ _ hr j l))
        _ = _ := by simp; ring
    have hcheck : (∑ _i : Fin s, ∑ _j : Fin d, (2*d+1)) ≤ d*d*(2*d+1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      exact (Nat.mul_le_mul_right _ hs).trans_eq (by ring)
    split_ifs <;> unfold normalKeyBudget <;> omega
  · simp only [normalKeyCharge, dif_neg hi, add_zero]
    unfold normalKeyBudget
    omega

/-- The actual early-stopping candidate search is charged, not a fictitious
number of successful candidates. -/
def matrixNormalArithmeticCharge {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) : ℕ :=
  firstWitnessCharge (tryNormalKey M) (normalKeyCharge M) (normalSearchKeys s d)

theorem matrixNormalArithmeticCharge_bound {s d : ℕ}
    (M : Matrix (Fin s) (Fin d) ℤ) (hd : 1 ≤ d) (hs : s ≤ d) :
    matrixNormalArithmeticCharge M ≤ ((d+1)*d^(2*d))*normalKeyBudget d := by
  exact (firstWitnessCharge_bound _ _ _ (normalKeyCharge_bound M hs) _).trans
    (Nat.mul_le_mul_right _ (matrixNormalSearch_calls M hd hs))

/-- A uniform operation charge along the actual count-basis recursion. -/
def normalBasisArithmeticCharge {q : ℕ} (solve : IntegerQuery q → Option (Counts q)) :
    ℕ → Finset (Counts q) → ℕ
  | 0, _ => 0
  | r+1, B => matrixNormalArithmeticCharge (orderedCountMatrix B) +
      match linearSpanOracle solve computedCountForms B with
      | none => 0
      | some z => normalBasisArithmeticCharge solve r (insert z B)

theorem normalBasisArithmeticCharge_bound {q : ℕ}
    (solve : IntegerQuery q → Option (Counts q)) (fuel : ℕ) (B : Finset (Counts q))
    (hB : B.card+fuel ≤ q+1) :
    normalBasisArithmeticCharge solve fuel B ≤
      fuel*(((q+2)*(q+1)^(2*(q+1)))*normalKeyBudget (q+1)) := by
  induction fuel generalizing B with
  | zero => simp [normalBasisArithmeticCharge]
  | succ r ih =>
    have hs : (orderedCounts B).length ≤ q+1 := by rw [orderedCounts_length]; omega
    have hc := matrixNormalArithmeticCharge_bound (orderedCountMatrix B) (by omega) hs
    cases he : linearSpanOracle solve computedCountForms B with
    | none =>
      simp only [normalBasisArithmeticCharge, he, add_zero]
      nlinarith
    | some z =>
      have hh : (insert z B).card+r ≤ q+1 := by
        have hi := Finset.card_insert_le z B
        omega
      have hh' := ih (insert z B) hh
      simp only [normalBasisArithmeticCharge, he]
      nlinarith

end MOR34
