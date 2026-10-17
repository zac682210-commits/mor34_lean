import MOR34.ForcedLinearEncoding

namespace MOR34

/-- The bit-size analysis can use original weight bounds without assuming sortedness. -/
theorem prefixCost_abs_bound {s : ℕ} (w : Fin s → ℤ) (M : ℤ)
    (hw : ∀ i, |w i| ≤ M) (z : ℕ) (hz : z ≤ s) :
    |prefixCost w z| ≤ (z : ℤ) * M := by
  calc
    _ ≤ ∑ i ∈ classPrefix s z, |w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ classPrefix s z, M := Finset.sum_le_sum (fun i _ => hw i)
    _ = (z : ℤ) * M := by simp [card_classPrefix hz]

theorem prefixIntercept_abs_bound {s : ℕ} (w : Fin s → ℤ) (M : ℤ)
    (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M) (t : Fin s) :
    |w t * (t.val : ℤ) - prefixCost w t.val| ≤ 2 * (s : ℤ) * M := by
  have hp := prefixCost_abs_bound w M hw t.val (Nat.le_of_lt t.isLt)
  have ht : (t.val : ℤ) ≤ s := by exact_mod_cast Nat.le_of_lt t.isLt
  have hm : |w t * (t.val : ℤ)| ≤ M * (t.val : ℤ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t.val)]
    exact mul_le_mul_of_nonneg_right (hw t) (by positivity)
  have hh := abs_sub_le (w t * (t.val : ℤ)) 0 (prefixCost w t.val)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  nlinarith

/-- Forced-prefix rows have the same polynomial-size intercept control. -/
theorem shiftedPrefixIntercept_abs_bound {s : ℕ} (w : Fin s → ℤ) (v M : ℤ)
    (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M) (hv : |v| ≤ M) (t : Fin s) :
    |((t.val : ℤ) + 1) * w t - prefixCost w t.val - v| ≤ (2 * (s : ℤ) + 2) * M := by
  have hp := prefixCost_abs_bound w M hw t.val (Nat.le_of_lt t.isLt)
  have ht : (t.val : ℤ) ≤ s := by exact_mod_cast Nat.le_of_lt t.isLt
  have hm : |((t.val : ℤ) + 1) * w t| ≤ ((t.val : ℤ) + 1) * M := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (t.val : ℤ) + 1)]
    exact mul_le_mul_of_nonneg_left (hw t) (by positivity)
  have hh := abs_sub_le (((t.val : ℤ) + 1) * w t) 0 (prefixCost w t.val)
  have hh' := abs_sub_le (((t.val : ℤ) + 1) * w t - prefixCost w t.val) 0 v
  simp only [sub_zero, zero_sub, abs_neg] at hh hh'
  nlinarith

end MOR34
