import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic

namespace MOR34

/-- A determinant bound suitable for integer normals; this is not yet a bit-cost theorem. -/
theorem integer_det_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (N : ℤ)
    (hA : ∀ i j, |A i j| ≤ N) : |A.det| ≤ (r.factorial : ℤ) * N ^ r := by
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) hA
  simpa [nsmul_eq_mul] using hh

theorem integer_cramer_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (b : Fin r → ℤ) (N : ℤ) (hA : ∀ i j, |A i j| ≤ N) (hb : ∀ i, |b i| ≤ N) :
    ∀ j, |A.cramer b j| ≤ (r.factorial : ℤ) * N ^ r := by
  intro j
  rw [Matrix.cramer_apply]
  apply integer_det_bound
  intro i k
  by_cases hk : k = j
  · subst k; simpa using hb i
  · simpa [Matrix.updateCol, hk] using hA i k

/-- A bounded integer kernel vector for one additional column. -/
def cramerNormal {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    Option (Fin r) → ℤ
  | none => A.det
  | some j => -A.cramer b j

theorem cramerNormal_kernel {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    ∀ i, (∑ j, A i j * cramerNormal A b (some j)) + b i * cramerNormal A b none = 0 := by
  intro i
  have hh := congrFun (Matrix.mulVec_cramer A b) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hh
  simp only [cramerNormal, mul_neg, Finset.sum_neg_distrib]
  nlinarith

theorem cramerNormal_nonzero {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (hd : A.det ≠ 0) : cramerNormal A b ≠ 0 := by
  intro he
  exact hd (congrFun he none)

theorem cramerNormal_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (b : Fin r → ℤ) (N : ℤ) (hA : ∀ i j, |A i j| ≤ N) (hb : ∀ i, |b i| ≤ N) :
    ∀ j, |cramerNormal A b j| ≤ (r.factorial : ℤ) * N ^ r := by
  intro j
  cases j with
  | none => exact integer_det_bound A N hA
  | some j => simpa [cramerNormal] using integer_cramer_bound A b N hA hb j
end MOR34
