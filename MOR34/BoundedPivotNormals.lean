import MOR34.CramerBounds
import Mathlib.Data.Nat.Log

namespace MOR34

/-- Integer normal for one free coordinate of a nonsingular pivot block. -/
def pivotNormal {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (k : Fin f) : Fin r ⊕ Fin f → ℤ
  | Sum.inl j => -A.cramer (fun i => C i k) j
  | Sum.inr j => if j = k then A.det else 0

/-- Every pivot row annihilates every constructed integer normal. -/
theorem pivotNormal_kernel {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (k : Fin f) :
    ∀ i, (∑ j : Fin r ⊕ Fin f, Sum.elim (A i) (C i) j * pivotNormal A C k j) = 0 := by
  intro i
  rw [Fintype.sum_sum_type]
  simp only [pivotNormal, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact cramerNormal_kernel A (fun i => C i k) i

theorem pivotNormal_bound {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (N : ℤ) (hN : 0 ≤ N)
    (hA : ∀ i j, |A i j| ≤ N) (hC : ∀ i j, |C i j| ≤ N) :
    ∀ k j, |pivotNormal A C k j| ≤ (r.factorial : ℤ) * N ^ r := by
  intro k j
  cases j with
  | inl j => simpa [pivotNormal] using integer_cramer_bound A (fun i => C i k) N hA (fun i => hC i k) j
  | inr j =>
    by_cases hj : j = k
    · simp only [pivotNormal, hj, if_true]
      exact integer_det_bound A N hA
    · simp only [pivotNormal, hj, if_false, abs_zero]
      positivity

/-- Free-coordinate diagonal entries prove independence over the rationals. -/
theorem pivotNormal_independent {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (hd : A.det ≠ 0) :
    LinearIndependent ℚ (fun k => fun j => (pivotNormal A C k j : ℚ)) := by
  rw [linearIndependent_iff']
  intro s w hw k hk
  have hh := congrFun hw (Sum.inr k)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, pivotNormal,
    Int.cast_ite, Int.cast_zero, mul_ite, mul_zero] at hh
  have he : (∑ j ∈ s, if k = j then w j * (A.det : ℚ) else 0) = w k * (A.det : ℚ) := by
    simp [Finset.sum_ite_eq, hk]
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast hd)

/-- Magnitude exponent bound: r! N^r needs at most r(D+L)+1 magnitude bits
when r<=2^D and N<=2^L. Signs need one additional bit. -/
theorem factorial_power_bound (r N D L : ℕ) (hr : r ≤ 2 ^ D) (hN : N ≤ 2 ^ L) :
    r.factorial * N ^ r ≤ 2 ^ ((D + L) * r) := by
  calc
    r.factorial * N ^ r ≤ r ^ r * N ^ r := Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
    _ ≤ (2 ^ D) ^ r * (2 ^ L) ^ r :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hr r) (Nat.pow_le_pow_left hN r)
    _ = 2 ^ ((D + L) * r) := by rw [← mul_pow, ← pow_add, ← pow_mul]
end MOR34
