import MOR34.FiniteDeterminant
import MOR34.PivotNormalBits

namespace MOR34

def laplaceTerm {r : ℕ} (A : Matrix (Fin (r+1)) (Fin (r+1)) ℤ) (j : Fin (r+1)) : ℤ :=
  (-1)^j.val * A 0 j * laplaceDet r (A.submatrix Fin.succ j.succAbove)

theorem laplaceTerm_abs_bound {r : ℕ} (A : Matrix (Fin (r+1)) (Fin (r+1)) ℤ)
    (N : ℤ) (hN : 0 ≤ N) (hA : ∀ i j, |A i j| ≤ N) (j : Fin (r+1)) :
    |laplaceTerm A j| ≤ (r.factorial : ℤ)*N^(r+1) := by
  have hminor := laplaceDet_bound r (A.submatrix Fin.succ j.succAbove) N (fun i k => hA _ _)
  have hsign : |(-1 : ℤ)^j.val| = 1 := by simp
  simp only [laplaceTerm, abs_mul, hsign, one_mul]
  calc
    _ ≤ N * ((r.factorial : ℤ)*N^r) :=
      mul_le_mul (hA 0 j) hminor (abs_nonneg _) hN
    _ = _ := by rw [pow_succ]; ring

/-- Any partial sum in a recursive expansion has a factorial bound before cancellation. -/
theorem laplace_partial_sum_bound {r : ℕ} (A : Matrix (Fin (r+1)) (Fin (r+1)) ℤ)
    (N : ℤ) (hN : 0 ≤ N) (hA : ∀ i j, |A i j| ≤ N) (J : Finset (Fin (r+1))) :
    |∑ j ∈ J, laplaceTerm A j| ≤ ((r+1).factorial : ℤ)*N^(r+1) := by
  have hJ : J.card ≤ r+1 := by simpa using Finset.card_le_univ J
  have hJ' : (J.card : ℤ) ≤ r+1 := by exact_mod_cast hJ
  have hp : 0 ≤ (r.factorial : ℤ)*N^(r+1) := by positivity
  calc
    _ ≤ ∑ j ∈ J, |laplaceTerm A j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ J, (r.factorial : ℤ)*N^(r+1) :=
      Finset.sum_le_sum (fun j _ => laplaceTerm_abs_bound A N hN hA j)
    _ = (J.card : ℤ)*((r.factorial : ℤ)*N^(r+1)) := by simp [nsmul_eq_mul]
    _ ≤ ((r : ℤ)+1)*((r.factorial : ℤ)*N^(r+1)) := mul_le_mul_of_nonneg_right hJ' hp
    _ = _ := by rw [Nat.factorial_succ]; push_cast; ring

/-- The same bound is expressed in magnitude bits using input-size exponents. -/
theorem laplace_partial_sum_bits {r : ℕ} (A : Matrix (Fin (r+1)) (Fin (r+1)) ℤ)
    (N D L : ℕ) (hr : r+1 ≤ 2^D) (hN : N ≤ 2^L)
    (hA : ∀ i j, |A i j| ≤ (N : ℤ)) (J : Finset (Fin (r+1))) :
    magnitudeBits (∑ j ∈ J, laplaceTerm A j) ≤ (D+L)*(r+1)+1 := by
  have hb := laplace_partial_sum_bound A N (by positivity) hA J
  have hn : (∑ j ∈ J, laplaceTerm A j).natAbs ≤ (r+1).factorial*N^(r+1) := by
    have hi : ((∑ j ∈ J, laplaceTerm A j).natAbs : ℤ) ≤
        (((r+1).factorial*N^(r+1) : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using hb
    exact_mod_cast hi
  exact magnitudeBits_le_of_power_bound _ _ (hn.trans (factorial_power_bound (r+1) N D L hr hN))

end MOR34
