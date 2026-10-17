import MOR34.BoundedPivotNormals

namespace MOR34

/-- Magnitude bits, with zero using zero magnitude bits. A sign bit is separate. -/
def magnitudeBits (z : ℤ) : ℕ := Nat.clog 2 (z.natAbs + 1)

theorem magnitudeBits_le_of_power_bound (z : ℤ) (e : ℕ)
    (hz : z.natAbs ≤ 2 ^ e) : magnitudeBits z ≤ e + 1 := by
  apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
  have hp : 0 < (2 : ℕ) ^ e := pow_pos (by decide) e
  rw [pow_succ]
  omega

/-- Explicit coefficient-bit bound for the constructed pivot normals. -/
theorem pivotNormal_magnitudeBits {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (N D L : ℕ)
    (hA : ∀ i j, |A i j| ≤ (N : ℤ)) (hC : ∀ i j, |C i j| ≤ (N : ℤ))
    (hr : r ≤ 2 ^ D) (hN : N ≤ 2 ^ L) :
    ∀ k j, magnitudeBits (pivotNormal A C k j) ≤ (D + L) * r + 1 := by
  intro k j
  apply magnitudeBits_le_of_power_bound
  have hb := pivotNormal_bound A C (N : ℤ) (by positivity) hA hC k j
  have hn : (pivotNormal A C k j).natAbs ≤ r.factorial * N ^ r := by
    have hi : ((pivotNormal A C k j).natAbs : ℤ) ≤ ((r.factorial * N ^ r : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using hb
    exact_mod_cast hi
  exact hn.trans (factorial_power_bound r N D L hr hN)

theorem pivotNormal_logarithmic_bits {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (N : ℕ)
    (hA : ∀ i j, |A i j| ≤ (N : ℤ)) (hC : ∀ i j, |C i j| ≤ (N : ℤ)) :
    ∀ k j, magnitudeBits (pivotNormal A C k j) ≤
      (Nat.clog 2 r + Nat.clog 2 N) * r + 1 :=
  pivotNormal_magnitudeBits A C N _ _ hA hC
    (Nat.le_pow_clog (by decide) r) (Nat.le_pow_clog (by decide) N)
end MOR34
