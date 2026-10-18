import MOR34.CellQueryBounds

namespace MOR34

/-- Natural version of the already proved bounded-normal coefficient radius. -/
def normalRadius (q N : ℕ) : ℕ := 2 * (q+1).factorial * N^(q+1)

def uniformRowRadius (q N M : ℕ) : ℕ := (6*N+10) * (M + normalRadius q N + 1)

def uniformRowBits (q N M : ℕ) : ℕ := Nat.clog 2 N + Nat.clog 2 (M+1) +
  (Nat.clog 2 (q+1) + Nat.clog 2 N) * (q+1) + 8

theorem normalRadius_cast (q N : ℕ) : (normalRadius q N : ℤ) = normalCoefficientBound q N := by
  simp [normalRadius, normalCoefficientBound]

theorem normalRadius_power_bound (q N : ℕ) :
    normalRadius q N ≤ 2^((Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1)+1) := by
  have h := factorial_power_bound (q+1) N (Nat.clog 2 (q+1)) (Nat.clog 2 N)
    (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
  unfold normalRadius
  calc
    2 * (q+1).factorial * N^(q+1) = 2 * ((q+1).factorial * N^(q+1)) := by ring
    _ ≤ 2 * 2^((Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1)) := Nat.mul_le_mul_left 2 h
    _ = _ := by rw [pow_succ]; omega

theorem uniformRowRadius_power_bound (q N M : ℕ) (hN : 1 ≤ N) :
    uniformRowRadius q N M ≤ 2^(Nat.clog 2 N + Nat.clog 2 (M+1) +
      (Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1) + 6) := by
  let D := Nat.clog 2 N
  let L := Nat.clog 2 (M+1)
  let E := (Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1)
  have hn : N ≤ 2^D := Nat.le_pow_clog (by decide) _
  have hm : M+1 ≤ 2^L := Nat.le_pow_clog (by decide) _
  have hh : normalRadius q N ≤ 2^(E+1) := normalRadius_power_bound q N
  have h1 : 6*N+10 ≤ 2^(D+4) := by rw [pow_add]; norm_num; omega
  have hpL : 1 ≤ 2^L := Nat.one_le_pow L 2 (by decide)
  have hpE : 1 ≤ 2^(E+1) := Nat.one_le_pow (E+1) 2 (by decide)
  have h2 : M + normalRadius q N + 1 ≤ 2^(L+E+2) := by
    calc
      _ ≤ 2^L + 2^(E+1) := by omega
      _ ≤ 2 * (2^L * 2^(E+1)) := by nlinarith
      _ = _ := by
        rw [← pow_add, show L+E+2 = (L+(E+1))+1 by omega, pow_succ]
        omega
  calc
    uniformRowRadius q N M ≤ 2^(D+4) * 2^(L+E+2) := Nat.mul_le_mul h1 h2
    _ = 2^(D+L+E+6) := by rw [← pow_add]; congr 1; omega

theorem uniformRow_signed_bits (q N M : ℕ) (hN : 1 ≤ N) (z : ℤ)
    (hz : |z| ≤ (uniformRowRadius q N M : ℤ)) :
    signedIntegerBits z ≤ uniformRowBits q N M := by
  have hn : z.natAbs ≤ uniformRowRadius q N M := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (uniformRowRadius q N M : ℤ) by simpa using hz)
  have hh := magnitudeBits_le_of_power_bound z _ (hn.trans (uniformRowRadius_power_bound q N M hN))
  unfold signedIntegerBits uniformRowBits
  omega

/-- One radius dominates both count coefficients, cost coefficients and right sides
in actual cell-separation parity queries. q<=N is the original-input size condition. -/
theorem cellRow_uniform_bound {q : ℕ} (L : CountInequality q) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : q ≤ N)
    (h : L.IntegerBounded (2*((M : ℤ)+(normalCoefficientBound q N+1)+1)) 1
      (rowConstantBound N M ((N : ℤ)+normalCoefficientBound q N+3)+
        q*((M : ℤ)+(normalCoefficientBound q N+1)+1))) :
    L.IntegerBounded (uniformRowRadius q N M) (uniformRowRadius q N M) (uniformRowRadius q N M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hq' : (q : ℤ) ≤ N := by exact_mod_cast hq
  have hH : (0 : ℤ) ≤ normalCoefficientBound q N := by unfold normalCoefficientBound; positivity
  have hNH := mul_nonneg (show (0 : ℤ) ≤ N by positivity) hH
  have hNM : (0 : ℤ) ≤ (N : ℤ) * M := by positivity
  have hmul := mul_le_mul_of_nonneg_right hq'
    (show (0 : ℤ) ≤ (M : ℤ)+normalCoefficientBound q N+2 by omega)
  have hR : (uniformRowRadius q N M : ℤ) =
      (6*(N : ℤ)+10)*((M : ℤ)+normalCoefficientBound q N+1) := by
    simp only [uniformRowRadius, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, normalRadius_cast]
  apply integerRow_bound_mono L h
  · rw [hR]; nlinarith
  · rw [hR]; nlinarith
  · rw [hR]; unfold rowConstantBound; nlinarith

end MOR34
