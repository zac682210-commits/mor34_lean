import MOR34.CompressionSize

namespace MOR34

/-- The explicit construction bounds use n+L+2, rather than the older n+L+1.
The offset is absorbed with coefficient 20 instead of 19. -/
theorem compressed_size_offset_bound (n L : ℕ) (hL : L ≤ 18*(n+1)^4) :
    n+L+2 ≤ 20*(n+1)^4 := by
  have hn : n+1 ≤ (n+1)^4 := le_self_pow₀ (by omega) (by decide)
  have hpos : 1 ≤ (n+1)^4 := Nat.one_le_pow _ _ (by omega)
  omega

theorem compression_cost_substitution_two (n L F c cost : ℕ)
    (hL : L ≤ 18*(n+1)^4) (hcost : cost ≤ F*(n+L+2)^c) :
    cost ≤ (F*20^c)*(n+1)^(4*c) := by
  calc
    _ ≤ F*(n+L+2)^c := hcost
    _ ≤ F*(20*(n+1)^4)^c :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' (compressed_size_offset_bound n L hL) c)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Standard preprocessing and a proved compressed-core bound combine without
letting the parameter enter the input exponent. This remains conditional on
the supplied core-cost premise, not a full coverage theorem. -/
theorem compressed_core_and_preprocessing (n L inputBits F C c e core prep : ℕ)
    (hL : L ≤ 18*(n+1)^4) (hcore : core ≤ F*(n+L+2)^c)
    (hprep : prep ≤ C*(n+inputBits+2)^e) :
    prep+core ≤ (C+F*20^c)*(n+inputBits+2)^(e+4*c) := by
  let t := n+inputBits+2
  have ht : 1 ≤ t := by dsimp [t]; omega
  have h₁ : t^e ≤ t^(e+4*c) := pow_le_pow_right' ht (by omega)
  have h₂ : (n+1)^(4*c) ≤ t^(e+4*c) :=
    (pow_le_pow_left' (by dsimp [t]; omega) _).trans (pow_le_pow_right' ht (by omega))
  have hc := (compression_cost_substitution_two n L F c core hL hcore).trans
    (Nat.mul_le_mul_left _ h₂)
  have hp := hprep.trans (Nat.mul_le_mul_left C h₁)
  calc
    _ ≤ C*t^(e+4*c)+(F*20^c)*t^(e+4*c) := Nat.add_le_add hp hc
    _ = _ := by ring

end MOR34
