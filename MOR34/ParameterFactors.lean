import MOR34.OracleCostComposition

namespace MOR34

theorem six_power_parameter_bound (q : ℕ) : 6^q ≤ (q+2)^(3*q) := by
  have hh : 6 ≤ (q+2)^3 := (by decide : 6 ≤ 2^3).trans
    (pow_le_pow_left' (by omega : 2 ≤ q+2) 3)
  calc
    _ ≤ ((q+2)^3)^q := pow_le_pow_left' hh q
    _ = _ := by rw [pow_mul]

theorem normal_calls_parameter_bound (q : ℕ) :
    6^q*((q+1)*((q+2)*(q+1)^(2*(q+1)))) ≤ (q+2)^(5*q+4) := by
  calc
    _ ≤ (q+2)^(3*q)*((q+2)^1*((q+2)^1*(q+2)^(2*(q+1)))) := by
      simp only [pow_one]
      exact Nat.mul_le_mul (six_power_parameter_bound q)
        (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega) _)))
    _ = _ := by repeat rw [← pow_add]; congr 1; omega

theorem rowCallFactor_parameter_bound (q : ℕ) : rowCallFactor q ≤ (q+2)^(3*q+5) := by
  have hb : 1 ≤ q+2 := by omega
  have h6 : 6 ≤ (q+2)^3 := (by decide : 6 ≤ 2^3).trans
    (pow_le_pow_left' (by omega : 2 ≤ q+2) 3)
  have h1 : 1 ≤ (q+2)^(3*q+3) := Nat.one_le_pow _ _ hb
  have h2 : 6*2^q ≤ (q+2)^(3*q+3) := by
    calc
      _ ≤ (q+2)^3*(q+2)^q := Nat.mul_le_mul h6 (pow_le_pow_left' (by omega) _)
      _ = (q+2)^(3+q) := by rw [pow_add]
      _ ≤ _ := pow_le_pow_right' hb (by omega)
  have h3 : 2*(q+1)^2*6^q ≤ (q+2)^(3*q+3) := by
    calc
      _ ≤ ((q+2)^1*(q+2)^2)*(q+2)^(3*q) := by
        simp only [pow_one]
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (pow_le_pow_left' (by omega) 2))
          (six_power_parameter_bound q)
      _ = _ := by repeat rw [← pow_add]; congr 1; omega
  calc
    rowCallFactor q ≤ 3*(q+2)^(3*q+3) := by unfold rowCallFactor; omega
    _ ≤ (q+2)^2*(q+2)^(3*q+3) := Nat.mul_le_mul_right _
      ((by decide : 3 ≤ 2^2).trans (pow_le_pow_left' (by omega) 2))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Translation to the paper's positive-coefficient parameter, allowing a zero class. -/
theorem normal_calls_original_parameter (q K : ℕ) (hq : q ≤ K+1) :
    6^q*((q+1)*((q+2)*(q+1)^(2*(q+1)))) ≤ (K+3)^(5*K+9) := by
  exact (normal_calls_parameter_bound q).trans
    ((pow_le_pow_left' (by omega : q+2 ≤ K+3) _).trans
      (pow_le_pow_right' (by omega) (by omega)))

end MOR34
