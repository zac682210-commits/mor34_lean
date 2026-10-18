import MOR34.NormalEnumerationAggregation

namespace MOR34

/-- The explicit key construction preserves the manuscript's singly exponential
q log q parameter dependence, not merely abstract fixed-parameter tractability. -/
theorem normalKeyBuildBudget_parameter_bound (d : ℕ) :
    normalKeyBuildBudget d ≤ (d+4)^(2*d+7) := by
  let b := d+4
  let P := b^(2*d+4)
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hb
  have hA : (d+3)^2*(d+1)^(d+1) ≤ P := by
    calc
      _ ≤ b^2*b^(2*d+2) := Nat.mul_le_mul
        (pow_le_pow_left' (by dsimp [b]; omega) _)
        ((pow_le_pow_left' (by dsimp [b]; omega) _).trans
          (pow_le_pow_right' hb (by omega)))
      _ = P := by rw [← pow_add]; congr 1; omega
  have hD : ((d+1)^d)*((d+1)^d) ≤ P := by
    calc
      _ ≤ b^d*b^d := Nat.mul_le_mul
        (pow_le_pow_left' (by dsimp [b]; omega) _)
        (pow_le_pow_left' (by dsimp [b]; omega) _)
      _ = b^(2*d) := by rw [← pow_add]; congr 1; omega
      _ ≤ P := pow_le_pow_right' hb (by omega)
  have hr : rankKeyBuildBudget d ≤ 8*P := by
    unfold rankKeyBuildBudget
    nlinarith
  have hk : normalKeyBuildBudget d ≤ (11*d+12)*P := by
    unfold normalKeyBuildBudget
    nlinarith
  have hc : 11*d+12 ≤ b^3 := by dsimp [b]; nlinarith
  calc
    _ ≤ (11*d+12)*P := hk
    _ ≤ b^3*P := Nat.mul_le_mul_right _ hc
    _ = _ := by dsimp [P,b]; rw [← pow_add]; congr 1; omega

theorem normalEnumerationFactor_parameter_bound (q : ℕ) :
    6^q*(q+1)*normalKeyBuildBudget (q+1) ≤ (q+5)^(4*q+10) := by
  have hb : 1 ≤ q+5 := by omega
  have h6 : 6^q ≤ (q+5)^(2*q) := by
    calc
      _ ≤ ((q+5)^2)^q := pow_le_pow_left' (by nlinarith) q
      _ = _ := by rw [pow_mul]
  have hk : normalKeyBuildBudget (q+1) ≤ (q+5)^(2*q+9) := by
    simpa only [show q+1+4=q+5 by omega, show 2*(q+1)+7=2*q+9 by omega]
      using normalKeyBuildBudget_parameter_bound (q+1)
  calc
    _ ≤ (q+5)^(2*q)*(q+5)*(q+5)^(2*q+9) :=
      Nat.mul_le_mul (Nat.mul_le_mul h6 (by omega)) hk
    _ = _ := by rw [← pow_succ, ← pow_add]; congr 1; omega

theorem builtNormalParameter_bound (q : ℕ) :
    builtNormalParameter q ≤ (q+5)^(6*q+14) := by
  let P := (q+5)^(6*q+13)
  have hb : 1 ≤ q+5 := by omega
  have ha : (q+4)^(6*q+13) ≤ P := pow_le_pow_left' (by omega) _
  have he : 6^q*(q+1)*normalKeyBuildBudget (q+1) ≤ P :=
    (normalEnumerationFactor_parameter_bound q).trans (pow_le_pow_right' hb (by omega))
  have hc : 2*P ≤ P*(q+5) := by nlinarith
  have hh : builtNormalParameter q ≤ P*(q+5) := by unfold builtNormalParameter; omega
  simpa only [P, ← pow_succ, show 6*q+13+1=6*q+14 by omega] using hh

end MOR34
