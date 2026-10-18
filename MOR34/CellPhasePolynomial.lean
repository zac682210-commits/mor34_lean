import MOR34.ChargedParityFamily

namespace MOR34

/-- This factor depends on the parameter and primitive constants only. -/
def cellQueryFactor (q I K c : ℕ) : ℕ :=
  2048+I*180^c+q*(K+2)+20*(q+1)^3+4

theorem denseCellQueryBudget_polynomial (q n L D I c K d : ℕ)
    (hD : D ≤ K*(n+L+2)^d) :
    denseCellQueryBudget q n L D I c ≤
      cellQueryFactor q I K c*(n+L+2)^(4*c+d+4) := by
  let S := n+L+2
  let X := S^(4*c+d+4)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hS
  have hd : S^d ≤ X := pow_le_pow_right' hS (by omega)
  have h4 : (n+1)^4 ≤ X :=
    (pow_le_pow_left' (show n+1 ≤ S by dsimp [S]; omega) 4).trans
      (pow_le_pow_right' hS (by omega))
  have hc : S^(4*c) ≤ X := pow_le_pow_right' hS (by omega)
  have hsolver : I*(180*S^4)^c ≤ (I*180^c)*X := by
    rw [mul_pow,← pow_mul]
    exact (Nat.mul_le_mul_left I (Nat.mul_le_mul_left (180^c) hc)).trans_eq (by ring)
  have hdecode : q*(D+2) ≤ (q*(K+2))*X := by
    have hh : D ≤ K*X := hD.trans (Nat.mul_le_mul_left K hd)
    calc
      _ ≤ q*((K+2)*X) := Nat.mul_le_mul_left q (by nlinarith)
      _ = _ := by ring
  have hcon := Nat.mul_le_mul_left 2048 h4
  have hrestr : 20*(q+1)^3+4 ≤ (20*(q+1)^3+4)*X :=
    Nat.le_mul_of_pos_right _ (by omega)
  dsimp only [denseCellQueryBudget,cellQueryFactor]
  change 2048*(n+1)^4+I*(180*S^4)^c+q*(D+2)+20*(q+1)^3+4 ≤ _*X
  nlinarith

/-- Positive affine reference budgets scale with a common local-cost envelope. -/
theorem chargedCellStepBudget_scale (q N U K V X : ℕ) (hX : 1 ≤ X)
    (hN : N ≤ K*X) (hU : U ≤ V*X) :
    chargedCellStepBudget q N U ≤ chargedCellStepBudget q K V*X := by
  have hn : N+1 ≤ (K+1)*X := by nlinarith
  have hu : U+1 ≤ (V+1)*X := by nlinarith
  have h1 : (q+1)*(4*(q+1)*(N+1)+3) ≤
      ((q+1)*(4*(q+1)*(K+1)+3))*X := by
    have ht := Nat.mul_le_mul_left (4*(q+1)) hn
    calc
      _ ≤ (q+1)*((4*(q+1)*(K+1)+3)*X) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have h2 := Nat.mul_le_mul_left (2*(q+1)) hu
  have h0 : builtCountFormBudget q+2 ≤ (builtCountFormBudget q+2)*X :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold chargedCellStepBudget
  nlinarith

def cellLoopFactor (q I K c : ℕ) : ℕ :=
  (q+1)*(chargedCellStepBudget q K (cellQueryFactor q I K c)+K+1)+1

theorem denseCellLoopBudget_polynomial (q n L N D I c J K d : ℕ)
    (hN : N ≤ K*(n+L+2)^d) (hD : D ≤ K*(n+L+2)^d) (hJ : J ≤ K*(n+L+2)^d) :
    denseCellLoopBudget q n L N D I c J ≤
      cellLoopFactor q I K c*(n+L+2)^(4*c+d+4) := by
  let S := n+L+2
  let X := S^(4*c+d+4)
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by dsimp [S]; omega)
  have hd : S^d ≤ X := pow_le_pow_right' (by dsimp [S]; omega) (by omega)
  have hN' := hN.trans (Nat.mul_le_mul_left K hd)
  have hJ' := hJ.trans (Nat.mul_le_mul_left K hd)
  have hstep := chargedCellStepBudget_scale q N (denseCellQueryBudget q n L D I c)
    K (cellQueryFactor q I K c) X hX hN' (denseCellQueryBudget_polynomial q n L D I c K d hD)
  have hh : chargedCellStepBudget q N (denseCellQueryBudget q n L D I c)+J+1 ≤
      (chargedCellStepBudget q K (cellQueryFactor q I K c)+K+1)*X := by nlinarith
  have hh' := Nat.mul_le_mul_left (q+1) hh
  dsimp only [denseCellLoopBudget,cellLoopFactor]
  change _ ≤ _*X
  nlinarith

end MOR34
