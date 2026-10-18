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

def cellModesFactor (q I K c : ℕ) : ℕ :=
  functionEnumerationBudget q 3+3^q*(cellLoopFactor q I K c+K+q+3)+1

theorem denseModesBudget_polynomial (q n L N D I c J E K d : ℕ)
    (hN : N ≤ K*(n+L+2)^d) (hD : D ≤ K*(n+L+2)^d)
    (hJ : J ≤ K*(n+L+2)^d) (hE : E ≤ K*(n+L+2)^d) :
    denseModesBudget q n L N D I c J E ≤
      cellModesFactor q I K c*(n+L+2)^(4*c+d+4) := by
  let X := (n+L+2)^(4*c+d+4)
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hd : (n+L+2)^d ≤ X := pow_le_pow_right' (by omega) (by omega)
  have he := hE.trans (Nat.mul_le_mul_left K hd)
  have hb := denseCellLoopBudget_polynomial q n L N D I c J K d hN hD hJ
  change denseCellLoopBudget q n L N D I c J ≤ cellLoopFactor q I K c*X at hb
  have hi : denseCellLoopBudget q n L N D I c J+E+q+3 ≤
      (cellLoopFactor q I K c+K+q+3)*X := by nlinarith
  have hh := Nat.mul_le_mul_left (3^q) hi
  have hf : functionEnumerationBudget q 3+1 ≤ (functionEnumerationBudget q 3+1)*X :=
    Nat.le_mul_of_pos_right _ (by omega)
  dsimp only [denseModesBudget,cellModesFactor]
  change _ ≤ _*X
  nlinarith

def cellExtremaFactor (q I K c : ℕ) : ℕ :=
  2*q*(cellQueryFactor q I K c+q+8)+2*q+3

theorem denseExtremaBudget_polynomial (q n L D I c K d : ℕ)
    (hD : D ≤ K*(n+L+2)^d) :
    denseExtremaBudget q n L D I c ≤
      cellExtremaFactor q I K c*(n+L+2)^(4*c+d+5) := by
  let S := n+L+2
  let X := S^(4*c+d+4)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hS
  have hY : 1 ≤ S*X := by nlinarith
  have hU : denseCellQueryBudget q n L D I c ≤ cellQueryFactor q I K c*X :=
    denseCellQueryBudget_polynomial q n L D I c K d hD
  have hsum : denseCellQueryBudget q n L D I c+q+5 ≤
      (cellQueryFactor q I K c+q+5)*X := by nlinarith
  have hmul := Nat.mul_le_mul (show n+1 ≤ S by dsimp [S]; omega) hsum
  have hi : (n+1)*(denseCellQueryBudget q n L D I c+q+5)+3 ≤
      (cellQueryFactor q I K c+q+8)*(S*X) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*q) hi
  have hconst : 2*q+3 ≤ (2*q+3)*(S*X) := Nat.le_mul_of_pos_right _ (by omega)
  have heq : (n+L+2)^(4*c+d+5) = S*X := by
    change S^((4*c+d+4)+1) = S*X
    rw [pow_succ']
  rw [heq]
  unfold denseExtremaBudget cellExtremaFactor
  nlinarith

def cellParityFactor (q I K c : ℕ) : ℕ :=
  cellQueryFactor q I K c+cellExtremaFactor q I K c+cellModesFactor q I K c+1

theorem denseParityBudget_polynomial (q n L N D I c J E K d : ℕ)
    (hN : N ≤ K*(n+L+2)^d) (hD : D ≤ K*(n+L+2)^d)
    (hJ : J ≤ K*(n+L+2)^d) (hE : E ≤ K*(n+L+2)^d) :
    denseParityBudget q n L N D I c J E ≤
      cellParityFactor q I K c*(n+L+2)^(4*c+d+5) := by
  let X := (n+L+2)^(4*c+d+5)
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hpow : (n+L+2)^(4*c+d+4) ≤ X := pow_le_pow_right' (by omega) (by omega)
  have hq := (denseCellQueryBudget_polynomial q n L D I c K d hD).trans
    (Nat.mul_le_mul_left (cellQueryFactor q I K c) hpow)
  have he := denseExtremaBudget_polynomial q n L D I c K d hD
  change denseExtremaBudget q n L D I c ≤ cellExtremaFactor q I K c*X at he
  have hm := (denseModesBudget_polynomial q n L N D I c J E K d hN hD hJ hE).trans
    (Nat.mul_le_mul_left (cellModesFactor q I K c) hpow)
  dsimp only [denseParityBudget,cellParityFactor]
  change _ ≤ _*X
  nlinarith

def cellSelectionFactor (q I K c : ℕ) : ℕ :=
  functionEnumerationBudget q 2+2^q*(cellParityFactor q I K c+3^q*(q+1)+1)+1

/-- Actual retained selection has a polynomial input exponent independent of q,
provided the established primitive exponents c and d are uniform in q. The
factor may depend on q; no whole-phase runtime premise is assumed. -/
theorem chargedDenseSelection_polynomial {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (K d : ℕ)
    (hN : A.N ≤ K*(Fintype.card (Item m)+A.L+2)^d)
    (hD : A.D ≤ K*(Fintype.card (Item m)+A.L+2)^d)
    (hJ : A.J ≤ K*(Fintype.card (Item m)+A.L+2)^d)
    (hE : A.E ≤ K*(Fintype.card (Item m)+A.L+2)^d) :
    (chargedDenseSelection P hWF solve hs A).2 ≤
      cellSelectionFactor q A.I K A.c*(Fintype.card (Item m)+A.L+2)^(4*A.c+d+5) := by
  let X := (Fintype.card (Item m)+A.L+2)^(4*A.c+d+5)
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hp := denseParityBudget_polynomial q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E K d hN hD hJ hE
  change denseParityBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E ≤
    cellParityFactor q A.I K A.c*X at hp
  have hi : denseParityBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E+3^q*(q+1)+1 ≤
      (cellParityFactor q A.I K A.c+3^q*(q+1)+1)*X := by nlinarith
  have hh := Nat.mul_le_mul_left (2^q) hi
  have he : functionEnumerationBudget q 2+1 ≤ (functionEnumerationBudget q 2+1)*X :=
    Nat.le_mul_of_pos_right _ (by omega)
  apply (chargedDenseSelection_cost P hWF solve hs A).trans
  unfold cellSelectionFactor
  change _ ≤ _*X
  nlinarith

end MOR34
