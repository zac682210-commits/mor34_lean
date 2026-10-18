import MOR34.PivotSearch
import MOR34.CramerBounds

namespace MOR34

/-- A concrete recursive determinant evaluator on finite integer matrices. -/
def laplaceDet : (r : ℕ) → Matrix (Fin r) (Fin r) ℤ → ℤ
  | 0, _ => 1
  | r+1, A => ∑ j : Fin (r+1), (-1) ^ j.val * A 0 j *
      laplaceDet r (A.submatrix Fin.succ j.succAbove)

theorem laplaceDet_correct (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) :
    laplaceDet r A = A.det := by
  induction r with
  | zero => simp [laplaceDet]
  | succ r ih =>
    rw [Matrix.det_succ_row_zero]
    simp only [laplaceDet, ih]

/-- Arithmetic-operation upper-budget for direct recursive expansion. Each sign power
is charged up to r multiplications; row extraction and indexing are separate. -/
def laplaceArithmeticBudget : ℕ → ℕ
  | 0 => 0
  | r+1 => (r+1) * (laplaceArithmeticBudget r + r + 3)

theorem laplaceArithmeticBudget_bound (r : ℕ) :
    laplaceArithmeticBudget r ≤ (r+3)^2 * r.factorial := by
  induction r with
  | zero => simp [laplaceArithmeticBudget]
  | succ r ih =>
    rw [laplaceArithmeticBudget, Nat.factorial_succ]
    have hf : 1 ≤ r.factorial := Nat.factorial_pos r
    calc
      (r+1) * (laplaceArithmeticBudget r + r + 3) ≤
          (r+1) * ((r+3)^2 * r.factorial + r + 3) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (r+1) * ((r+1+3)^2 * r.factorial) := by
        apply Nat.mul_le_mul_left
        nlinarith
      _ = _ := by ring

/-- The determinant correctness assumption in the finite pivot search is discharged. -/
def exactPivotSearch {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) : Option (Fin r ↪ Fin d) :=
  pivotSearch M (laplaceDet r)

theorem exactPivotSearch_sound {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (c : Fin r ↪ Fin d) (hc : exactPivotSearch M = some c) : (M.submatrix id c).det ≠ 0 :=
  pivotSearch_sound M (laplaceDet r) (laplaceDet_correct r) c hc

theorem exactPivotSearch_complete {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (h : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row) :
    ∃ c, exactPivotSearch M = some c :=
  pivotSearch_complete M (laplaceDet r) (laplaceDet_correct r) h

theorem exactPivotSearch_calls {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) :
    firstWitnessCalls (tryPivot M (laplaceDet r)) (allFinFunctions r d) ≤ d ^ r :=
  pivotSearch_calls M (laplaceDet r)

/-- Every subdeterminant value has the standard factorial magnitude bound. -/
theorem laplaceDet_bound (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) (N : ℤ)
    (hA : ∀ i j, |A i j| ≤ N) : |laplaceDet r A| ≤ (r.factorial : ℤ) * N ^ r := by
  rw [laplaceDet_correct]
  exact integer_det_bound A N hA

end MOR34
