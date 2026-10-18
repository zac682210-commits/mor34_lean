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

/-- A deterministic arithmetic trace. Indexing, storage and integer bit costs are not charged. -/
def tracedLaplaceDet : (r : ℕ) → Matrix (Fin r) (Fin r) ℤ → ℤ × ℕ
  | 0, _ => (1, 0)
  | r+1, A =>
    let sub := fun j : Fin (r+1) => tracedLaplaceDet r (A.submatrix Fin.succ j.succAbove)
    (∑ j : Fin (r+1), (-1) ^ j.val * A 0 j * (sub j).1,
      ∑ j : Fin (r+1), ((sub j).2 + j.val + 3))

theorem tracedLaplaceDet_value (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) :
    (tracedLaplaceDet r A).1 = laplaceDet r A := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [tracedLaplaceDet, laplaceDet, ih]

theorem tracedLaplaceDet_cost (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) :
    (tracedLaplaceDet r A).2 ≤ laplaceArithmeticBudget r := by
  induction r with
  | zero => simp [tracedLaplaceDet, laplaceArithmeticBudget]
  | succ r ih =>
    change (∑ j : Fin (r+1), ((tracedLaplaceDet r (A.submatrix Fin.succ j.succAbove)).2 + j.val + 3)) ≤ _
    calc
      _ ≤ ∑ _j : Fin (r+1), (laplaceArithmeticBudget r + r + 3) := by
        apply Finset.sum_le_sum
        intro j _
        have hh := ih (A.submatrix Fin.succ j.succAbove)
        have hj := j.isLt
        omega
      _ = laplaceArithmeticBudget (r+1) := by simp [laplaceArithmeticBudget]

theorem tracedLaplaceDet_correct_and_cost (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) :
    (tracedLaplaceDet r A).1 = A.det ∧
      (tracedLaplaceDet r A).2 ≤ (r+3)^2 * r.factorial :=
  ⟨(tracedLaplaceDet_value r A).trans (laplaceDet_correct r A),
    (tracedLaplaceDet_cost r A).trans (laplaceArithmeticBudget_bound r)⟩

end MOR34
