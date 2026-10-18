import MOR34.FiniteDeterminant

namespace MOR34

/-- Sum the supplied operation charges along the actual first-witness path.
The charge model deliberately excludes list construction and branching cost. -/
def firstWitnessCharge {Q α : Type*} (solve : Q → Option α) (charge : Q → ℕ) : List Q → ℕ
  | [] => 0
  | x :: xs => charge x + match solve x with
    | some _ => 0
    | none => firstWitnessCharge solve charge xs

theorem firstWitnessCharge_bound {Q α : Type*} (solve : Q → Option α)
    (charge : Q → ℕ) (C : ℕ) (hc : ∀ x, charge x ≤ C) (L : List Q) :
    firstWitnessCharge solve charge L ≤ firstWitnessCalls solve L * C := by
  induction L with
  | nil => simp [firstWitnessCharge, firstWitnessCalls]
  | cons x xs ih =>
    cases hs : solve x with
    | none =>
      simp only [firstWitnessCharge, firstWitnessCalls, hs]
      have hx := hc x
      nlinarith
    | some y => simpa [firstWitnessCharge, firstWitnessCalls, hs] using hc x

/-- Only determinant arithmetic is charged; injectivity testing and minor construction
are separate obligations. Noninjective maps do not trigger determinant evaluation. -/
def pivotDetCharge {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (f : Fin r → Fin d) : ℕ :=
  if Function.Injective f then (tracedLaplaceDet r (M.submatrix id f)).2 else 0

theorem pivotDetCharge_bound {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) (f : Fin r → Fin d) :
    pivotDetCharge M f ≤ laplaceArithmeticBudget r := by
  by_cases hi : Function.Injective f
  · simpa only [pivotDetCharge, if_pos hi] using tracedLaplaceDet_cost r (M.submatrix id f)
  · simp [pivotDetCharge, hi]

def exactPivotDetCharge {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) : ℕ :=
  firstWitnessCharge (tryPivot M (laplaceDet r)) (pivotDetCharge M) (allFinFunctions r d)

theorem exactPivotDetCharge_bound {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ) :
    exactPivotDetCharge M ≤ d^r * ((r+3)^2 * r.factorial) := by
  calc
    _ ≤ firstWitnessCalls (tryPivot M (laplaceDet r)) (allFinFunctions r d) * laplaceArithmeticBudget r :=
      firstWitnessCharge_bound _ _ _ (pivotDetCharge_bound M) _
    _ ≤ d^r * laplaceArithmeticBudget r := Nat.mul_le_mul_right _ (exactPivotSearch_calls M)
    _ ≤ _ := Nat.mul_le_mul_left _ (laplaceArithmeticBudget_bound r)

end MOR34
