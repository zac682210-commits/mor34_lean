import MOR34.PivotMinorExistence
import MOR34.LinearOracle
import Mathlib.Data.List.FinRange

namespace MOR34

/-- An explicit list of all maps between two finite ordinal types. -/
def allFinFunctions : (r d : ℕ) → List (Fin r → Fin d)
  | 0, _ => [Fin.elim0]
  | r + 1, d => (List.finRange d).flatMap fun j =>
      (allFinFunctions r d).map (fun f => Fin.cases j f)

theorem mem_allFinFunctions (r d : ℕ) (f : Fin r → Fin d) : f ∈ allFinFunctions r d := by
  induction r with
  | zero =>
    have he : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [allFinFunctions, he]
  | succ r ih =>
    have he : f = Fin.cases (f 0) (fun i => f i.succ) := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨f 0, List.mem_finRange _, ?_⟩
    exact List.mem_map.mpr ⟨fun i => f i.succ, ih _, he.symm⟩

theorem allFinFunctions_length (r d : ℕ) : (allFinFunctions r d).length = d ^ r := by
  induction r with
  | zero => simp [allFinFunctions]
  | succ r ih => simp [allFinFunctions, List.length_flatMap, ih, pow_succ, mul_comm]

/-- Determinant evaluation is an explicit supplied operation. -/
def tryPivot {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (detEval : Matrix (Fin r) (Fin r) ℤ → ℤ) (f : Fin r → Fin d) : Option (Fin r ↪ Fin d) :=
  if hi : Function.Injective f then
    if detEval (M.submatrix id f) = 0 then none else some ⟨f, hi⟩
  else none

def pivotSearch {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (detEval : Matrix (Fin r) (Fin r) ℤ → ℤ) : Option (Fin r ↪ Fin d) :=
  firstWitness (tryPivot M detEval) (allFinFunctions r d)

theorem pivotSearch_sound {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (detEval : Matrix (Fin r) (Fin r) ℤ → ℤ) (hd : ∀ A, detEval A = A.det)
    (c : Fin r ↪ Fin d) (hc : pivotSearch M detEval = some c) :
    (M.submatrix id c).det ≠ 0 := by
  obtain ⟨f, _, hf⟩ := firstWitness_some (tryPivot M detEval) (allFinFunctions r d) c hc
  unfold tryPivot at hf
  split_ifs at hf with hi hz
  · simp at hf
  · have he : (⟨f, hi⟩ : Fin r ↪ Fin d) = c := Option.some.inj hf
    subst c
    simpa [hd] using hz
  · simp at hf

theorem pivotSearch_complete {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (detEval : Matrix (Fin r) (Fin r) ℤ → ℤ) (hd : ∀ A, detEval A = A.det)
    (h : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row) :
    ∃ c, pivotSearch M detEval = some c := by
  obtain ⟨c, hc⟩ := independent_rows_pivot_minor (M.map (Int.castRingHom ℚ)) h
  have hci : (M.submatrix id c).det ≠ 0 := by
    intro hz
    apply hc
    calc
      ((M.map (Int.castRingHom ℚ)).submatrix id c).det = ((M.submatrix id c).det : ℚ) :=
        ((Int.castRingHom ℚ).map_det (M.submatrix id c)).symm
      _ = 0 := by rw [hz]; rfl
  cases he : pivotSearch M detEval with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have hh := firstWitness_none (tryPivot M detEval) (allFinFunctions r d) he c
      (mem_allFinFunctions r d c)
    simp [tryPivot, c.injective, hd, hci] at hh

theorem pivotSearch_calls {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (detEval : Matrix (Fin r) (Fin r) ℤ → ℤ) :
    firstWitnessCalls (tryPivot M detEval) (allFinFunctions r d) ≤ d ^ r := by
  simpa only [allFinFunctions_length] using
    firstWitness_calls_le (tryPivot M detEval) (allFinFunctions r d)

end MOR34
