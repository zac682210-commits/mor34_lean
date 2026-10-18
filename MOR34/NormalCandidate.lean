import MOR34.BoundedMatrixNormals

namespace MOR34

/-- A candidate consists of original rows and a nonsingular original-column minor.
Checking that every original row satisfies its integer equations certifies the whole span. -/
theorem selected_rows_span_of_checks {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d)
    (hd : ((M.submatrix a id).submatrix id c).det ≠ 0)
    (hc : ∀ i j, ∑ k, M i k * columnNormal (M.submatrix a id) c j k = 0) :
    integerRowSpan (M.submatrix a id) =
      Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨a i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (columnNormals_describe (M.submatrix a id) c hd _).mpr
    intro j
    have hh := hc i j
    change (∑ k, (M i k : ℚ) * (columnNormal (M.submatrix a id) c j k : ℚ)) = 0
    exact_mod_cast hh

theorem checked_candidate_describes {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d)
    (hd : ((M.submatrix a id).submatrix id c).det ≠ 0)
    (hc : ∀ i j, ∑ k, M i k * columnNormal (M.submatrix a id) c j k = 0)
    (y : Fin d → ℚ) :
    y ∈ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) ↔
      ∀ j, ∑ k, y k * (columnNormal (M.submatrix a id) c j k : ℚ) = 0 := by
  rw [← selected_rows_span_of_checks M a c hd hc]
  exact columnNormals_describe (M.submatrix a id) c hd y

end MOR34
