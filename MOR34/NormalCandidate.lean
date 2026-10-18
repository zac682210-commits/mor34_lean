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

/-- The finite candidate test is complete: some original-row/column candidate passes.
This is an existence proof for the future enumerator, not the enumerator itself. -/
theorem normal_candidate_exists {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    ∃ r : ℕ, r ≤ d ∧ ∃ a : Fin r ↪ Fin s, ∃ c : Fin r ↪ Fin d,
      ((M.submatrix a id).submatrix id c).det ≠ 0 ∧
      ∀ i j, ∑ k, M i k * columnNormal (M.submatrix a id) c j k = 0 := by
  classical
  obtain ⟨ρ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ (M.map (Int.castRingHom ℚ)).row
  letI : Finite ρ := Finite.of_injective a ha
  letI : Fintype ρ := Fintype.ofFinite ρ
  let r := Fintype.card ρ
  let e : Fin r ≃ ρ := (Fintype.equivFin ρ).symm
  let a' : Fin r ↪ Fin s := ⟨a ∘ e, ha.comp e.injective⟩
  let R : Matrix (Fin r) (Fin d) ℤ := M.submatrix a' id
  have hR : LinearIndependent ℚ (R.map (Int.castRingHom ℚ)).row := by
    simpa only [R, a', Matrix.row, Matrix.map, Matrix.submatrix_apply,
      Function.Embedding.coeFn_mk, Function.comp_def, id_eq] using hli.comp e e.injective
  have hs : integerRowSpan R = Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) := by
    have he : Set.range (R.map (Int.castRingHom ℚ)).row =
        Set.range ((M.map (Int.castRingHom ℚ)).row ∘ a) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨e.symm i, ?_⟩
        funext j
        change (M (a (e (e.symm i))) j : ℚ) = (M (a i) j : ℚ)
        rw [e.apply_symm_apply]
    rw [integerRowSpan, he, hspan]
  obtain ⟨c, hc⟩ := independent_integer_rows_pivot R hR
  have hrd : r ≤ d := by simpa using Fintype.card_le_of_injective c c.injective
  refine ⟨r, hrd, a', c, hc, ?_⟩
  intro i j
  have hm : (M.map (Int.castRingHom ℚ)).row i ∈ integerRowSpan R := by
    rw [hs]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hh := (columnNormals_describe R c hc _).mp hm j
  change (∑ k, (M i k : ℚ) * (columnNormal R c j k : ℚ)) = 0 at hh
  exact_mod_cast hh

end MOR34
