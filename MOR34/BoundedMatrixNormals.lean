import MOR34.ColumnNormalBounds

namespace MOR34

theorem independent_rows_pivot_columns {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) ι ℚ)
    (h : LinearIndependent ℚ M.row) :
    ∃ c : Fin r ↪ ι, (M.submatrix id c).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ M.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    have hh := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card κ = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (M.col ∘ a))) at hh
    rw [hspan, ← Matrix.rank_eq_finrank_span_cols, h.rank_matrix, Fintype.card_fin] at hh
    exact hh
  let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let c : Fin r ↪ ι := ⟨a ∘ e, ha.comp e.injective⟩
  have hc : LinearIndependent ℚ (M.submatrix id c).col := by
    simpa only [Matrix.col, Matrix.submatrix, Function.comp_def, c,
      Function.Embedding.coeFn_mk, id_eq] using hli.comp e e.injective
  refine ⟨c, ?_⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hc))


theorem independent_integer_rows_pivot {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) ι ℤ) (h : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row) :
    ∃ c : Fin r ↪ ι, (M.submatrix id c).det ≠ 0 := by
  obtain ⟨c, hc⟩ := independent_rows_pivot_columns (M.map (Int.castRingHom ℚ)) h
  refine ⟨c, ?_⟩
  intro hz
  apply hc
  calc
    ((M.map (Int.castRingHom ℚ)).submatrix id c).det = ((M.submatrix id c).det : ℚ) :=
      ((Int.castRingHom ℚ).map_det (M.submatrix id c)).symm
    _ = 0 := by rw [hz]; rfl

/-- Every finite bounded integer row family has a bounded family of integer defining equations.
The proof chooses an independent row subfamily and an original-column pivot minor.
This is not a costed implementation of the choices. -/
theorem bounded_matrix_normals {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (M : Matrix κ ι ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hM : ∀ i j, |M i j| ≤ (N : ℤ)) :
    ∃ v : ι → ι → ℤ,
      (∀ y : ι → ℚ,
        y ∈ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) ↔
          ∀ j, ∑ k, y k * (v j k : ℚ) = 0) ∧
      (∀ j k, |v j k| ≤ 2 * ((Fintype.card ι).factorial : ℤ) * (N : ℤ) ^ Fintype.card ι) := by
  classical
  obtain ⟨ρ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ (M.map (Int.castRingHom ℚ)).row
  letI : Finite ρ := Finite.of_injective a ha
  letI : Fintype ρ := Fintype.ofFinite ρ
  let r := Fintype.card ρ
  let e : Fin r ≃ ρ := (Fintype.equivFin ρ).symm
  let R : Matrix (Fin r) ι ℤ := fun i j => M (a (e i)) j
  have hR : LinearIndependent ℚ (R.map (Int.castRingHom ℚ)).row := by
    simpa only [R, Matrix.row, Matrix.map, Function.comp_def] using hli.comp e e.injective
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
  refine ⟨columnNormal R c, ?_, ?_⟩
  · intro y
    rw [← hs]
    exact columnNormals_describe R c hc y
  · exact columnNormal_uniform_bound R c N hN (fun i j => hM (a (e i)) j)

end MOR34
