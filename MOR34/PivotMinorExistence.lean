import MOR34.PivotNormalSpan
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace MOR34

/-- Independent rows admit a nonsingular minor using original columns.
This is an existence result, not yet a costed pivot-search implementation. -/
theorem independent_rows_pivot_minor {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℚ)
    (h : LinearIndependent ℚ M.row) :
    ∃ c : Fin r ↪ Fin d, (M.submatrix id c).det ≠ 0 := by
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
  let c : Fin r ↪ Fin d := ⟨a ∘ e, ha.comp e.injective⟩
  have hc : LinearIndependent ℚ (M.submatrix id c).col := by
    simpa only [Matrix.col, Matrix.submatrix, Function.comp_def, c,
      Function.Embedding.coeFn_mk, id_eq] using hli.comp e e.injective
  refine ⟨c, ?_⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hc))

end MOR34
