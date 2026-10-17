import MOR34.PivotMinorExistence
import MOR34.PivotNormalBits

namespace MOR34
variable {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Row span over the rationals, retaining the original integer matrix. -/
def integerRowSpan (M : Matrix (Fin r) ι ℤ) : Submodule ℚ (ι → ℚ) :=
  Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row)

def columnNormal (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι) (j k : ι) : ℤ :=
  (if k = j then (M.submatrix id c).det else 0) -
    ∑ i : Fin r, if c i = k then (M.submatrix id c).cramer (fun a => M a j) i else 0

theorem columnNormal_pairing (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι)
    (j : ι) (y : ι → ℚ) :
    (∑ k, y k * (columnNormal M c j k : ℚ)) =
      y j * ((M.submatrix id c).det : ℚ) -
      ∑ i : Fin r, y (c i) * ((M.submatrix id c).cramer (fun a => M a j) i : ℚ) := by
  simp only [columnNormal, Int.cast_sub, Int.cast_sum, Int.cast_ite, Int.cast_zero,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem integerRowSpan_iff (M : Matrix (Fin r) ι ℤ) (y : ι → ℚ) :
    y ∈ integerRowSpan M ↔ ∃ w : Fin r → ℚ, ∀ k, y k = ∑ i, w i * (M i k : ℚ) := by
  rw [integerRowSpan, ← Matrix.range_vecMulLinear]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, fun k => (congrFun hw k).symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, funext (fun k => (hw k).symm)⟩

theorem column_cramer_pair (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι)
    (j : ι) (w : Fin r → ℚ) :
    (∑ l, (∑ i, w i * (M i (c l) : ℚ)) *
      ((M.submatrix id c).cramer (fun a => M a j) l : ℚ)) =
      ((M.submatrix id c).det : ℚ) * ∑ i, w i * (M i j : ℚ) := by
  have hcr (i : Fin r) :
      (∑ l, (M i (c l) : ℚ) * ((M.submatrix id c).cramer (fun a => M a j) l : ℚ)) =
        ((M.submatrix id c).det : ℚ) * (M i j : ℚ) := by
    have hh := congrFun (Matrix.mulVec_cramer (M.submatrix id c) (fun a => M a j)) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Matrix.submatrix_apply, id_eq] at hh
    exact_mod_cast hh
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original-column Cramer equations characterize the complete row span. -/
theorem columnNormals_describe (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι)
    (hd : (M.submatrix id c).det ≠ 0) (y : ι → ℚ) :
    y ∈ integerRowSpan M ↔ ∀ j, ∑ k, y k * (columnNormal M c j k : ℚ) = 0 := by
  have hd' : ((M.submatrix id c).det : ℚ) ≠ 0 := by exact_mod_cast hd
  constructor
  · intro hy j
    obtain ⟨w, hw⟩ := (integerRowSpan_iff M y).mp hy
    rw [columnNormal_pairing]
    simp_rw [hw]
    rw [column_cramer_pair]
    ring
  · intro hy
    let A := (M.submatrix id c).map (Int.castRingHom ℚ)
    have hdet : A.det ≠ 0 := by
      have he : A.det = ((M.submatrix id c).det : ℚ) := by
        simpa [A] using ((Int.castRingHom ℚ).map_det (M.submatrix id c)).symm
      rwa [he]
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
    obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hu) (fun i => y (c i))
    have hw' (l : Fin r) : y (c l) = ∑ i, w i * (M i (c l) : ℚ) :=
      (congrFun hw l).symm
    apply (integerRowSpan_iff M y).mpr
    refine ⟨w, ?_⟩
    intro j
    have hj := hy j
    rw [columnNormal_pairing] at hj
    simp_rw [hw'] at hj
    rw [column_cramer_pair] at hj
    exact (mul_right_cancel₀ hd') (by nlinarith [hj])

end MOR34
