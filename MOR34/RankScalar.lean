import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Real.Basic

namespace MOR34

/-- Square-matrix rank is unchanged by an embedding of fields. -/
theorem square_matrix_rank_map {ι K L : Type*} [Fintype ι]
    [Field K] [Field L] (f : K →+* L) (A : Matrix ι ι K) :
    (A.map f).rank = A.rank := by
  classical
  obtain ⟨ls, rs, d, he⟩ := Matrix.TransvectionStruct.exists_list_transvec_mul_diagonal_mul_list_transvec A
  let U := (ls.map Matrix.TransvectionStruct.toMatrix).prod
  let V := (rs.map Matrix.TransvectionStruct.toMatrix).prod
  have hu : U.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod ls
  have hv : V.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod rs
  have hum : (U.map f).det = 1 := by
    rw [← f.map_det, hu, map_one]
  have hvm : (V.map f).det = 1 := by
    rw [← f.map_det, hv, map_one]
  have he' : A = U * Matrix.diagonal d * V := he
  have hk : A.rank = (Matrix.diagonal d).rank := by
    rw [he', Matrix.rank_mul_eq_left_of_isUnit_det V _ (by rw [hv]; exact isUnit_one),
      Matrix.rank_mul_eq_right_of_isUnit_det U _ (by rw [hu]; exact isUnit_one)]
  have hl : (A.map f).rank = (Matrix.diagonal (fun i => f (d i))).rank := by
    rw [he', Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f),
      Matrix.rank_mul_eq_left_of_isUnit_det (V.map f) _ (by rw [hvm]; exact isUnit_one),
      Matrix.rank_mul_eq_right_of_isUnit_det (U.map f) _ (by rw [hum]; exact isUnit_one)]
  rw [hk, hl, Matrix.rank_diagonal, Matrix.rank_diagonal]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => by
    have h : f (d i) = 0 ↔ d i = 0 := by
      rw [← map_zero f]
      exact f.injective.eq_iff
    exact not_congr h)

/-- Rectangular rational matrices have the same rank over the reals. -/
theorem rational_matrix_rank {r c : Type*} [Fintype r] [Fintype c]
    (A : Matrix r c ℚ) : (A.map (Rat.castHom ℝ)).rank = A.rank := by
  classical
  calc
    (A.map (Rat.castHom ℝ)).rank =
        ((A.map (Rat.castHom ℝ)).transpose * A.map (Rat.castHom ℝ)).rank :=
      (Matrix.rank_transpose_mul_self _).symm
    _ = ((A.transpose * A).map (Rat.castHom ℝ)).rank := by
      rw [Matrix.map_mul, Matrix.transpose_map]
    _ = (A.transpose * A).rank := square_matrix_rank_map _ _
    _ = A.rank := Matrix.rank_transpose_mul_self A

theorem integer_matrix_rank {r c : Type*} [Fintype r] [Fintype c]
    (A : Matrix r c ℤ) :
    (A.map (Int.castRingHom ℝ)).rank = (A.map (Int.castRingHom ℚ)).rank := by
  have h := rational_matrix_rank (A.map (Int.castRingHom ℚ))
  have he : (A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) = A.map (Int.castRingHom ℝ) := by
    ext i j
    simp
  rw [he] at h
  exact h

end MOR34
