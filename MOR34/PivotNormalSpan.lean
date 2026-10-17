import MOR34.BoundedPivotNormals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace MOR34

/-- Rational row map corresponding to the pivot block and its free columns. -/
def pivotRowMap {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) : (Fin r ⊕ Fin f → ℚ) →ₗ[ℚ] (Fin r → ℚ) :=
  (show Matrix (Fin r) (Fin r ⊕ Fin f) ℚ from
    fun i j => ((Sum.elim (A i) (C i) j : ℤ) : ℚ)).mulVecLin

theorem pivotNormal_mem_ker {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (k : Fin f) :
    (fun j => (pivotNormal A C k j : ℚ)) ∈ LinearMap.ker (pivotRowMap A C) := by
  rw [LinearMap.mem_ker]
  ext i
  change (∑ j, ((Sum.elim (A i) (C i) j : ℤ) : ℚ) * (pivotNormal A C k j : ℚ)) = 0
  exact_mod_cast pivotNormal_kernel A C k i

/-- Kernel vectors are determined by their free coordinates. -/
theorem pivot_kernel_free_injective {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (hd : A.det ≠ 0)
    (x y : Fin r ⊕ Fin f → ℚ)
    (hx : x ∈ LinearMap.ker (pivotRowMap A C)) (hy : y ∈ LinearMap.ker (pivotRowMap A C))
    (hfree : ∀ j, x (Sum.inr j) = y (Sum.inr j)) : x = y := by
  have hd' : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    have he : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) := by
      simpa using ((Int.castRingHom ℚ).map_det A).symm
    rw [he]
    exact_mod_cast hd
  have hinj : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd'))
  have hxy : (fun j => x (Sum.inl j)) = (fun j => y (Sum.inl j)) := by
    apply hinj
    ext i
    have hxi := congrFun (LinearMap.mem_ker.mp hx) i
    have hyi := congrFun (LinearMap.mem_ker.mp hy) i
    change (∑ j, ((Sum.elim (A i) (C i) j : ℤ) : ℚ) * x j) = 0 at hxi
    change (∑ j, ((Sum.elim (A i) (C i) j : ℤ) : ℚ) * y j) = 0 at hyi
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hfree] at hxi hyi
    change (∑ j, (A i j : ℚ) * x (Sum.inl j)) = ∑ j, (A i j : ℚ) * y (Sum.inl j)
    linarith
  funext j
  cases j with
  | inl j => exact congrFun hxy j
  | inr j => exact hfree j

/-- The bounded integer normals span the full rational kernel of the pivot row block. -/
theorem pivotNormals_span {r f : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (C : Matrix (Fin r) (Fin f) ℤ) (hd : A.det ≠ 0) :
    Submodule.span ℚ (Set.range (fun k => fun j => (pivotNormal A C k j : ℚ))) =
      LinearMap.ker (pivotRowMap A C) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact pivotNormal_mem_ker A C k
  · intro x hx
    let y : Fin r ⊕ Fin f → ℚ := ∑ k : Fin f,
      (x (Sum.inr k) / (A.det : ℚ)) • (fun j => (pivotNormal A C k j : ℚ))
    have hyspan : y ∈ Submodule.span ℚ (Set.range (fun k => fun j => (pivotNormal A C k j : ℚ))) := by
      apply Submodule.sum_mem
      intro k _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hyker : y ∈ LinearMap.ker (pivotRowMap A C) := by
      apply Submodule.sum_mem
      intro k _
      exact Submodule.smul_mem _ _ (pivotNormal_mem_ker A C k)
    have hd' : (A.det : ℚ) ≠ 0 := by exact_mod_cast hd
    have heq : x = y := by
      apply pivot_kernel_free_injective A C hd x y hx hyker
      intro j
      simp [y, pivotNormal, Finset.sum_apply, smul_eq_mul, Finset.sum_ite_eq, div_mul_cancel₀ _ hd']
    rwa [heq]
end MOR34
