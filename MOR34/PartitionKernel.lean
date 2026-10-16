import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace MOR34

section PartitionKernel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A real coordinate unit vector. -/
def unitVector (i : α) : α → ℝ := fun k => if k = i then 1 else 0

/-- The linear map that sums coordinates in each labelled group. -/
def fiberSumMap (f : α → β) : (α → ℝ) →ₗ[ℝ] (β → ℝ) where
  toFun x b := ∑ i ∈ Finset.univ.filter (fun i => f i = b), x i
  map_add' x y := by ext b; simp [Finset.sum_add_distrib]
  map_smul' c x := by ext b; simp [Finset.mul_sum]

/-- All differences of unit vectors belonging to the same group. -/
def fiberDifferenceSpan (f : α → β) : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ {v | ∃ i j : α, f i = f j ∧ v = unitVector i - unitVector j}

theorem fiberSumMap_unit (f : α → β) (i : α) :
    fiberSumMap f (unitVector i) = unitVector (f i) := by
  ext b
  simp [fiberSumMap, unitVector, eq_comm]

theorem unitVector_expansion (x : α → ℝ) :
    (∑ i : α, x i • unitVector i) = x := by
  ext k
  simp [unitVector, Finset.sum_apply]

theorem fiberDifferenceSpan_le_ker (f : α → β) :
    fiberDifferenceSpan f ≤ LinearMap.ker (fiberSumMap f) := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, j, hij, rfl⟩
  rw [LinearMap.mem_ker, map_sub, fiberSumMap_unit, fiberSumMap_unit, hij, sub_self]

/-- Regrouping by labels annihilates the anchored part of a kernel vector. -/
theorem anchor_sum_zero (f : α → β) (g : β → α) (x : α → ℝ)
    (hx : fiberSumMap f x = 0) :
    (∑ i : α, x i • unitVector (g (f i))) = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun i => x i • unitVector (g (f i)))]
  apply Finset.sum_eq_zero
  intro b _
  have he : (∑ i ∈ Finset.univ.filter (fun i => f i = b), x i • unitVector (g (f i))) =
      (∑ i ∈ Finset.univ.filter (fun i => f i = b), x i) • unitVector (g b) := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [he]
  have hb : (∑ i ∈ Finset.univ.filter (fun i => f i = b), x i) = 0 := congrFun hx b
  rw [hb, zero_smul]

/-- A right inverse supplies one anchor in every group. -/
theorem fiberDifferenceSpan_eq_ker_of_section (f : α → β) (g : β → α)
    (hg : Function.RightInverse g f) :
    fiberDifferenceSpan f = LinearMap.ker (fiberSumMap f) := by
  apply le_antisymm (fiberDifferenceSpan_le_ker f)
  intro x hx
  have hs : (∑ i : α, x i • (unitVector i - unitVector (g (f i)))) ∈ fiberDifferenceSpan f := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, g (f i), (hg (f i)).symm, rfl⟩
  have he : (∑ i : α, x i • (unitVector i - unitVector (g (f i)))) = x := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, unitVector_expansion,
      anchor_sum_zero f g x (LinearMap.mem_ker.mp hx), sub_zero]
  simpa only [he] using hs

theorem fiberDifferenceSpan_eq_ker (f : α → β) (hf : Function.Surjective f) :
    fiberDifferenceSpan f = LinearMap.ker (fiberSumMap f) := by
  classical
  choose g hg using hf
  exact fiberDifferenceSpan_eq_ker_of_section f g hg

end PartitionKernel
end MOR34
