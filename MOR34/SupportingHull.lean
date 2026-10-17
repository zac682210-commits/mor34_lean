import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

namespace MOR34
section SupportingHull
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A supporting linear bound is preserved under convex hull. -/
theorem linear_bound_convexHull (f : V →ₗ[ℝ] ℝ) (s : Set V) (b : ℝ)
    (hb : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  apply convexHull_min hb
  intro x hx y hy a c ha hc hac
  change f (a • x + c • y) ≤ b
  simp only [map_add, map_smul, smul_eq_mul]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hc (sub_nonneg.mpr hy)]

/-- Equality in a supporting bound uses only equality generators. -/
theorem supporting_hull_eq (f : V →ₗ[ℝ] ℝ) (s : Set V) (b : ℝ)
    (hb : ∀ x ∈ s, f x ≤ b) :
    {x ∈ convexHull ℝ s | f x = b} = convexHull ℝ {x ∈ s | f x = b} := by
  let t := convexHull ℝ {x ∈ s | f x = b}
  have hc : Convex ℝ {x : V | f x ≤ b ∧ (f x = b → x ∈ t)} := by
    intro x hx y hy a c ha hc hac
    change f (a • x + c • y) ≤ b ∧ (f (a • x + c • y) = b → a • x + c • y ∈ t)
    have he : f (a • x + c • y) = a * f x + c * f y := by simp
    refine ⟨?_, ?_⟩
    · rw [he]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1), mul_nonneg hc (sub_nonneg.mpr hy.1)]
    · intro hh
      by_cases ha0 : a = 0
      · have hc1 : c = 1 := by linarith
        simpa [ha0, hc1] using hy.2 (by simpa [he, ha0, hc1] using hh)
      by_cases hc0 : c = 0
      · have ha1 : a = 1 := by linarith
        simpa [hc0, ha1] using hx.2 (by simpa [he, hc0, ha1] using hh)
      have hfx : f x = b := by
        rw [he] at hh
        have hh' := mul_nonneg hc (sub_nonneg.mpr hy.1)
        nlinarith
      have hfy : f y = b := by
        rw [he, hfx] at hh
        nlinarith
      exact convex_convexHull ℝ _ (hx.2 hfx) (hy.2 hfy) ha hc hac
  have hsub : s ⊆ {x : V | f x ≤ b ∧ (f x = b → x ∈ t)} := by
    intro x hx
    exact ⟨hb x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  apply Set.Subset.antisymm
  · intro x hx
    exact (convexHull_min hsub hc hx.1).2 hx.2
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ _ hx.1, hx.2⟩
    · intro x hx y hy a c ha hc hac
      refine ⟨convex_convexHull ℝ s hx.1 hy.1 ha hc hac, ?_⟩
      change f (a • x + c • y) = b
      simp only [map_add, map_smul, smul_eq_mul, hx.2, hy.2]
      nlinarith

/-- A supporting equality level is an extreme subset in the standard segment sense. -/
theorem supporting_level_extreme (f : V →ₗ[ℝ] ℝ) (s : Set V) (b : ℝ)
    (hb : ∀ x ∈ s, f x ≤ b) : IsExtreme ℝ s {x ∈ s | f x = b} := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hzseg
  obtain ⟨a, c, ha, hc, hac, he⟩ := hzseg
  have heq : a * f x + c * f y = b := by
    have hh := congrArg f he
    simpa only [map_add, map_smul, smul_eq_mul, hz.2] using hh
  have hfx := hb x hx
  have hfy := hb y hy
  have hx' : f x = b := by
    nlinarith [mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hfy)]
  have hy' : f y = b := by nlinarith
  exact ⟨⟨hx, hx'⟩, hy, hy'⟩
end SupportingHull
end MOR34
