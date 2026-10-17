import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

namespace MOR34
section SupportingHull
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Positive coefficients cannot hide slack in a supporting inequality. -/
theorem weighted_support_equality {a c x y b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hac : a + c = 1)
    (hx : x ≤ b) (hy : y ≤ b) (he : a * x + c * y = b) : x = b ∧ y = b := by
  have hax : 0 ≤ a * (b - x) := mul_nonneg ha.le (sub_nonneg.mpr hx)
  have hcy : 0 ≤ c * (b - y) := mul_nonneg hc.le (sub_nonneg.mpr hy)
  have hsum : a * (b - x) + c * (b - y) = 0 := by
    calc
      _ = (a + c) * b - (a * x + c * y) := by ring
      _ = 0 := by rw [hac, he]; ring
  have hax0 : a * (b - x) = 0 := by linarith
  have hcy0 : c * (b - y) = 0 := by linarith
  have hx0 := (mul_eq_zero.mp hax0).resolve_left (ne_of_gt ha)
  have hy0 := (mul_eq_zero.mp hcy0).resolve_left (ne_of_gt hc)
  constructor <;> linarith

/-- A supporting linear bound is preserved under convex hull. -/
theorem linear_bound_convexHull (f : V →ₗ[ℝ] ℝ) (s : Set V) (b : ℝ)
    (hb : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  apply convexHull_min hb
  intro x hx y hy a c ha hc hac
  change f (a • x + c • y) ≤ b
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    _ ≤ a * b + c * b := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hc)
    _ = b := by rw [← add_mul, hac, one_mul]

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
      calc
        _ ≤ a * b + c * b := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
          (mul_le_mul_of_nonneg_left hy.1 hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    · intro hh
      by_cases ha0 : a = 0
      · have hc1 : c = 1 := by linarith
        simpa [ha0, hc1] using hy.2 (by simpa [he, ha0, hc1] using hh)
      by_cases hc0 : c = 0
      · have ha1 : a = 1 := by linarith
        simpa [hc0, ha1] using hx.2 (by simpa [he, hc0, ha1] using hh)
      obtain ⟨hfx, hfy⟩ := weighted_support_equality
        (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hc (Ne.symm hc0)) hac hx.1 hy.1
        (by rwa [he] at hh)
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
      rw [← add_mul, hac, one_mul]

/-- A supporting equality level is an extreme subset in the standard segment sense. -/
theorem supporting_level_extreme (f : V →ₗ[ℝ] ℝ) (s : Set V) (b : ℝ)
    (hb : ∀ x ∈ s, f x ≤ b) : IsExtreme ℝ s {x ∈ s | f x = b} := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hzseg
  obtain ⟨a, c, ha, hc, hac, he⟩ := hzseg
  have heq : a * f x + c * f y = b := by
    have hh := congrArg f he
    simpa only [map_add, map_smul, smul_eq_mul, hz.2] using hh
  obtain ⟨hx', hy'⟩ := weighted_support_equality ha hc hac (hb x hx) (hb y hy) heq
  exact ⟨⟨hx, hx'⟩, hy, hy'⟩
end SupportingHull
end MOR34
