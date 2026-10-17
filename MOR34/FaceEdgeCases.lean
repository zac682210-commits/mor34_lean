import MOR34.FacetBridge

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The geometric definition forces a proper face, not the whole polytope. -/
theorem codimensionOneFace_ne {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A F : Set V} (h : IsCodimensionOneFace A F) : F ≠ A := by
  intro he
  have hd := h.2.2.2
  rw [he] at hd
  omega

/-- All tight generators stay on the supporting affine hyperplane. -/
theorem tightPointSet_candidate (P : Model m) :
    ∀ x ∈ tightPointSet P, candidateLinear P x = (P.rhs : ℝ) := by
  rintro x ⟨t, ht, rfl⟩
  rw [candidateLinear_point, ht.2]

theorem zero_candidate_all_tight (P : Model m)
    (hc : ∀ j, P.coefficient j = 0) (hb : P.rhs = 0) :
    tightPointSet P = feasiblePointSet P := by
  ext x
  constructor
  · rintro ⟨t, ht, he⟩; exact ⟨t, ht.1, he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ⟨ht, by simp [candidateValue, hc, hb]⟩, he⟩

theorem zero_candidate_valid (P : Model m)
    (hc : ∀ j, P.coefficient j = 0) (hb : P.rhs = 0) : Valid P := by
  intro t _
  simp [candidateValue, hc, hb]

theorem zero_candidate_not_facet (P : Model m)
    (hc : ∀ j, P.coefficient j = 0) (hb : P.rhs = 0) :
    ¬ IsCodimensionOneFace (knapsackPolytope P) (candidateFace P) := by
  intro hf
  apply codimensionOneFace_ne hf
  rw [candidateFace_eq_hull P (zero_candidate_valid P hc hb), zero_candidate_all_tight P hc hb]
  rfl

theorem valid_empty_not_facet (P : Model m) (hv : Valid P)
    (ht : tightPointSet P = ∅) :
    ¬ IsCodimensionOneFace (knapsackPolytope P) (candidateFace P) := by
  intro hf
  have hn := (candidateFace_nonempty_iff P hv).mp hf.1
  rw [ht] at hn
  exact Set.not_nonempty_empty hn
end MOR34
