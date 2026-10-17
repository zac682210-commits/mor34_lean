import MOR34.CountEncoding

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Validity can be tested on cheapest count realizations without assuming it in Tight. -/
theorem valid_iff_count_prefixes (P : Model m) (hWF : WellFormed P) :
    Valid P ↔ ∀ z : Counts q, BoundedCounts (m := m) z →
      Feasible P (prefixSet z) → (∑ j, P.coefficient j * (z j : ℤ)) ≤ P.rhs := by
  constructor
  · intro hv z hz hf
    have h := hv (prefixSet z) hf
    rw [candidateValue_counts, counts_prefixSet z hz] at h
    simpa only [mul_comm] using h
  · intro h S hS
    have hz := counts_bounded S
    have hf : Feasible P (prefixSet (counts S)) := le_trans (prefixMinimality P hWF S) hS
    have hh := h (counts S) hz hf
    rw [candidateValue_counts]
    simpa only [mul_comm] using hh

theorem invalid_iff_count_violation (P : Model m) (hWF : WellFormed P) :
    ¬ Valid P ↔ ∃ z : Counts q, BoundedCounts (m := m) z ∧
      Feasible P (prefixSet z) ∧ P.rhs + 1 ≤ ∑ j, P.coefficient j * (z j : ℤ) := by
  rw [valid_iff_count_prefixes P hWF]
  push_neg
  constructor
  · rintro ⟨z, hb, hf, hv⟩
    exact ⟨z, hb, hf, by omega⟩
  · rintro ⟨z, hb, hf, hv⟩
    exact ⟨z, hb, hf, by omega⟩

theorem support_iff_tight_prefix (P : Model m) (hWF : WellFormed P) :
    (∃ S : Finset (Item m), Tight P S) ↔
      ∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
  constructor
  · rintro ⟨S, hs⟩
    exact ⟨counts S, counts_bounded S, prefix_tight P hWF hs⟩
  · rintro ⟨z, _, hz⟩
    exact ⟨prefixSet z, hz⟩

theorem support_iff_count_epigraph (P : Model m) (hWF : WellFormed P) :
    (∃ S : Finset (Item m), Tight P S) ↔ ∃ z y : Fin q → ℤ, CountEpigraph P z y := by
  rw [support_iff_tight_prefix P hWF]
  have h := restricted_count_epigraph P hWF (fun _ => True)
  simpa only [and_true] using h

end MOR34
