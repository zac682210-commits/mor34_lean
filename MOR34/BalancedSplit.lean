import MOR34.Targets
import Mathlib.Tactic

namespace MOR34

/-- Extend the prescribed positive pair inside the complement of the negative pair. -/
theorem balancedSplit : BalancedSplitGoal := by
  intro α _ D P N k hPD hND hPN hP hN hD hk
  have hPN' : ∀ ⦃x⦄, x ∈ P → x ∉ N := by
    intro x hx hn
    exact Finset.disjoint_left.mp hPN hx hn
  have hsub : P ⊆ D \ N := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hPD hx, hPN' hx⟩
  have hcard : k ≤ (D \ N).card := by
    rw [Finset.card_sdiff hND, hD, hN]
    omega
  obtain ⟨U, hPU, hU, hUk⟩ :=
    Finset.exists_subsuperset_card_eq hsub (by omega : P.card ≤ k) hcard
  have hUD : U ⊆ D := fun x hx => (Finset.mem_sdiff.mp (hU hx)).1
  refine ⟨U, D \ U, ?_, ?_, hUk, ?_, hPU, ?_⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact hUD hx
      · exact hx
    · intro hx
      by_cases hu : x ∈ U
      · exact Or.inl hu
      · exact Or.inr ⟨hx, hu⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hv
    exact (Finset.mem_sdiff.mp hv).2 hx
  · rw [Finset.card_sdiff hUD, hD, hUk]
    omega
  · intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨hND hx, ?_⟩
    intro hu
    exact (Finset.mem_sdiff.mp (hU hu)).2 hx

end MOR34
