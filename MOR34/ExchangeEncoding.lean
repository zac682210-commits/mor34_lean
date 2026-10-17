import MOR34.ForcedPairPrefix

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Original-class witnesses: one forced pair, ordinary prefixes elsewhere. -/
def forcedFamily (j : Fin q) (u v : Fin (m j)) (z : Counts q) :
    (k : Fin q) → Finset (Fin (m k)) :=
  Function.update (fun k => classPrefix (m k) (z k)) j (forcedPairPrefix u v (z j))

def forcedSet (j : Fin q) (u v : Fin (m j)) (z : Counts q) : Finset (Item m) :=
  assemble (forcedFamily j u v z)

theorem forcedSet_pattern (j : Fin q) (u v : Fin (m j)) (huv : u ≠ v) (z : Counts q) :
    (⟨j, u⟩ : Item m) ∉ forcedSet j u v z ∧ (⟨j, v⟩ : Item m) ∈ forcedSet j u v z := by
  simpa [forcedSet, forcedFamily] using forcedPairPrefix_pattern u v huv (z j)

theorem counts_forcedSet (j : Fin q) (u v : Fin (m j)) (huv : u ≠ v) (z : Counts q)
    (hz : BoundedCounts (m := m) z) (hl : 1 ≤ z j) (hu : z j ≤ m j - 1) :
    counts (forcedSet j u v z) = z := by
  funext k
  rw [forcedSet, counts_assemble]
  by_cases hk : k = j
  · subst k
    simpa [forcedFamily] using forcedPairPrefix_card u v huv (z j) hl hu
  · simpa [forcedFamily, hk] using card_classPrefix (hz k)

theorem forced_count_bounds (j : Fin q) (u v : Fin (m j)) (S : Finset (Item m))
    (hu : (⟨j, u⟩ : Item m) ∉ S) (hv : (⟨j, v⟩ : Item m) ∈ S) :
    1 ≤ counts S j ∧ counts S j ≤ m j - 1 := by
  rw [counts_classSlice]
  have hp : 0 < (classSlice S j).card := Finset.card_pos.mpr ⟨v, mem_classSlice S j v |>.mpr hv⟩
  have hsub : classSlice S j ⊆ Finset.univ.erase u := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst x
    exact hu ((mem_classSlice S j u).mp hx)
  have hb := Finset.card_le_card hsub
  have he : (Finset.univ.erase u).card = m j - 1 := by simp
  rw [he] at hb
  omega

/-- The global forced witness preserves counts and never increases cost. -/
theorem forcedSet_minimal (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (S : Finset (Item m))
    (hu : (⟨j, u⟩ : Item m) ∉ S) (hv : (⟨j, v⟩ : Item m) ∈ S) :
    weightSum P (forcedSet j u v (counts S)) ≤ weightSum P S := by
  change (∑ i ∈ assemble (forcedFamily j u v (counts S)), P.weight i) ≤ _
  rw [sum_assemble]
  calc
    _ ≤ ∑ k, ∑ x ∈ classSlice S k, P.weight ⟨k, x⟩ := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k = j
      · subst k
        simp only [forcedFamily, Function.update_same, counts_classSlice]
        exact forcedPairPrefix_minimal u v (classSlice S j)
          (by simpa using hu) (by simpa using hv) _ (hWF.2.2.2.2.2.2.2 j)
      · simp only [forcedFamily, Function.update_noteq hk, counts_classSlice]
        exact classPrefix_minimal (classSlice S k) _ (hWF.2.2.2.2.2.2.2 k)
    _ = weightSum P S := by rw [← sum_assemble, assemble_classSlice]; rfl

/-- Exact reduction of the original exchange predicate to cheapest count witnesses. -/
theorem exchange_iff_forced_counts (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) :
    Exchange P j u v ↔ u < v ∧ ∃ z : Counts q,
      BoundedCounts (m := m) z ∧ 1 ≤ z j ∧ z j ≤ m j - 1 ∧
      weightSum P (forcedSet j u v z) ≤ P.capacity ∧
      (∑ k, (z k : ℤ) * P.coefficient k) = P.rhs := by
  constructor
  · rintro ⟨huv, S, ht, hu, hv⟩
    have hb := forced_count_bounds j u v S hu hv
    refine ⟨huv, counts S, counts_bounded S, hb.1, hb.2,
      le_trans (forcedSet_minimal P hWF j u v S hu hv) ht.1, ?_⟩
    simpa only [candidateValue_counts] using ht.2
  · rintro ⟨huv, z, hz, hl, hu, hw, he⟩
    have hc := counts_forcedSet j u v (ne_of_lt huv) z hz hl hu
    have hp := forcedSet_pattern j u v (ne_of_lt huv) z
    refine ⟨huv, forcedSet j u v z, ⟨hw, ?_⟩, hp.1, hp.2⟩
    rw [candidateValue_counts, hc]
    exact he

end MOR34
