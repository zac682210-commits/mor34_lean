import MOR34.PrefixEpigraph

namespace MOR34
section RestrictedPrefix
variable {α : Type*} [LinearOrder α]

/-- Encode a subset in the increasing enumeration of an allowed finite set. -/
def restrictionIndices (R S : Finset α) : Finset (Fin R.card) :=
  Finset.univ.filter fun i => R.orderEmbOfFin rfl i ∈ S

def restrictedPrefix (R : Finset α) (k : ℕ) : Finset α :=
  (classPrefix R.card k).map (R.orderEmbOfFin rfl).toEmbedding

theorem restrictionIndices_map (R S : Finset α) (hS : S ⊆ R) :
    (restrictionIndices R S).map (R.orderEmbOfFin rfl).toEmbedding = S := by
  ext x
  simp only [Finset.mem_map, restrictionIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    have hR := hS hx
    rw [← R.map_orderEmbOfFin_univ rfl] at hR
    obtain ⟨i, _, he⟩ := Finset.mem_map.mp hR
    exact ⟨i, he.symm ▸ hx, he⟩

theorem restrictionIndices_card (R S : Finset α) (hS : S ⊆ R) :
    (restrictionIndices R S).card = S.card := by
  have h := congrArg Finset.card (restrictionIndices_map R S hS)
  simpa only [Finset.card_map] using h

theorem restrictedPrefix_subset (R : Finset α) (k : ℕ) : restrictedPrefix R k ⊆ R := by
  calc
    restrictedPrefix R k ⊆ Finset.univ.map (R.orderEmbOfFin rfl).toEmbedding :=
      Finset.map_subset_map.mpr (Finset.subset_univ _)
    _ = R := R.map_orderEmbOfFin_univ rfl

theorem restrictedPrefix_card (R : Finset α) (k : ℕ) (hk : k ≤ R.card) :
    (restrictedPrefix R k).card = k := by
  rw [restrictedPrefix, Finset.card_map, card_classPrefix hk]

/-- Prefix minimality in an inherited order, including an empty allowed set. -/
theorem restrictedPrefix_minimal (R S : Finset α) (hS : S ⊆ R)
    (w : α → ℤ) (hw : Monotone w) :
    (∑ i ∈ restrictedPrefix R S.card, w i) ≤ ∑ i ∈ S, w i := by
  have h := classPrefix_minimal (restrictionIndices R S)
    (fun i => w (R.orderEmbOfFin rfl i)) (hw.comp (R.orderEmbOfFin rfl).monotone)
  rw [restrictionIndices_card R S hS] at h
  calc
    (∑ i ∈ restrictedPrefix R S.card, w i) =
        ∑ i ∈ classPrefix R.card S.card, w (R.orderEmbOfFin rfl i) := Finset.sum_map _ _ _
    _ ≤ ∑ i ∈ restrictionIndices R S, w (R.orderEmbOfFin rfl i) := h
    _ = ∑ i ∈ S, w i := by
      rw [← Finset.sum_map, restrictionIndices_map R S hS]

theorem restrictedPrefix_cost (R : Finset α) (k : ℕ) (w : α → ℤ) :
    (∑ i ∈ restrictedPrefix R k, w i) = prefixCost (fun i => w (R.orderEmbOfFin rfl i)) k := by
  rw [restrictedPrefix, Finset.sum_map]
  rfl

end RestrictedPrefix
end MOR34
