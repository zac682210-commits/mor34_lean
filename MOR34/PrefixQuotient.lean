import MOR34.TightDimension
import MOR34.PrefixMinimality

namespace MOR34

theorem sum_eq_of_cross_equal {α V : Type*} [DecidableEq α] [AddCommGroup V]
    (A B : Finset α) (f : α → V) (hc : A.card = B.card)
    (hf : ∀ a ∈ A \ B, ∀ b ∈ B \ A, f a = f b) :
    (∑ a ∈ A, f a) = ∑ b ∈ B, f b := by
  apply Finset.sum_sdiff_eq_sum_sdiff_iff.mp
  have hd := Finset.card_sdiff_comm hc
  by_cases ha : (A \ B).Nonempty
  · obtain ⟨a, ha⟩ := ha
    have hb : (B \ A).Nonempty := Finset.card_pos.mp (by rw [← hd]; exact Finset.card_pos.mpr ⟨a, ha⟩)
    obtain ⟨b, hb⟩ := hb
    calc
      (∑ i ∈ A \ B, f i) = ∑ _i ∈ A \ B, f a := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hf i hi b hb).trans (hf a ha b hb).symm
      _ = (A \ B).card • f a := by simp
      _ = (B \ A).card • f a := by rw [hd]
      _ = ∑ i ∈ B \ A, f i := by
        rw [← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro i hi
        exact hf a ha i hi
  · have he : A \ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have he' : B \ A = ∅ := Finset.card_eq_zero.mp (by rw [← hd, he]; rfl)
    simp [he, he']

variable {q : ℕ} {m : Fin q → ℕ}

theorem pointVector_sum_units (S : Finset (Item m)) :
    pointVector S = ∑ i ∈ S, unitVector i := by
  ext k
  simp [pointVector, unitVector, Finset.sum_apply]

theorem componentCountMap_pointVector (P : Model m) (S : Finset (Item m)) :
    componentCountMap P (pointVector S) = ∑ i ∈ S, unitVector (componentLabel P i) := by
  classical
  rw [pointVector_sum_units, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact fiberSumMap_unit (componentLabel P) i

theorem prefix_component_class_sum (P : Model m) {S : Finset (Item m)}
    (hS : Tight P S) (j : Fin q) :
    (∑ u ∈ classPrefix (m j) (counts S j), unitVector (componentLabel P ⟨j, u⟩)) =
      ∑ v ∈ classSlice S j, unitVector (componentLabel P ⟨j, v⟩) := by
  classical
  apply sum_eq_of_cross_equal
  · rw [card_classPrefix (counts_bounded S j), counts_classSlice]
  · intro u hu v hv
    obtain ⟨hu, hnu⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hv, hnv⟩ := Finset.mem_sdiff.mp hv
    have hu' := (mem_classPrefix u).mp hu
    have hv' : counts S j ≤ v.val := by
      have hn : ¬ v.val < counts S j := by simpa using hnv
      omega
    have hex : Exchange P j u v := by
      refine ⟨?_, S, hS, ?_, ?_⟩
      · change u.val < v.val
        omega
      · simpa using hnu
      · simpa using hv
    have he : componentLabel P (⟨j, u⟩ : Item m) = componentLabel P (⟨j, v⟩ : Item m) := by
      apply @Quotient.sound (Item m) (exchangeSetoid P)
      exact Relation.ReflTransGen.single ⟨j, u, v, rfl, rfl, Or.inl hex⟩
    exact congrArg unitVector he

/-- Tight points and their cheapest prefixes have identical component counts. -/
theorem componentCountMap_prefix (P : Model m) {S : Finset (Item m)} (hS : Tight P S) :
    componentCountMap P (pointVector (prefixSet (counts S))) =
      componentCountMap P (pointVector S) := by
  classical
  rw [componentCountMap_pointVector, componentCountMap_pointVector, prefixSet_assemble]
  change (∑ i ∈ Finset.univ.sigma (fun j => classPrefix (m j) (counts S j)),
      unitVector (componentLabel P i)) = _
  rw [Finset.sum_sigma]
  calc
    (∑ j, ∑ u ∈ classPrefix (m j) (counts S j), unitVector (componentLabel P ⟨j, u⟩)) =
        ∑ j, ∑ u ∈ classSlice S j, unitVector (componentLabel P ⟨j, u⟩) := by
      apply Finset.sum_congr rfl
      intro j _
      exact prefix_component_class_sum P hS j
    _ = ∑ i ∈ S, unitVector (componentLabel P i) := by
      have h := Finset.sum_sigma Finset.univ (classSlice S) (fun i => unitVector (componentLabel P i))
      change (∑ i ∈ assemble (classSlice S), unitVector (componentLabel P i)) = _ at h
      rw [assemble_classSlice] at h
      exact h.symm

/-- The set of tight prefix vectors, with actual feasibility retained. -/
def tightPrefixPointSet (P : Model m) : Set (Item m → ℝ) :=
  {x | ∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧ x = pointVector (prefixSet z)}

theorem tight_image_eq_prefix_image (P : Model m) (hWF : WellFormed P) :
    (componentCountMap P) '' tightPointSet P =
      (componentCountMap P) '' tightPrefixPointSet P := by
  ext y
  constructor
  · rintro ⟨x, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨pointVector (prefixSet (counts S)),
      ⟨counts S, counts_bounded S, prefix_tight P hWF hS, rfl⟩,
      componentCountMap_prefix P hS⟩
  · rintro ⟨x, ⟨z, hz, ht, rfl⟩, rfl⟩
    exact ⟨pointVector (prefixSet z), ⟨prefixSet z, ht, rfl⟩, rfl⟩

end MOR34
