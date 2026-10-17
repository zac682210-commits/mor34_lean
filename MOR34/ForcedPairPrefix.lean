import MOR34.RestrictedPrefix

namespace MOR34

variable {s : ℕ}

def pairAllowed (u v : Fin s) : Finset (Fin s) := (Finset.univ.erase u).erase v

def forcedPairPrefix (u v : Fin s) (t : ℕ) : Finset (Fin s) :=
  insert v (restrictedPrefix (pairAllowed u v) (t - 1))

theorem pairAllowed_card (u v : Fin s) (huv : u ≠ v) :
    (pairAllowed u v).card = s - 2 := by
  have hv : v ∈ Finset.univ.erase u := by simp [huv.symm]
  simp [pairAllowed, Finset.card_erase_of_mem hv, Finset.card_erase_of_mem (Finset.mem_univ u)]

theorem forcedPairPrefix_pattern (u v : Fin s) (huv : u ≠ v) (t : ℕ) :
    u ∉ forcedPairPrefix u v t ∧ v ∈ forcedPairPrefix u v t := by
  constructor
  · intro hu
    rcases Finset.mem_insert.mp hu with he | hp
    · exact huv he
    · have hh := restrictedPrefix_subset (pairAllowed u v) (t - 1) hp
      simp [pairAllowed] at hh
  · exact Finset.mem_insert_self _ _

theorem forcedPairPrefix_card (u v : Fin s) (huv : u ≠ v) (t : ℕ)
    (ht : 1 ≤ t) (hb : t ≤ s - 1) : (forcedPairPrefix u v t).card = t := by
  have hs : 2 ≤ s := by
    have h1 := u.isLt
    have h2 := v.isLt
    have hn : u.val ≠ v.val := fun he => huv (Fin.ext he)
    omega
  have hk : t - 1 ≤ (pairAllowed u v).card := by rw [pairAllowed_card u v huv]; omega
  have hv : v ∉ restrictedPrefix (pairAllowed u v) (t - 1) := by
    intro h
    have hh := restrictedPrefix_subset (pairAllowed u v) (t - 1) h
    simp [pairAllowed] at hh
  rw [forcedPairPrefix, Finset.card_insert_of_not_mem hv, restrictedPrefix_card _ _ hk]
  omega

/-- Actual minimum-cost realization of a forced-out/forced-in pair at fixed count. -/
theorem forcedPairPrefix_minimal (u v : Fin s) (S : Finset (Fin s))
    (hu : u ∉ S) (hv : v ∈ S) (w : Fin s → ℤ) (hw : Monotone w) :
    (∑ i ∈ forcedPairPrefix u v S.card, w i) ≤ ∑ i ∈ S, w i := by
  have hsub : S.erase v ⊆ pairAllowed u v := by
    intro x hx
    have hmem := Finset.mem_erase.mp hx
    simp only [pairAllowed, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hmem.1, fun he => hu (he ▸ hmem.2)⟩
  have hc : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
  have hmin := restrictedPrefix_minimal (pairAllowed u v) (S.erase v) hsub w hw
  rw [hc] at hmin
  have hn : v ∉ restrictedPrefix (pairAllowed u v) (S.card - 1) := by
    intro h
    have hh := restrictedPrefix_subset (pairAllowed u v) (S.card - 1) h
    simp [pairAllowed] at hh
  have he : (∑ i ∈ S, w i) = w v + ∑ i ∈ S.erase v, w i := by
    conv_lhs => rw [← Finset.insert_erase hv]
    rw [Finset.sum_insert (Finset.not_mem_erase v S)]
  rw [forcedPairPrefix, Finset.sum_insert hn, he]
  omega

theorem forcedPairPrefix_cost (u v : Fin s) (t : ℕ) (w : Fin s → ℤ) :
    (∑ i ∈ forcedPairPrefix u v t, w i) = w v +
      prefixCost (fun i => w ((pairAllowed u v).orderEmbOfFin rfl i)) (t - 1) := by
  have hn : v ∉ restrictedPrefix (pairAllowed u v) (t - 1) := by
    intro h
    have hh := restrictedPrefix_subset (pairAllowed u v) (t - 1) h
    simp [pairAllowed] at hh
  rw [forcedPairPrefix, Finset.sum_insert hn, restrictedPrefix_cost]

end MOR34

namespace MOR34

/-- The constant condition handles the zero-size residual class. -/
theorem prefix_epigraph_all_sizes {s z : ℕ} (w : Fin s → ℤ) (hw : Monotone w)
    (hz : z ≤ s) (y : ℤ) : prefixCost w z ≤ y ↔
      (s = 0 → 0 ≤ y) ∧ ∀ t : Fin s, prefixLine w t (z : ℤ) ≤ y := by
  by_cases hs : s = 0
  · subst s
    have hz0 : z = 0 := by omega
    subst z
    simp [prefixCost, classPrefix]
  · have hs' : 0 < s := by omega
    rw [prefix_epigraph_iff w hw hs' hz y]
    simp [hs]

/-- Exact cost epigraph for the forced pair, including a two-item original class. -/
theorem forcedPairPrefix_epigraph {s : ℕ} (u v : Fin s) (huv : u ≠ v) (t : ℕ)
    (ht : 1 ≤ t) (hb : t ≤ s - 1) (w : Fin s → ℤ) (hw : Monotone w) (y : ℤ) :
    (∑ i ∈ forcedPairPrefix u v t, w i) ≤ y ↔
      ((pairAllowed u v).card = 0 → w v ≤ y) ∧
      ∀ a : Fin (pairAllowed u v).card,
        w v + prefixLine (fun i => w ((pairAllowed u v).orderEmbOfFin rfl i)) a ((t - 1 : ℕ) : ℤ) ≤ y := by
  have hs : 2 ≤ s := by
    have h1 := u.isLt
    have h2 := v.isLt
    have hn : u.val ≠ v.val := fun he => huv (Fin.ext he)
    omega
  have hk : t - 1 ≤ (pairAllowed u v).card := by rw [pairAllowed_card u v huv]; omega
  rw [forcedPairPrefix_cost]
  have he := prefix_epigraph_all_sizes
    (fun i => w ((pairAllowed u v).orderEmbOfFin rfl i))
    (hw.comp ((pairAllowed u v).orderEmbOfFin rfl).monotone) hk (y - w v)
  constructor
  · intro h
    obtain ⟨h0, ha⟩ := he.mp (by omega)
    exact ⟨fun hh => by have hi := h0 hh; omega, fun a => by have hi := ha a; omega⟩
  · rintro ⟨h0, ha⟩
    have h := he.mpr ⟨fun hh => by have hi := h0 hh; omega,
      fun a => by have hi := ha a; omega⟩
    omega

end MOR34
