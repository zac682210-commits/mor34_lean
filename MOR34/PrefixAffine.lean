import MOR34.PrefixQuotient

namespace MOR34

section AffineSums
variable {q : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

def countReal (z : Counts q) : Fin q → ℝ := fun j => z j

def slopeMap (s : Fin q → V) : (Fin q → ℝ) →ₗ[ℝ] V where
  toFun x := ∑ j, x j • s j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

noncomputable def affineBoxMap (base : V) (low : Counts q) (s : Fin q → V) : (Fin q → ℝ) →ᵃ[ℝ] V where
  toFun x := base + ∑ j, (x j - (low j : ℝ)) • s j
  linear := slopeMap s
  map_vadd' p v := by
    change base + (∑ j, (v j + p j - (low j : ℝ)) • s j) =
      (∑ j, v j • s j) + (base + ∑ j, (p j - (low j : ℝ)) • s j)
    simp_rw [add_sub_assoc, add_smul]
    rw [Finset.sum_add_distrib]
    abel

theorem prefix_sum_increment {n l z : ℕ} (hlz : l ≤ z) (hz : z ≤ n)
    (f : Fin n → V) (s : V) (hs : ∀ i : Fin n, l ≤ i.val → i.val < z → f i = s) :
    (∑ i ∈ classPrefix n z, f i) = (∑ i ∈ classPrefix n l, f i) + ((z : ℝ) - l) • s := by
  have hsub := classPrefix_mono (m := n) hlz
  have hsum := Finset.sum_sdiff (f := f) hsub
  have hc : (classPrefix n z \ classPrefix n l).card = z - l := by
    rw [Finset.card_sdiff hsub, card_classPrefix hz, card_classPrefix (le_trans hlz hz)]
  have hd : (∑ i ∈ classPrefix n z \ classPrefix n l, f i) = (z - l) • s := by
    calc
      _ = ∑ _i ∈ classPrefix n z \ classPrefix n l, s := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hiz, hil⟩ := Finset.mem_sdiff.mp hi
        apply hs i
        · have : ¬ i.val < l := by simpa using hil
          omega
        · simpa using hiz
      _ = _ := by simp [hc]
  rw [hd] at hsum
  have hcast : ((z - l : ℕ) : ℝ) = (z : ℝ) - l := Nat.cast_sub hlz
  rw [← hcast, Nat.cast_smul_eq_nsmul]
  exact hsum.symm.trans (add_comm _ _)
end AffineSums

variable {q : ℕ} {m : Fin q → ℕ}

theorem component_prefix_sum (P : Model m) (z : Counts q) :
    componentCountMap P (pointVector (prefixSet z)) =
      ∑ j, ∑ u ∈ classPrefix (m j) (z j), unitVector (componentLabel P ⟨j, u⟩) := by
  classical
  rw [componentCountMap_pointVector, prefixSet_assemble]
  exact Finset.sum_sigma _ _ _

/-- Generic box affinity; the label constancy premise must be derived for actual cells. -/
theorem prefix_affine_on_box (P : Model m) (low high : Counts q)
    (s : Fin q → (ExchangeComponent P → ℝ))
    (hs : ∀ j (u : Fin (m j)), low j ≤ u.val → u.val < high j →
      unitVector (componentLabel P ⟨j, u⟩) = s j)
    (z : Counts q) (hz : BoundedCounts (m := m) z)
    (hlz : ∀ j, low j ≤ z j) (hzh : ∀ j, z j ≤ high j) :
    affineBoxMap (componentCountMap P (pointVector (prefixSet low))) low s (countReal z) =
      componentCountMap P (pointVector (prefixSet z)) := by
  classical
  change componentCountMap P (pointVector (prefixSet low)) +
    (∑ j, ((z j : ℝ) - low j) • s j) = _
  rw [component_prefix_sum, component_prefix_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact (prefix_sum_increment (hlz j) (hz j) _ (s j)
    (fun u hlu huz => hs j u hlu (lt_of_lt_of_le huz (hzh j)))).symm

end MOR34
