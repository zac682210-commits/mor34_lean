import MOR34.PrefixMinimality

namespace MOR34

/-- Integer cost of a sorted prefix in one class. -/
def prefixCost {s : ℕ} (w : Fin s → ℤ) (z : ℕ) : ℤ :=
  ∑ u ∈ classPrefix s z, w u

/-- Supporting line with the zero-based breakpoint t. -/
def prefixLine {s : ℕ} (w : Fin s → ℤ) (t : Fin s) (z : ℤ) : ℤ :=
  prefixCost w t.val + w t * (z - (t.val : ℤ))

theorem prefixCost_shift {s z : ℕ} (w : Fin s → ℤ) (c : ℤ) (hz : z ≤ s) :
    (∑ u ∈ classPrefix s z, (w u - c)) = prefixCost w z - (z : ℤ) * c := by
  simp [prefixCost, Finset.sum_sub_distrib, card_classPrefix hz, nsmul_eq_mul]

/-- Sorting makes every prefix line a lower bound at every bounded count. -/
theorem prefixLine_le {s z : ℕ} (w : Fin s → ℤ) (hw : Monotone w)
    (hz : z ≤ s) (t : Fin s) : prefixLine w t (z : ℤ) ≤ prefixCost w z := by
  have hp : ∀ u : Fin s,
      (if u.val < t.val then w u - w t else 0) ≤
      (if u.val < z then w u - w t else 0) := by
    intro u
    by_cases hut : u.val < t.val <;> by_cases huz : u.val < z
    · simp [hut, huz]
    · have h := hw (show u ≤ t from Nat.le_of_lt hut)
      simp [hut, huz]; omega
    · have h := hw (show t ≤ u from Nat.le_of_not_gt hut)
      simp [hut, huz]; omega
    · simp [hut, huz]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hp u)
  have ht : t.val ≤ s := Nat.le_of_lt t.isLt
  rw [← Finset.sum_filter, ← Finset.sum_filter] at hs
  change (∑ u ∈ classPrefix s t.val, (w u - w t)) ≤
    ∑ u ∈ classPrefix s z, (w u - w t) at hs
  rw [prefixCost_shift w (w t) ht, prefixCost_shift w (w t) hz] at hs
  unfold prefixLine
  nlinarith

theorem prefixCost_succ {s : ℕ} (w : Fin s → ℤ) (t : Fin s) :
    prefixCost w (t.val + 1) = prefixCost w t.val + w t := by
  have he : classPrefix s (t.val + 1) = insert t (classPrefix s t.val) := by
    ext u
    simp only [mem_classPrefix, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : u = t
      · exact Or.inl he
      · right
        have hn : u.val ≠ t.val := fun h => he (Fin.ext h)
        omega
    · rintro (rfl | h) <;> omega
  have hn : t ∉ classPrefix s t.val := by simp
  unfold prefixCost
  rw [he, Finset.sum_insert hn]
  omega

/-- At the right endpoint the last supporting line is still attained. -/
theorem prefixLine_attained {s z : ℕ} (w : Fin s → ℤ) (hs : 0 < s)
    (hz : z ≤ s) : ∃ t : Fin s, prefixLine w t (z : ℤ) = prefixCost w z := by
  by_cases h : z < s
  · refine ⟨⟨z, h⟩, ?_⟩
    simp [prefixLine]
  · have hzs : z = s := by omega
    let t : Fin s := ⟨s - 1, by omega⟩
    have ht : t.val + 1 = z := by dsimp [t]; omega
    have hc := prefixCost_succ w t
    rw [ht] at hc
    have hcast : (z : ℤ) - (t.val : ℤ) = 1 := by omega
    refine ⟨t, ?_⟩
    simp only [prefixLine, hcast, mul_one]
    exact hc.symm

theorem prefix_epigraph_iff {s z : ℕ} (w : Fin s → ℤ) (hw : Monotone w)
    (hs : 0 < s) (hz : z ≤ s) (y : ℤ) :
    prefixCost w z ≤ y ↔ ∀ t : Fin s, prefixLine w t (z : ℤ) ≤ y := by
  constructor
  · intro h t
    exact le_trans (prefixLine_le w hw hz t) h
  · intro h
    obtain ⟨t, ht⟩ := prefixLine_attained w hs hz
    rw [← ht]
    exact h t

variable {q : ℕ} {m : Fin q → ℕ}

theorem weightSum_prefixCost (P : Model m) (z : Counts q) :
    weightSum P (prefixSet z) = ∑ j, prefixCost (fun u => P.weight ⟨j, u⟩) (z j) := by
  unfold weightSum
  rw [prefixSet_assemble, sum_assemble]
  rfl

/-- Exact integer epigraph feasibility in q count and q cost variables. -/
theorem prefix_feasible_epigraph (P : Model m) (hWF : WellFormed P)
    (z : Counts q) (hz : BoundedCounts (m := m) z) :
    Feasible P (prefixSet z) ↔ ∃ y : Fin q → ℤ,
      (∀ j (t : Fin (m j)), prefixLine (fun u => P.weight ⟨j, u⟩) t (z j : ℤ) ≤ y j) ∧
      (∑ j, y j) ≤ P.capacity := by
  rcases hWF with ⟨_, hm, _, _, _, _, _, hw⟩
  change weightSum P (prefixSet z) ≤ P.capacity ↔ _
  rw [weightSum_prefixCost]
  constructor
  · intro h
    refine ⟨fun j => prefixCost (fun u => P.weight ⟨j, u⟩) (z j), ?_, h⟩
    intro j t
    exact prefixLine_le _ (hw j) (hz j) t
  · rintro ⟨y, hy, hb⟩
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro j _
    exact (prefix_epigraph_iff _ (hw j) (hm j) (hz j) (y j)).mpr (hy j)

end MOR34
