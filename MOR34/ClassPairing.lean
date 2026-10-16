import MOR34.PrefixTools

namespace MOR34

def ClassPairSpec (m a b : ℕ) (U V : Finset (Fin m)) : Prop :=
  (∀ i, indicator U i + indicator V i =
    indicator (classPrefix m a) i + indicator (classPrefix m b) i) ∧
  U.card = V.card ∧ U.card + V.card = a + b

def ClassCross {m : ℕ} (r : ℕ) (S : Finset (Fin m)) : Prop :=
  ∃ u v : Fin m, u.val < r ∧ r ≤ v.val ∧ u ∉ S ∧ v ∈ S

theorem classPairSpec_comm {m a b : ℕ} {U V : Finset (Fin m)}
    (h : ClassPairSpec m a b U V) : ClassPairSpec m b a U V := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro i
    rw [h.1 i, add_comm]
  · rw [h.2.2, add_comm]

theorem ordered_pair_prescribed {m a b : ℕ} (hab : a ≤ b) (hb : b ≤ m)
    (hpar : a % 2 = b % 2) (P N : Finset (Fin m))
    (hPD : P ⊆ classPrefix m b \ classPrefix m a)
    (hND : N ⊆ classPrefix m b \ classPrefix m a)
    (hPN : Disjoint P N)
    (hP : P.card ≤ (b - a) / 2) (hN : N.card ≤ (b - a) / 2) :
    ∃ U V : Finset (Fin m), ClassPairSpec m a b U V ∧
      P ⊆ U ∧ N ⊆ V ∧ Disjoint U N ∧ Disjoint V P := by
  let C := classPrefix m a
  let H := classPrefix m b
  let D := H \ C
  have hCH : C ⊆ H := classPrefix_mono hab
  have hCcard : C.card = a := card_classPrefix (hab.trans hb)
  have hDcard : D.card = 2 * ((b - a) / 2) := by
    dsimp [D, H, C]
    rw [Finset.card_sdiff (classPrefix_mono hab), card_classPrefix hb,
      card_classPrefix (hab.trans hb)]
    omega
  obtain ⟨u, v, huv, hdis, hucard, hvcard, hPu, hNv⟩ :=
    split_prescribed D P N ((b - a) / 2) hPD hND hPN hP hN hDcard
  have huD : u ⊆ D := by
    intro i hi
    rw [← huv]
    exact Finset.mem_union_left _ hi
  have hvD : v ⊆ D := by
    intro i hi
    rw [← huv]
    exact Finset.mem_union_right _ hi
  have hCu : Disjoint C u := by
    apply Finset.disjoint_left.mpr
    intro i hc hu
    exact (Finset.mem_sdiff.mp (huD hu)).2 hc
  have hCv : Disjoint C v := by
    apply Finset.disjoint_left.mpr
    intro i hc hv
    exact (Finset.mem_sdiff.mp (hvD hv)).2 hc
  refine ⟨C ∪ u, C ∪ v, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      have hcHi : i ∈ C → i ∈ H := fun hi => hCH hi
      have hcover : (i ∈ u ∨ i ∈ v) ↔ (i ∈ H ∧ i ∉ C) := by
        rw [← Finset.mem_union, huv]
        simp only [D, Finset.mem_sdiff]
      have hn : ¬ (i ∈ u ∧ i ∈ v) := by
        rintro ⟨hu, hv⟩
        exact Finset.disjoint_left.mp hdis hu hv
      change indicator (C ∪ u) i + indicator (C ∪ v) i = indicator C i + indicator H i
      by_cases hc : i ∈ C <;> by_cases hh : i ∈ H <;>
        by_cases hu : i ∈ u <;> by_cases hv : i ∈ v <;>
        simp_all [indicator]
    · rw [Finset.card_union_of_disjoint hCu, Finset.card_union_of_disjoint hCv,
        hucard, hvcard]
    · rw [Finset.card_union_of_disjoint hCu, Finset.card_union_of_disjoint hCv,
        hCcard, hucard, hvcard]
      omega
  · exact fun i hi => Finset.mem_union_right _ (hPu hi)
  · exact fun i hi => Finset.mem_union_right _ (hNv hi)
  · apply Finset.disjoint_left.mpr
    intro i hi hn
    rcases Finset.mem_union.mp hi with hc | hu
    · exact (Finset.mem_sdiff.mp (hND hn)).2 hc
    · exact Finset.disjoint_left.mp hdis hu (hNv hn)
  · apply Finset.disjoint_left.mpr
    intro i hi hp
    rcases Finset.mem_union.mp hi with hc | hv
    · exact (Finset.mem_sdiff.mp (hPD hp)).2 hc
    · exact Finset.disjoint_left.mp hdis (hPu hp) hv

theorem class_pair {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m)
    (hpar : a % 2 = b % 2) :
    ∃ U V : Finset (Fin m), ClassPairSpec m a b U V := by
  by_cases hab : a ≤ b
  · obtain ⟨U, V, h, _⟩ := ordered_pair_prescribed hab hb hpar ∅ ∅
      (Finset.empty_subset _) (Finset.empty_subset _) (by simp) (by simp) (by simp)
    exact ⟨U, V, h⟩
  · have hba : b ≤ a := by omega
    obtain ⟨U, V, h, _⟩ := ordered_pair_prescribed hba ha hpar.symm ∅ ∅
      (Finset.empty_subset _) (Finset.empty_subset _) (by simp) (by simp) (by simp)
    exact ⟨U, V, classPairSpec_comm h⟩

theorem class_pair_cross {m a b r : ℕ} (hb : b ≤ m)
    (hpar : a % 2 = b % 2) (har : a + 2 ≤ r) (hrb : r + 2 ≤ b) :
    ∃ U V : Finset (Fin m), ClassPairSpec m a b U V ∧
      ClassCross r U ∧ ClassCross r V := by
  let l0 : Fin m := ⟨a, by omega⟩
  let l1 : Fin m := ⟨a + 1, by omega⟩
  let r0 : Fin m := ⟨r, by omega⟩
  let r1 : Fin m := ⟨r + 1, by omega⟩
  let P : Finset (Fin m) := {l0, r0}
  let N : Finset (Fin m) := {l1, r1}
  have hPD : P ⊆ classPrefix m b \ classPrefix m a := by
    intro i hi
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi <;> subst i <;>
      simp only [Finset.mem_sdiff, mem_classPrefix] <;> dsimp [l0, r0] <;> omega
  have hND : N ⊆ classPrefix m b \ classPrefix m a := by
    intro i hi
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi <;> subst i <;>
      simp only [Finset.mem_sdiff, mem_classPrefix] <;> dsimp [l1, r1] <;> omega
  have hPN : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hi hn
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hi with hi | hi <;> rcases hn with hn | hn <;>
      have heq := congrArg Fin.val (hi.symm.trans hn) <;>
      dsimp [l0, l1, r0, r1] at heq <;> omega
  have hpne : l0 ≠ r0 := by
    intro h
    have heq := congrArg Fin.val h
    dsimp [l0, r0] at heq
    omega
  have hnne : l1 ≠ r1 := by
    intro h
    have heq := congrArg Fin.val h
    dsimp [l1, r1] at heq
    omega
  have hpCard : P.card = 2 := by simp [P, hpne]
  have hnCard : N.card = 2 := by simp [N, hnne]
  have hk : 2 ≤ (b - a) / 2 := by omega
  obtain ⟨U, V, hspec, hPU, hNV, hUN, hVP⟩ :=
    ordered_pair_prescribed (by omega) hb hpar P N hPD hND hPN
      (by omega) (by omega)
  refine ⟨U, V, hspec, ?_, ?_⟩
  · refine ⟨l1, r0, ?_, ?_, ?_, ?_⟩
    · dsimp [l1]; omega
    · exact le_rfl
    · intro hi
      exact Finset.disjoint_left.mp hUN hi (by simp [N])
    · exact hPU (by simp [P])
  · refine ⟨l0, r1, ?_, ?_, ?_, ?_⟩
    · dsimp [l0]; omega
    · dsimp [r1]; omega
    · intro hi
      exact Finset.disjoint_left.mp hVP hi (by simp [P])
    · exact hNV (by simp [N])

end MOR34
