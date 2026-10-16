import MOR34.BalancedSplit
import Mathlib.Tactic

namespace MOR34

def classPrefix (m a : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.val < a

@[simp] theorem mem_classPrefix {m a : ℕ} (i : Fin m) :
    i ∈ classPrefix m a ↔ i.val < a := by
  simp [classPrefix]

theorem card_classPrefix {m a : ℕ} (ha : a ≤ m) :
    (classPrefix m a).card = a := by
  by_cases h : a < m
  · have heq : classPrefix m a = Finset.Iio (⟨a, h⟩ : Fin m) := by
      ext i
      simp [classPrefix, Fin.lt_def]
    rw [heq, Fin.card_Iio]
  · have heq : a = m := by omega
    subst a
    have hp : classPrefix m m = Finset.univ := by
      ext i
      simp [classPrefix, i.isLt]
    simp [hp]

theorem classPrefix_mono {m a b : ℕ} (hab : a ≤ b) :
    classPrefix m a ⊆ classPrefix m b := by
  intro i hi
  simp only [mem_classPrefix] at hi ⊢
  omega

def assemble {q : ℕ} {m : Fin q → ℕ}
    (F : (j : Fin q) → Finset (Fin (m j))) : Finset (Item m) :=
  Finset.univ.sigma F

@[simp] theorem mem_assemble {q : ℕ} {m : Fin q → ℕ}
    (F : (j : Fin q) → Finset (Fin (m j))) (i : Item m) :
    i ∈ assemble F ↔ i.2 ∈ F i.1 := by
  simp [assemble]

theorem counts_assemble {q : ℕ} {m : Fin q → ℕ}
    (F : (j : Fin q) → Finset (Fin (m j))) (j : Fin q) :
    counts (assemble F) j = (F j).card := by
  unfold counts assemble
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_sigma]
  simp [apply_ite]

theorem prefixSet_assemble {q : ℕ} {m : Fin q → ℕ} (z : Counts q) :
    prefixSet (m := m) z = assemble (fun j => classPrefix (m j) (z j)) := by
  ext i
  simp [prefixSet]

theorem split_prescribed {α : Type*} [DecidableEq α]
    (D P N : Finset α) (k : ℕ)
    (hPD : P ⊆ D) (hND : N ⊆ D) (hPN : Disjoint P N)
    (hP : P.card ≤ k) (hN : N.card ≤ k) (hD : D.card = 2 * k) :
    ∃ U V : Finset α, U ∪ V = D ∧ Disjoint U V ∧
      U.card = k ∧ V.card = k ∧ P ⊆ U ∧ N ⊆ V := by
  have hsub : P ⊆ D \ N := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hPD hx, fun hn => Finset.disjoint_left.mp hPN hx hn⟩
  have hcard : k ≤ (D \ N).card := by
    rw [Finset.card_sdiff hND, hD]
    omega
  obtain ⟨U, hPU, hU, hUk⟩ := Finset.exists_subsuperset_card_eq hsub hP hcard
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
    exact Finset.mem_sdiff.mpr ⟨hND hx, fun hu => (Finset.mem_sdiff.mp (hU hu)).2 hx⟩

end MOR34
