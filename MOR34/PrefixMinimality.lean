import MOR34.Accounting
import MOR34.PaperInterface
import Mathlib.Data.Finset.Sort

namespace MOR34

variable {q : ℕ} {m : Fin q → ℕ}

/-- Selected positions in one coefficient class. -/
def classSlice (S : Finset (Item m)) (j : Fin q) : Finset (Fin (m j)) :=
  Finset.univ.filter fun u => (⟨j, u⟩ : Item m) ∈ S

@[simp] theorem mem_classSlice (S : Finset (Item m)) (j : Fin q) (u : Fin (m j)) :
    u ∈ classSlice S j ↔ (⟨j, u⟩ : Item m) ∈ S := by simp [classSlice]

theorem assemble_classSlice (S : Finset (Item m)) : assemble (classSlice S) = S := by
  ext i
  simp

theorem counts_classSlice (S : Finset (Item m)) (j : Fin q) :
    counts S j = (classSlice S j).card := by
  rw [← counts_assemble, assemble_classSlice]

theorem counts_bounded (S : Finset (Item m)) : BoundedCounts (counts S) := by
  intro j
  rw [counts_classSlice]
  simpa using Finset.card_le_univ (classSlice S j)

theorem counts_prefixSet (z : Counts q) (hz : BoundedCounts (m := m) z) :
    counts (prefixSet (m := m) z) = z := by
  funext j
  rw [prefixSet_assemble, counts_assemble, card_classPrefix (hz j)]

theorem sum_assemble (F : (j : Fin q) → Finset (Fin (m j))) (f : Item m → ℤ) :
    (∑ i ∈ assemble F, f i) = ∑ j, ∑ u ∈ F j, f ⟨j, u⟩ := by
  exact Finset.sum_sigma _ _ _

/-- An increasing list of distinct nonnegative positions cannot undershoot its index. -/
theorem orderEmbedding_index_le {k s : ℕ} (e : Fin k ↪o Fin s) (i : Fin k) :
    i.val ≤ (e i).val := by
  have aux : ∀ n (i : Fin k), i.val = n → i.val ≤ (e i).val := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      let j : Fin k := ⟨n, by omega⟩
      have hj := ih j rfl
      have hji : j < i := by change j.val < i.val; dsimp [j]; omega
      have he := e.strictMono hji
      change (e j).val < (e i).val at he
      dsimp [j] at hj
      omega
  exact aux i.val i rfl

theorem classPrefix_map {s k : ℕ} (h : k ≤ s) :
    Finset.univ.map (Fin.castLEOrderEmb h).toEmbedding = classPrefix s k := by
  ext v
  simp only [Finset.mem_map, Finset.mem_univ, true_and, mem_classPrefix]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.isLt
  · intro hv
    exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩

/-- Sorted prefixes minimize every monotone sum at fixed cardinality. -/
theorem classPrefix_minimal {s : ℕ} (S : Finset (Fin s)) (f : Fin s → ℤ)
    (hf : Monotone f) : (∑ i ∈ classPrefix s S.card, f i) ≤ ∑ i ∈ S, f i := by
  have hb : S.card ≤ s := by simpa using Finset.card_le_univ S
  have hsum : (∑ i ∈ S, f i) = ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) := by
    calc
      (∑ i ∈ S, f i) = ∑ i ∈ Finset.univ.map (S.orderEmbOfFin rfl).toEmbedding, f i :=
        congrArg (fun T : Finset (Fin s) => ∑ i ∈ T, f i) (S.map_orderEmbOfFin_univ rfl).symm
      _ = _ := Finset.sum_map _ _ _
  rw [← classPrefix_map hb, Finset.sum_map, hsum]
  apply Finset.sum_le_sum
  intro i _
  apply hf
  exact orderEmbedding_index_le (S.orderEmbOfFin rfl) i

/-- The exact paper-facing minimum-weight prefix specification. -/
theorem prefixMinimality (P : Model m) : PaperInterface.PrefixMinimality P := by
  intro hWF S
  rcases hWF with ⟨_, _, _, _, _, _, _, hsorted⟩
  change (∑ i ∈ prefixSet (counts S), P.weight i) ≤ ∑ i ∈ S, P.weight i
  rw [prefixSet_assemble, sum_assemble]
  calc
    (∑ j, ∑ u ∈ classPrefix (m j) (counts S j), P.weight ⟨j, u⟩)
        ≤ ∑ j, ∑ u ∈ classSlice S j, P.weight ⟨j, u⟩ := by
      apply Finset.sum_le_sum
      intro j _
      rw [counts_classSlice]
      exact classPrefix_minimal (classSlice S j) (fun u => P.weight ⟨j, u⟩) (hsorted j)
    _ = ∑ i ∈ S, P.weight i := by rw [← sum_assemble, assemble_classSlice]

theorem prefix_tight (P : Model m) (hWF : WellFormed P)
    {S : Finset (Item m)} (hS : Tight P S) : Tight P (prefixSet (counts S)) := by
  constructor
  · exact le_trans (prefixMinimality P hWF S) hS.1
  · rw [candidateValue_counts, counts_prefixSet _ (counts_bounded S)]
    rw [← candidateValue_counts]
    exact hS.2

end MOR34
