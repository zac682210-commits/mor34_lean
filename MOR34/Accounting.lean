import MOR34.PrefixTools
import MOR34.PairingArithmetic

namespace MOR34

theorem sum_eq_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℤ) :
    (∑ i ∈ S, f i) = ∑ i, indicator S i * f i := by
  have he : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  calc
    (∑ i ∈ S, f i) = ∑ i ∈ Finset.univ.filter (fun i => i ∈ S), f i := by rw [he]
    _ = ∑ i, if i ∈ S then f i else 0 := Finset.sum_filter _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [indicator, hi]

theorem repartition_sum {q : ℕ} {m : Fin q → ℕ}
    {S T U V : Finset (Item m)} (h : Repartitions S T U V) (f : Item m → ℤ) :
    (∑ i ∈ U, f i) + (∑ i ∈ V, f i) = (∑ i ∈ S, f i) + (∑ i ∈ T, f i) := by
  rw [sum_eq_indicator U f, sum_eq_indicator V f,
    sum_eq_indicator S f, sum_eq_indicator T f]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    indicator U i * f i + indicator V i * f i = (indicator U i + indicator V i) * f i := by ring
    _ = (indicator S i + indicator T i) * f i := by rw [h i]
    _ = indicator S i * f i + indicator T i * f i := by ring

theorem candidateValue_counts {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) (S : Finset (Item m)) :
    candidateValue P S = ∑ j, (counts S j : ℤ) * P.coefficient j := by
  simpa [candidateValue, counts, nsmul_eq_mul] using
    (Finset.sum_fiberwise' S (fun i : Item m => i.1) P.coefficient).symm

theorem one_tight_of_repartition {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) {S T U V : Finset (Item m)}
    (hS : Tight P S) (hT : Tight P T) (hrep : Repartitions S T U V)
    (hcounts : ∀ j, counts U j = counts V j) : Tight P U ∨ Tight P V := by
  have heq : candidateValue P U = candidateValue P V := by
    rw [candidateValue_counts, candidateValue_counts]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcounts j]
  have hc : candidateValue P U + candidateValue P V = candidateValue P S + candidateValue P T :=
    repartition_sum hrep (fun i => P.coefficient i.1)
  have hw : weightSum P U + weightSum P V = weightSum P S + weightSum P T :=
    repartition_sum hrep P.weight
  have ht := balanced_values_are_tight _ _ _ _ _ hS.2 hT.2 heq hc
  have hf := one_feasible_of_pair_sum _ _ _ _ _ hS.1 hT.1 hw
  rcases hf with hU | hV
  · exact Or.inl ⟨hU, ht.1⟩
  · exact Or.inr ⟨hV, ht.2⟩

end MOR34
