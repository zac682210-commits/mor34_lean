import MOR34.InputGrouping
import MOR34.ParameterCount

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

def RawFeasible (a : Fin n → ℤ) (b : ℤ) (S : Finset (Fin n)) : Prop :=
  (∑ i ∈ S, a i) ≤ b

def RawTight (a c : Fin n → ℤ) (b d : ℤ) (S : Finset (Fin n)) : Prop :=
  RawFeasible a b S ∧ (∑ i ∈ S, c i) = d

def RawValid (a c : Fin n → ℤ) (b d : ℤ) : Prop :=
  ∀ S, RawFeasible a b S → (∑ i ∈ S, c i) ≤ d

theorem relabel_weight_sum (P : Model m) (e : Item m ≃ Fin n) (a : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (S : Finset (Item m)) :
    weightSum P S = ∑ i ∈ S.map e.toEmbedding, a i := by
  classical
  simpa only [weightSum, Finset.sum_map, Equiv.toEmbedding_apply] using
    Finset.sum_congr rfl (fun i (_ : i ∈ S) => ha i)

theorem relabel_candidate_sum (P : Model m) (e : Item m ≃ Fin n) (c : Fin n → ℤ)
    (hc : ∀ i, P.coefficient i.1 = c (e i)) (S : Finset (Item m)) :
    candidateValue P S = ∑ i ∈ S.map e.toEmbedding, c i := by
  classical
  simpa only [candidateValue, Finset.sum_map, Equiv.toEmbedding_apply] using
    Finset.sum_congr rfl (fun i (_ : i ∈ S) => hc i)

theorem relabel_feasible (P : Model m) (e : Item m ≃ Fin n) (a : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (S : Finset (Item m)) :
    Feasible P S ↔ RawFeasible a P.capacity (S.map e.toEmbedding) := by
  unfold Feasible RawFeasible
  rw [relabel_weight_sum P e a ha]

theorem relabel_tight (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (S : Finset (Item m)) :
    Tight P S ↔ RawTight a c P.capacity P.rhs (S.map e.toEmbedding) := by
  unfold Tight RawTight
  rw [relabel_feasible P e a ha, relabel_candidate_sum P e c hc]

theorem relabel_valid (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    Valid P ↔ RawValid a c P.capacity P.rhs := by
  classical
  constructor
  · intro h S hS
    let T := S.map e.symm.toEmbedding
    have he : T.map e.toEmbedding = S := by ext i; simp [T]
    have ht : Feasible P T := (relabel_feasible P e a ha T).mpr (he.symm ▸ hS)
    have hh := h T ht
    rw [relabel_candidate_sum P e c hc, he] at hh
    exact hh
  · intro h S hS
    have hh := h _ ((relabel_feasible P e a ha S).mp hS)
    rwa [← relabel_candidate_sum P e c hc] at hh

/-- The paper parameter is preserved by the actual item bijection. -/
theorem relabel_positive_values (P : Model m) (e : Item m ≃ Fin n) (c : Fin n → ℤ)
    (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    positiveCandidateValues P = (Finset.univ.image c).filter (fun v => 0 < v) := by
  classical
  ext v
  simp only [positiveCandidateValues, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hv⟩
    exact ⟨⟨e i, (hc i).symm.trans hi⟩, hv⟩
  · rintro ⟨⟨i, hi⟩, hv⟩
    refine ⟨⟨e.symm i, ?_⟩, hv⟩
    simpa using (hc (e.symm i)).trans (by simpa using hi)

theorem raw_parameter_bound (P : Model m) (hWF : WellFormed P)
    (e : Item m ≃ Fin n) (c : Fin n → ℤ)
    (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    q ≤ ((Finset.univ.image c).filter (fun v => 0 < v)).card + 1 := by
  rw [← relabel_positive_values P e c hc]
  exact coefficient_class_parameter_bound P hWF

theorem raw_classes_le_items (P : Model m) (hWF : WellFormed P)
    (e : Item m ≃ Fin n) : q ≤ n := by
  have he : Fintype.card (Item m) = n := by simpa using Fintype.card_congr e
  simpa only [he] using coefficient_classes_le_items P hWF

end MOR34
