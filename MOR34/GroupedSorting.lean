import MOR34.Model
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The grouped-input hypotheses before ordering weights inside classes. -/
def GroupedConditions (P : Model m) : Prop :=
  0 < q ∧ (∀ j, 0 < m j) ∧ (∀ i, 0 < P.weight i) ∧ 0 < P.capacity ∧
  (∀ i, P.weight i ≤ P.capacity) ∧ (∀ j, 0 ≤ P.coefficient j) ∧
  Function.Injective P.coefficient

def sortItems (P : Model m) : Item m ≃ Item m :=
  Equiv.sigmaCongrRight (fun j => Tuple.sort (fun k => P.weight ⟨j, k⟩))

def sortGrouped (P : Model m) : Model m :=
  ⟨fun i => P.weight (sortItems P i), P.coefficient, P.capacity, P.rhs⟩

theorem sortItems_class (P : Model m) (i : Item m) : (sortItems P i).1 = i.1 := rfl

theorem sortGrouped_wellFormed (P : Model m) (h : GroupedConditions P) :
    WellFormed (sortGrouped P) := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · intro i
    exact h.2.2.1 (sortItems P i)
  · intro i
    exact h.2.2.2.2.1 (sortItems P i)
  · intro j u v huv
    exact Tuple.monotone_sort (fun k => P.weight ⟨j, k⟩) huv

theorem sortGrouped_weightSum (P : Model m) (S : Finset (Item m)) :
    weightSum (sortGrouped P) S = weightSum P (S.map (sortItems P).toEmbedding) := by
  classical
  simp [weightSum, sortGrouped]

theorem sortGrouped_candidateValue (P : Model m) (S : Finset (Item m)) :
    candidateValue (sortGrouped P) S = candidateValue P (S.map (sortItems P).toEmbedding) := by
  classical
  simp [candidateValue, sortGrouped, sortItems]

theorem sortGrouped_feasible (P : Model m) (S : Finset (Item m)) :
    Feasible (sortGrouped P) S ↔ Feasible P (S.map (sortItems P).toEmbedding) := by
  unfold Feasible
  rw [sortGrouped_weightSum]
  rfl

theorem sortGrouped_tight (P : Model m) (S : Finset (Item m)) :
    Tight (sortGrouped P) S ↔ Tight P (S.map (sortItems P).toEmbedding) := by
  unfold Tight
  rw [sortGrouped_feasible, sortGrouped_candidateValue]
  rfl

theorem sortGrouped_valid (P : Model m) : Valid (sortGrouped P) ↔ Valid P := by
  classical
  constructor
  · intro h S hS
    let T := S.map (sortItems P).symm.toEmbedding
    have he : T.map (sortItems P).toEmbedding = S := by
      ext i
      simp [T]
    have ht : Feasible (sortGrouped P) T := (sortGrouped_feasible P T).mpr (he.symm ▸ hS)
    have hh := h T ht
    rw [sortGrouped_candidateValue, he] at hh
    exact hh
  · intro h S hS
    have hh := h _ ((sortGrouped_feasible P S).mp hS)
    rwa [← sortGrouped_candidateValue] at hh

end MOR34
