import MOR34.DenseBasicQueryCost
import MOR34.ChargedCellExecution

namespace MOR34

theorem searchStates_and {α : Type*} [DecidableEq α]
    (oracle : Finset α → Option α) (I J : Finset α → Prop) (fuel : ℕ) (B : Finset α)
    (hi : SearchStates oracle I fuel B) (hj : SearchStates oracle J fuel B) :
    SearchStates oracle (fun B => I B ∧ J B) fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ r ih =>
      refine ⟨⟨hi.1,hj.1⟩,?_⟩
      cases h : oracle B with
      | none => simp [h]
      | some z =>
          simp only [h]
          exact ih (insert z B) (by simpa only [SearchStates,h] using hi.2)
            (by simpa only [SearchStates,h] using hj.2)

/-- This closes the cell loop from costs of actual reached scalar queries.
Only finite-collection insertion remains an explicit local primitive. -/
theorem chargedCellBasis_cost_of_query_states {q : ℕ}
    (solve : IntegerQuery q → Option (Counts q) × ℕ) (R U J : ℕ)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B)
    (hi : ∀ z B, B.card ≤ q+1 → (put z B).2 ≤ J)
    (hs : SearchStates (linearSpanOracle (fun a => (solve a).1) computedCountForms)
      (fun B => ∀ a ∈ outsideQueries (computedCountForms B), (solve a).2 ≤ U) (q+1) ∅) :
    (chargedCellBasis solve R put).2 ≤
      (q+1)*(chargedCellStepBudget q R U+J+1)+1 := by
  have hcard := searchStates_card
    (linearSpanOracle (fun a => (solve a).1) computedCountForms) (q+1) (q+1) ∅ (by simp)
  have hboth := searchStates_and _ _ _ _ _ hcard hs
  have hstate : SearchStates (fun B => (chargedCellStep solve R B).1)
      (fun B => (chargedCellStep solve R B).2 ≤ chargedCellStepBudget q R U ∧
        ∀ z, (chargedCellStep solve R B).1 = some z → (put z B).2 ≤ J) (q+1) ∅ := by
    simp only [chargedCellStep_value]
    apply searchStates_mono _ _ _ ?_ _ _ hboth
    intro B hB
    exact ⟨chargedCellStep_cost solve R U B hB.1 hB.2,fun z _ => hi z B hB.1⟩
  exact chargedBasisExecution_cost_on_states (chargedCellStep solve R) put hp
    (chargedCellStepBudget q R U) J (q+1) ∅ hstate

/-- For bit-sensitive collections, insertion is bounded only on genuine cell
points. No uniform insertion cost on arbitrarily large count vectors is needed. -/
theorem chargedCellBasis_cost_on_contained_states {q : ℕ}
    (C : Set (Counts q)) (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (hor : LinearOracleSpec C (fun a => (solve a).1)) (R U J : ℕ)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B)
    (hi : ∀ z (B : Finset (Counts q)), B.card ≤ q+1 → z ∈ C → (B : Set (Counts q)) ⊆ C → (put z B).2 ≤ J)
    (hs : SearchStates (linearSpanOracle (fun a => (solve a).1) computedCountForms)
      (fun B => ∀ a ∈ outsideQueries (computedCountForms B), (solve a).2 ≤ U) (q+1) ∅) :
    (chargedCellBasis solve R put).2 ≤
      (q+1)*(chargedCellStepBudget q R U+J+1)+1 := by
  have hf := linearSpanOracle_spec C (fun a => (solve a).1) hor
    computedCountForms computedCountForms_spec
  have hc := searchStates_of_containment C _ (fun B z hz => (hf.found B z hz).1)
    (fun B => (B : Set (Counts q)) ⊆ C) (fun _ h => h) (q+1) ∅ (by simp)
  have hcard := searchStates_card
    (linearSpanOracle (fun a => (solve a).1) computedCountForms) (q+1) (q+1) ∅ (by simp)
  have hboth := searchStates_and _ _ _ _ _ hcard (searchStates_and _ _ _ _ _ hs hc)
  have hstate : SearchStates (fun B => (chargedCellStep solve R B).1)
      (fun B => (chargedCellStep solve R B).2 ≤ chargedCellStepBudget q R U ∧
        ∀ z, (chargedCellStep solve R B).1 = some z → (put z B).2 ≤ J) (q+1) ∅ := by
    simp only [chargedCellStep_value]
    apply searchStates_mono _ _ _ ?_ _ _ hboth
    intro B hB
    exact ⟨chargedCellStep_cost solve R U B hB.1 hB.2.1,
      fun z hz => hi z B hB.1 (hf.found B z hz).1 hB.2.2⟩
  exact chargedBasisExecution_cost_on_states (chargedCellStep solve R) put hp
    (chargedCellStepBudget q R U) J (q+1) ∅ hstate

end MOR34
