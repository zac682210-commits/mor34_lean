import MOR34.PreparedNormalExecution

namespace MOR34
variable {q : ℕ}

def preparedCellStep (prep : CountMatrixPreparation q) (unit normalRead : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ) (B : Finset (Counts q)) :
    Option (Counts q) × ℕ :=
  let forms := preparedCountForms prep unit B
  let queries := chargedOutsideQueries forms.1 normalRead
  let found := chargedFirstWitness solve queries.1
  (found.1,forms.2+queries.2+found.2+1)

theorem preparedCellStep_value (prep : CountMatrixPreparation q) (unit normalRead : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ) (B : Finset (Counts q)) :
    (preparedCellStep prep unit normalRead solve B).1 =
      linearSpanOracle (fun a => (solve a).1) computedCountForms B := by
  simp only [preparedCellStep,chargedFirstWitness_value,chargedOutsideQueries_value,
    preparedCountForms_value,linearSpanOracle]

def preparedCellStepBudget (q unit E R U : ℕ) : ℕ :=
  E+builtCountFormBudget q*unit+(q+1)*(4*(q+1)*(R+1)+3)+2*(q+1)*(U+1)+2

theorem preparedCellStep_cost (prep : CountMatrixPreparation q) (unit E R U : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ) (B : Finset (Counts q))
    (hB : B.card ≤ q+1) (he : (prep.emit B).2 ≤ E)
    (hs : ∀ a ∈ outsideQueries (computedCountForms B), (solve a).2 ≤ U) :
    (preparedCellStep prep unit R solve B).2 ≤ preparedCellStepBudget q unit E R U := by
  have hf := preparedCountForms_cost prep unit E B hB he
  have hq := chargedOutsideQueries_cost (preparedCountForms prep unit B).1 R
  rw [preparedCountForms_value,computedCountForms_length] at hq
  have hc := chargedFirstWitness_cost solve (outsideQueries (computedCountForms B)) U hs
  have hl := linearSpanOracle_calls_le (fun a => (solve a).1) computedCountForms B
  rw [computedCountForms_length] at hl
  have hc' := hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (U+1) hl) 1)
  dsimp only [preparedCellStep,preparedCellStepBudget]
  rw [chargedOutsideQueries_value,preparedCountForms_value]
  omega

def preparedCellBasis (prep : CountMatrixPreparation q) (unit R : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ) :
    Finset (Counts q) × ℕ := chargedBasisExecution (preparedCellStep prep unit R solve) put (q+1) ∅

theorem preparedCellBasis_value (prep : CountMatrixPreparation q) (unit R : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) :
    (preparedCellBasis prep unit R solve put).1 =
      basisSearch (linearSpanOracle (fun a => (solve a).1) computedCountForms) (q+1) ∅ := by
  rw [preparedCellBasis,chargedBasisExecution_value _ _ hp]
  simp only [preparedCellStep_value]

/-- Each matrix-preparation call is bounded only on actual reached sets. The
matrix is then used by that same normal search before the next scalar query. -/
theorem preparedCellBasis_cost_on_states (prep : CountMatrixPreparation q)
    (C : Set (Counts q)) (unit E R U J : ℕ)
    (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (hor : LinearOracleSpec C (fun a => (solve a).1))
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B)
    (hi : ∀ z (B : Finset (Counts q)), B.card ≤ q+1 → z ∈ C →
      (B : Set (Counts q)) ⊆ C → (put z B).2 ≤ J)
    (he : ∀ (B : Finset (Counts q)), B.card ≤ q+1 → (B : Set (Counts q)) ⊆ C →
      (prep.emit B).2 ≤ E)
    (hs : SearchStates (linearSpanOracle (fun a => (solve a).1) computedCountForms)
      (fun B => ∀ a ∈ outsideQueries (computedCountForms B), (solve a).2 ≤ U) (q+1) ∅) :
    (preparedCellBasis prep unit R solve put).2 ≤
      (q+1)*(preparedCellStepBudget q unit E R U+J+1)+1 := by
  have hf := linearSpanOracle_spec C (fun a => (solve a).1) hor computedCountForms computedCountForms_spec
  have hc := searchStates_of_containment C _ (fun B z hz => (hf.found B z hz).1)
    (fun B => (B : Set (Counts q)) ⊆ C) (fun _ h => h) (q+1) ∅ (by simp)
  have hcard := searchStates_card (linearSpanOracle (fun a => (solve a).1) computedCountForms)
    (q+1) (q+1) ∅ (by simp)
  have hboth := searchStates_and _ _ _ _ _ hcard (searchStates_and _ _ _ _ _ hs hc)
  apply chargedBasisExecution_cost_on_states _ put hp
  simp only [preparedCellStep_value]
  apply searchStates_mono _ _ _ ?_ _ _ hboth
  intro B hB
  refine ⟨preparedCellStep_cost prep unit E R U solve B hB.1 (he B hB.1 hB.2.2) hB.2.1,?_⟩
  intro z hz
  exact hi z B hB.1 (hf.found B z hz).1 hB.2.2

theorem preparedCellBudget_uniform (K H I W : ℕ → ℕ) (d a c b : ℕ) :
    UniformPolynomial (fun q n L => (q+1)*(preparedCellStepBudget q
      (H q*(n+L+2)^a) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
      (weightedCellQueryBudget q n L (K q*(n+L+2)^d) (I q) c (W q) b)+
      K q*(n+L+2)^d+1)+1) := by
  unfold preparedCellStepBudget weightedCellQueryBudget
  uniform_polynomial

end MOR34
