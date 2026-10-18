import MOR34.ChargedSearchExecution

namespace MOR34

/-- Dense positive/negative query records are constructed from retained normal
forms. R is the primitive cost of reading a stored normal coefficient. -/
def chargedOutsideQueries {q : ℕ} (forms : List (IntegerForm q)) (R : ℕ) :
    List (IntegerQuery q) × ℕ :=
  chargedFlatMap (fun f => ([f.positiveQuery,f.negativeQuery],4*(q+1)*(R+1))) forms

theorem chargedOutsideQueries_value {q : ℕ} (forms : List (IntegerForm q)) (R : ℕ) :
    (chargedOutsideQueries forms R).1 = outsideQueries forms := by
  simp [chargedOutsideQueries,chargedFlatMap_value,outsideQueries]

theorem chargedOutsideQueries_cost {q : ℕ} (forms : List (IntegerForm q)) (R : ℕ) :
    (chargedOutsideQueries forms R).2 ≤ forms.length*(4*(q+1)*(R+1)+3) := by
  exact chargedFlatMap_cost _ forms _ 2 (fun _ _ => le_rfl) (by intro f _; simp)

/-- One cell step retains its generated forms and queries and executes the
charged early-stop solver search on that exact query list. -/
def chargedCellStep {q : ℕ} (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (normalRead : ℕ) (B : Finset (Counts q)) : Option (Counts q) × ℕ :=
  let forms := builtCountForms B
  let queries := chargedOutsideQueries forms.1 normalRead
  let found := chargedFirstWitness solve queries.1
  (found.1,forms.2+queries.2+found.2+1)

theorem chargedCellStep_value {q : ℕ} (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (R : ℕ) (B : Finset (Counts q)) :
    (chargedCellStep solve R B).1 = linearSpanOracle (fun a => (solve a).1) computedCountForms B := by
  simp only [chargedCellStep,chargedFirstWitness_value,chargedOutsideQueries_value,
    builtCountForms_value,linearSpanOracle]

def chargedCellStepBudget (q R U : ℕ) : ℕ :=
  builtCountFormBudget q+(q+1)*(4*(q+1)*(R+1)+3)+2*(q+1)*(U+1)+2

theorem chargedCellStep_cost {q : ℕ} (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (R U : ℕ) (B : Finset (Counts q)) (hB : B.card ≤ q+1)
    (hU : ∀ a ∈ outsideQueries (computedCountForms B), (solve a).2 ≤ U) :
    (chargedCellStep solve R B).2 ≤ chargedCellStepBudget q R U := by
  have hf := builtCountForms_cost B hB
  have hq := chargedOutsideQueries_cost (builtCountForms B).1 R
  rw [builtCountForms_value,computedCountForms_length] at hq
  have hs := chargedFirstWitness_cost solve (outsideQueries (computedCountForms B)) U hU
  have hc := linearSpanOracle_calls_le (fun a => (solve a).1) computedCountForms B
  rw [computedCountForms_length] at hc
  have hs' := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (U+1) hc) 1)
  dsimp only [chargedCellStep,chargedCellStepBudget]
  rw [chargedOutsideQueries_value,builtCountForms_value]
  omega

/-- Local bounds are required only along reached states. This permits a bit
bound using the proved count-coordinate invariant instead of all finite sets. -/
theorem chargedBasisExecution_cost_on_states {α : Type*} [DecidableEq α]
    (step : Finset α → Option α × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) (S I fuel : ℕ) (B : Finset α)
    (hstate : SearchStates (fun B => (step B).1)
      (fun B => (step B).2 ≤ S ∧ ∀ z, (step B).1 = some z → (put z B).2 ≤ I) fuel B) :
    (chargedBasisExecution step put fuel B).2 ≤ fuel*(S+I+1)+1 := by
  induction fuel generalizing B with
  | zero => simp [chargedBasisExecution]
  | succ n ih =>
      have hs := hstate.1.1
      cases h : (step B).1 with
      | none => simp only [chargedBasisExecution,h]; nlinarith
      | some z =>
          have hi := hstate.1.2 z h
          have ht := ih (insert z B) (by simpa only [SearchStates,h] using hstate.2)
          simp only [chargedBasisExecution,h,hp]
          nlinarith

def chargedCellBasis {q : ℕ} (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (R : ℕ) (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ) :
    Finset (Counts q) × ℕ := chargedBasisExecution (chargedCellStep solve R) put (q+1) ∅

theorem chargedCellBasis_value {q : ℕ} (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (R : ℕ) (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) :
    (chargedCellBasis solve R put).1 =
      basisSearch (linearSpanOracle (fun a => (solve a).1) computedCountForms) (q+1) ∅ := by
  rw [chargedCellBasis,chargedBasisExecution_value _ _ hp]
  simp only [chargedCellStep_value]

end MOR34
