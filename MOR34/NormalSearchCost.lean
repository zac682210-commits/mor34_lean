import MOR34.ExecutableMatrixNormals
import MOR34.ExecutableCountForms
import MOR34.SearchPayload
import MOR34.ComputedCellPipeline

namespace MOR34

/-- A list-size estimate used for the explicit finite candidate enumeration. -/
theorem flatMap_length_bound {α β : Type*} (L : List α) (f : α → List β) (C : ℕ)
    (h : ∀ x ∈ L, (f x).length ≤ C) : (L.flatMap f).length ≤ L.length * C := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    nlinarith

theorem normalSearchKeys_length_bound (s d : ℕ) (hd : 1 ≤ d) (hs : s ≤ d) :
    (normalSearchKeys s d).length ≤ (d+1) * d^(2*d) := by
  unfold normalSearchKeys
  apply (flatMap_length_bound _ _ (d^(2*d)) ?_).trans_eq
  · simp
  · intro r _
    have hr : r.val ≤ d := by omega
    have ha : s^r.val ≤ d^d :=
      (pow_le_pow_left' hs r.val).trans (pow_le_pow_right' hd hr)
    have hc : d^r.val ≤ d^d := pow_le_pow_right' hd hr
    have hh := flatMap_length_bound (allFinFunctions r.val s)
      (fun a => (allFinFunctions r.val d).map (fun c => (⟨r,a,c⟩ : NormalSearchKey s d)))
      (d^r.val) (by intro a _; simp [allFinFunctions_length])
    simp only [allFinFunctions_length] at hh
    calc
      _ ≤ s^r.val * d^r.val := hh
      _ ≤ d^d * d^d := Nat.mul_le_mul ha hc
      _ = d^(2*d) := by rw [← pow_add]; congr 1; omega

theorem matrixNormalSearch_calls {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (hd : 1 ≤ d) (hs : s ≤ d) :
    firstWitnessCalls (tryNormalKey M) (normalSearchKeys s d) ≤ (d+1)*d^(2*d) :=
  (firstWitness_calls_le _ _).trans (normalSearchKeys_length_bound s d hd hs)

/-- The bound applies to the matrix actually built from the selected count points. -/
theorem computedCountForms_search_calls {q : ℕ} (B : Finset (Counts q)) (hB : B.card ≤ q+1) :
    firstWitnessCalls (tryNormalKey (orderedCountMatrix B))
      (normalSearchKeys (orderedCounts B).length (q+1)) ≤ (q+2)*(q+1)^(2*(q+1)) := by
  apply matrixNormalSearch_calls _ (by omega)
  simpa only [orderedCounts_length] using hB

/-- Cardinality is bounded at every actual recursive state, without assuming oracle correctness. -/
theorem searchStates_card {α : Type*} [DecidableEq α] (oracle : Finset α → Option α)
    (limit fuel : ℕ) (B : Finset α) (hB : B.card + fuel ≤ limit) :
    SearchStates oracle (fun S => S.card ≤ limit) fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ r ih =>
    refine ⟨by omega, ?_⟩
    cases he : oracle B with
    | none => simp [he]
    | some z =>
      simp only [he]
      apply ih
      have hh := Finset.card_insert_le z B
      omega

/-- Every normal computation used by the q+1-step basis search has parameter-only
candidate count. This counts candidate checks, not their integer bit cost. -/
theorem computedCountForms_search_states {q : ℕ} (solve : IntegerQuery q → Option (Counts q)) :
    SearchStates (linearSpanOracle solve computedCountForms)
      (fun B => firstWitnessCalls (tryNormalKey (orderedCountMatrix B))
        (normalSearchKeys (orderedCounts B).length (q+1)) ≤ (q+2)*(q+1)^(2*(q+1))) (q+1) ∅ := by
  have aux : ∀ fuel (B : Finset (Counts q)), B.card + fuel ≤ q+1 →
      SearchStates (linearSpanOracle solve computedCountForms)
        (fun B => firstWitnessCalls (tryNormalKey (orderedCountMatrix B))
          (normalSearchKeys (orderedCounts B).length (q+1)) ≤ (q+2)*(q+1)^(2*(q+1))) fuel B := by
    intro fuel
    induction fuel with
    | zero => intros; trivial
    | succ r ih =>
      intro B hB
      refine ⟨computedCountForms_search_calls B (by omega), ?_⟩
      cases he : linearSpanOracle solve computedCountForms B with
      | none => simp [he]
      | some z =>
        simp only [he]
        apply ih
        have hh := Finset.card_insert_le z B
        omega
  exact aux _ _ (by simp)

/-- Candidate checks charged once per normal-family invocation along the actual basis search.
List construction, arithmetic inside a check, and solver work are separate costs. -/
def normalBasisCandidateCalls {q : ℕ} (solve : IntegerQuery q → Option (Counts q)) :
    ℕ → Finset (Counts q) → ℕ
  | 0, _ => 0
  | r+1, B => firstWitnessCalls (tryNormalKey (orderedCountMatrix B))
      (normalSearchKeys (orderedCounts B).length (q+1)) +
      match linearSpanOracle solve computedCountForms B with
      | none => 0
      | some z => normalBasisCandidateCalls solve r (insert z B)

theorem normalBasisCandidateCalls_bound {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (fuel : ℕ) (B : Finset (Counts q)) (hB : B.card + fuel ≤ q+1) :
    normalBasisCandidateCalls solve fuel B ≤ fuel * ((q+2)*(q+1)^(2*(q+1))) := by
  induction fuel generalizing B with
  | zero => simp [normalBasisCandidateCalls]
  | succ r ih =>
    have hc := computedCountForms_search_calls B (by omega : B.card ≤ q+1)
    cases he : linearSpanOracle solve computedCountForms B with
    | none =>
      simp only [normalBasisCandidateCalls, he, add_zero]
      nlinarith
    | some z =>
      have hi : (insert z B).card + r ≤ q+1 := by
        have hh := Finset.card_insert_le z B
        omega
      have hh := ih (insert z B) hi
      simp only [normalBasisCandidateCalls, he]
      nlinarith

theorem computedCellSelection_normal_checks {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q)
    (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    normalBasisCandidateCalls
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) (q+1) ∅ ≤
      (q+1)*((q+2)*(q+1)^(2*(q+1))) :=
  normalBasisCandidateCalls_bound _ _ _ (by simp)

end MOR34
