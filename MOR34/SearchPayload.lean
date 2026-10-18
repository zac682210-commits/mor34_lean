import MOR34.RowPayload
import MOR34.BoundedCellPipeline
import MOR34.ParameterCount

namespace MOR34

/-- An invariant at every queried state, following the procedure's actual answers. -/
def SearchStates {α : Type*} [DecidableEq α] (oracle : Finset α → Option α)
    (Inv : Finset α → Prop) : ℕ → Finset α → Prop
  | 0, _ => True
  | r+1, B => Inv B ∧ match oracle B with
    | none => True
    | some z => SearchStates oracle Inv r (insert z B)

theorem searchStates_of_containment {α : Type*} [DecidableEq α]
    (C : Set α) (oracle : Finset α → Option α)
    (hf : ∀ B z, oracle B = some z → z ∈ C)
    (Inv : Finset α → Prop) (hInv : ∀ B : Finset α, (B : Set α) ⊆ C → Inv B)
    (fuel : ℕ) (B : Finset α) (hB : (B : Set α) ⊆ C) : SearchStates oracle Inv fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ r ih =>
    refine ⟨hInv B hB, ?_⟩
    cases he : oracle B with
    | none => simp [he]
    | some z =>
      simp only [he]
      apply ih
      intro x hx
      rcases Finset.mem_insert.mp hx with hxz | hx
      · subst x
        exact hf B z he
      · exact hB hx

variable {q : ℕ} {m : Fin q → ℕ}

/-- Every generated separating query has a bounded dense integer payload. -/
def CellSearchPayload (P : Model m) (ε : Parity q) (e : ParityExtrema P ε)
    (mode : CellMode q) (N M : ℕ) (B : Finset (Counts q)) : Prop :=
  ∀ t ∈ outsideQueries (boundedCountForms B),
    ∃ a b : CountRow m (t :: cellQueries e.low e.high mode).length → Fin q → ℤ,
      ∃ d : CountRow m (t :: cellQueries e.low e.high mode).length → ℤ,
      (∀ k, (countRow P (queryCoefficients (t :: cellQueries e.low e.high mode))
        (queryBounds (t :: cellQueries e.low e.high mode)) k).withParity ε = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+5*q+4)*((2*q+1)*uniformRowBits q N M)

theorem cellSearch_payload_states (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : q ≤ N) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) :
    SearchStates (linearSpanOracle (rowCellOracle solve ε e mode) boundedCountForms)
      (CellSearchPayload P ε e mode N M) (q+1) ∅ := by
  have hor := linearSpanOracle_spec (parityCellSet P ε e mode) (rowCellOracle solve ε e mode)
    (rowCellOracle_spec P hWF solve hs ε e mode) boundedCountForms boundedCountForms_spec
  apply searchStates_of_containment (parityCellSet P ε e mode) _ (fun B z hz => (hor.found B z hz).1)
  · intro B hB t ht
    apply cell_system_payload P N M hN hM hq hm hw hc hb hd e.low e.high mode
    · intro j
      rw [← e.lower_eq j]
      exact ((e.lower_mem j).1 j).trans (hm j)
    · intro j
      rw [← e.upper_eq j]
      exact ((e.upper_mem j).1 j).trans (hm j)
    · intro z hz j
      exact ((hB hz).1.1 j).trans (hm j)
    · exact ht
  · simp

/-- Instantiation at the exact extrema and scalar solver used in boundedPipeline. -/
theorem boundedPipeline_payload_states (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    SearchStates
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) boundedCountForms)
      (CellSearchPayload P ε (rowSearchedExtrema P hWF solve hs ε hn) mode
        (Fintype.card (Item m)+1) M) (q+1) ∅ :=
  cellSearch_payload_states P hWF solve hs ε _ mode _ M (by omega) hM
    ((coefficient_classes_le_items P hWF).trans (Nat.le_succ _))
    (fun j => (class_size_le_items j).trans (Nat.le_succ _)) hw hc hb hd

end MOR34
