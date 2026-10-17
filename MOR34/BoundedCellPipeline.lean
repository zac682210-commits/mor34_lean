import MOR34.BoundedNormalFamily
import MOR34.NormalizedPipeline

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Every normal-family call in the recursive count search satisfies the magnitude bound. -/
def CountSearchFormsBounded (solve : IntegerQuery q → Option (Counts q)) (N : ℕ) :
    ℕ → Finset (Counts q) → Prop
  | 0, _ => True
  | n + 1, B => FormsBounded (boundedCountForms B) N ∧
      match linearSpanOracle solve boundedCountForms B with
      | none => True
      | some z => CountSearchFormsBounded solve N n (insert z B)

theorem countSearch_forms_bounded (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (N : ℕ) (hN : 1 ≤ N) (hC : ∀ z ∈ C, ∀ j, z j ≤ N)
    (fuel : ℕ) (B : Finset (Counts q)) (hB : (B : Set (Counts q)) ⊆ C) :
    CountSearchFormsBounded solve N fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ n ih =>
    refine ⟨boundedCountForms_bound B N hN (fun z hz j => hC z (hB hz) j), ?_⟩
    cases he : linearSpanOracle solve boundedCountForms B with
    | none => simp [he]
    | some z =>
      simp only [he]
      apply ih
      intro x hx
      have hz := ((linearSpanOracle_spec C solve hs boundedCountForms boundedCountForms_spec).found B z he).1
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz
      · exact hB hx

/-- The actual cell searches now use the bounded family, not the earlier quotient-normal choice. -/
noncomputable def boundedCellSelection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : CellBasisSelection P := by
  let ex := rowSearchedExtrema P hWF solve hs
  let B := fun ε hn mode => basisSearch
    (linearSpanOracle (rowCellOracle solve ε (ex ε hn) mode) boundedCountForms) (q + 1) ∅
  have hc := fun ε hn mode => linear_count_basis_correct
    (parityCellSet P ε (ex ε hn) mode) (rowCellOracle solve ε (ex ε hn) mode)
    (rowCellOracle_spec P hWF solve hs ε (ex ε hn) mode)
    boundedCountForms boundedCountForms_spec (fun B => (boundedCountForms_length B).le)
  exact {
    extrema := ex
    basis := B
    contained := fun ε hn mode => (hc ε hn mode).1
    spanning := fun ε hn mode z hz =>
      countReal_affineSpan_of_rational_span _ z ((hc ε hn mode).2.2.1 z hz)
  }

theorem boundedCellSelection_basis (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    (boundedCellSelection P hWF solve hs).basis ε hn mode = basisSearch
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
        boundedCountForms) (q + 1) ∅ := rfl

theorem boundedCellSelection_small (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, ((boundedCellSelection P hWF solve hs).basis ε hn mode).card ≤ q + 1 := by
  intro ε hn mode
  rw [boundedCellSelection_basis]
  simpa using basisSearch_card
    (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      boundedCountForms) (q + 1) ∅

theorem boundedCellSelection_query_calls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, linearBasisCalls
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      boundedCountForms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  intro ε hn mode
  have hh := linearBasisCalls_le
    (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
    boundedCountForms (q + 1) (fun B => (boundedCountForms_length B).le) (q + 1) ∅
  nlinarith

theorem class_size_le_items (j : Fin q) : m j ≤ Fintype.card (Item m) := by
  let f : Fin (m j) → Item m := fun k => ⟨j, k⟩
  have hi : Function.Injective f := by
    intro a b h
    simpa [f] using h
  simpa using Fintype.card_le_of_injective f hi

theorem boundedCellSelection_query_bounds (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, CountSearchFormsBounded
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      (Fintype.card (Item m) + 1) (q + 1) ∅ := by
  intro ε hn mode
  apply countSearch_forms_bounded
    (parityCellSet P ε (rowSearchedExtrema P hWF solve hs ε hn) mode) _
    (rowCellOracle_spec P hWF solve hs ε _ mode) _ (by omega)
  · intro z hz j
    exact (hz.1.1 j).trans ((class_size_le_items (m := m) j).trans (Nat.le_succ _))
  · simp

end MOR34
