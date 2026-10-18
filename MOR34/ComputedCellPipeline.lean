import MOR34.ExecutableCountForms
import MOR34.BoundedCellPipeline

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Every normal-family call in the recursive count search satisfies the magnitude bound. -/
def ComputedSearchFormsBounded (solve : IntegerQuery q → Option (Counts q)) (N : ℕ) :
    ℕ → Finset (Counts q) → Prop
  | 0, _ => True
  | n + 1, B => FormsBounded (computedCountForms B) N ∧
      match linearSpanOracle solve computedCountForms B with
      | none => True
      | some z => ComputedSearchFormsBounded solve N n (insert z B)

theorem computedSearch_forms_bounded (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (N : ℕ) (hN : 1 ≤ N) (hC : ∀ z ∈ C, ∀ j, z j ≤ N)
    (fuel : ℕ) (B : Finset (Counts q)) (hB : (B : Set (Counts q)) ⊆ C) :
    ComputedSearchFormsBounded solve N fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ n ih =>
    refine ⟨computedCountForms_bound B N hN (fun z hz j => hC z (hB hz) j), ?_⟩
    cases he : linearSpanOracle solve computedCountForms B with
    | none => simp [he]
    | some z =>
      simp only [he]
      apply ih
      intro x hx
      have hz := ((linearSpanOracle_spec C solve hs computedCountForms computedCountForms_spec).found B z he).1
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz
      · exact hB hx

/-- The actual cell searches now use the finite computed family, without classical normal selection. -/
def computedCellSelection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : CellBasisSelection P := by
  let ex := rowSearchedExtrema P hWF solve hs
  let B := fun ε hn mode => basisSearch
    (linearSpanOracle (rowCellOracle solve ε (ex ε hn) mode) computedCountForms) (q + 1) ∅
  have hc := fun ε hn mode => linear_count_basis_correct
    (parityCellSet P ε (ex ε hn) mode) (rowCellOracle solve ε (ex ε hn) mode)
    (rowCellOracle_spec P hWF solve hs ε (ex ε hn) mode)
    computedCountForms computedCountForms_spec (fun B => (computedCountForms_length B).le)
  exact {
    extrema := ex
    basis := B
    contained := fun ε hn mode => (hc ε hn mode).1
    spanning := fun ε hn mode z hz =>
      countReal_affineSpan_of_rational_span _ z ((hc ε hn mode).2.2.1 z hz)
  }

theorem computedCellSelection_basis (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    (computedCellSelection P hWF solve hs).basis ε hn mode = basisSearch
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
        computedCountForms) (q + 1) ∅ := rfl

theorem computedCellSelection_small (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, ((computedCellSelection P hWF solve hs).basis ε hn mode).card ≤ q + 1 := by
  intro ε hn mode
  rw [computedCellSelection_basis]
  simpa using basisSearch_card
    (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      computedCountForms) (q + 1) ∅

theorem computedCellSelection_query_calls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, linearBasisCalls
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      computedCountForms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  intro ε hn mode
  have hh := linearBasisCalls_le
    (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
    computedCountForms (q + 1) (fun B => (computedCountForms_length B).le) (q + 1) ∅
  nlinarith

theorem computedCellSelection_query_bounds (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    ∀ ε hn mode, ComputedSearchFormsBounded
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode)
      (Fintype.card (Item m) + 1) (q + 1) ∅ := by
  intro ε hn mode
  apply computedSearch_forms_bounded
    (parityCellSet P ε (rowSearchedExtrema P hWF solve hs ε hn) mode) _
    (rowCellOracle_spec P hWF solve hs ε _ mode) _ (by omega)
  · intro z hz j
    exact (hz.1.1 j).trans ((class_size_le_items (m := m) j).trans (Nat.le_succ _))
  · simp

end MOR34
