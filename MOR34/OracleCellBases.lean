import MOR34.BasisIndependence

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Instantiate the original cell-selection contract with the actual recursive count search.
Extrema and linear feasibility remain supplied inputs with their original specifications. -/
theorem oracle_cell_basis_selection (P : Model m)
    (ex : (ε : Parity q) → (∃ z, TightParity P ε z) → ParityExtrema P ε)
    (solve : (ε : Parity q) → (hn : ∃ z, TightParity P ε z) →
      CellMode q → IntegerQuery q → Option (Counts q))
    (hs : ∀ ε hn mode, LinearOracleSpec (parityCellSet P ε (ex ε hn) mode) (solve ε hn mode)) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q), ∃ S : CellBasisSelection P,
      S.extrema = ex ∧
      (∀ ε hn mode, S.basis ε hn mode =
        basisSearch (linearSpanOracle (solve ε hn mode) forms) (q + 1) ∅) ∧
      (∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) ∧
      (∀ ε hn mode, AffineIndependent ℝ (fun z : S.basis ε hn mode => countReal z.val)) ∧
      (∀ ε hn mode, linearBasisCalls (solve ε hn mode) forms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2) := by
  classical
  obtain ⟨forms, hf, hsize⟩ := bounded_integer_forms_family (q := q)
  let B := fun ε hn mode => basisSearch (linearSpanOracle (solve ε hn mode) forms) (q + 1) ∅
  have hc := fun ε hn mode => linear_count_basis_correct
    (parityCellSet P ε (ex ε hn) mode) (solve ε hn mode) (hs ε hn mode) forms hf hsize
  let S : CellBasisSelection P := {
    extrema := ex
    basis := B
    contained := fun ε hn mode => (hc ε hn mode).1
    spanning := fun ε hn mode z hz =>
      countReal_affineSpan_of_rational_span _ z ((hc ε hn mode).2.2.1 z hz)
  }
  refine ⟨forms, S, rfl, (by intros; rfl), ?_, ?_, ?_⟩
  · exact fun ε hn mode => (hc ε hn mode).2.1
  · intro ε hn mode
    exact real_count_search_independent _ _
      (linearSpanOracle_spec _ _ (hs ε hn mode) forms hf)
  · exact fun ε hn mode => (hc ε hn mode).2.2.2

end MOR34
