import MOR34.ComputedCellPipeline
import MOR34.SearchPayload

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Bit bounds for the integer forms returned by the executable finite search. -/
theorem computedCountForms_bits (B : Finset (Counts q)) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ N) :
    ∀ f ∈ computedCountForms B,
      magnitudeBits f.constant ≤ (Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1)+2 ∧
      ∀ j, magnitudeBits (f.coefficient j) ≤ (Nat.clog 2 (q+1) + Nat.clog 2 N)*(q+1)+2 := by
  intro f hf
  have hb := computedCountForms_bound B N hN hB f hf
  exact ⟨normalCoefficient_magnitudeBits _ q N hb.1,
    fun j => normalCoefficient_magnitudeBits _ q N (hb.2 j)⟩

/-- This generic row bound applies to any bounded normal family. -/
theorem forms_cell_queries_bound (l h : Counts q) (mode : CellMode q) (N : ℕ)
    (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N)
    (forms : List (IntegerForm q)) (hf : FormsBounded forms N)
    (a : IntegerQuery q) (ha : a ∈ outsideQueries forms) :
    ∀ t ∈ a :: cellQueries l h mode,
      t.Bounded (normalCoefficientBound q N + 1) ((N : ℤ)+normalCoefficientBound q N+3) := by
  have hH : (0 : ℤ) ≤ normalCoefficientBound q N := by unfold normalCoefficientBound; positivity
  intro t ht
  rcases List.mem_cons.mp ht with he | ht
  · subst t
    exact integerQuery_bound_mono a (outsideQueries_bound forms N hf a ha) (by omega) (by omega)
  · exact integerQuery_bound_mono t (cellQueries_bound l h mode N hl hh t ht) (by omega) (by omega)

theorem forms_cell_system_payload (P : Model m)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : q ≤ N) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (l h : Counts q) (mode : CellMode q) (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N)
    (forms : List (IntegerForm q)) (hf : FormsBounded forms N)
    (t : IntegerQuery q) (ht : t ∈ outsideQueries forms) (ε : Parity q) :
    ∃ a b : CountRow m (t :: cellQueries l h mode).length → Fin q → ℤ,
      ∃ d : CountRow m (t :: cellQueries l h mode).length → ℤ,
      (∀ k, (countRow P (queryCoefficients (t :: cellQueries l h mode))
        (queryBounds (t :: cellQueries l h mode)) k).withParity ε = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+5*q+4)*((2*q+1)*uniformRowBits q N M) := by
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hrows := parityRows_integer_bounded P N M
    (normalCoefficientBound q N+1) ((N : ℤ)+normalCoefficientBound q N+3) hM'
    (by unfold normalCoefficientBound; positivity) (by unfold normalCoefficientBound; positivity)
    hm hw hc hb hd (t :: cellQueries l h mode) (forms_cell_queries_bound l h mode N hl hh forms hf t ht) ε
  have hp := uniform_system_payload
    (fun k : CountRow m (t :: cellQueries l h mode).length =>
      (countRow P (queryCoefficients (t :: cellQueries l h mode))
        (queryBounds (t :: cellQueries l h mode)) k).withParity ε) N M hN
    (fun k => cellRow_uniform_bound _ N M hN hM hq (hrows k))
  simpa only [cell_solver_row_count] using hp

def ComputedCellSearchPayload (P : Model m) (ε : Parity q) (e : ParityExtrema P ε)
    (mode : CellMode q) (N M : ℕ) (B : Finset (Counts q)) : Prop :=
  ∀ t ∈ outsideQueries (computedCountForms B),
    ∃ a b : CountRow m (t :: cellQueries e.low e.high mode).length → Fin q → ℤ,
      ∃ d : CountRow m (t :: cellQueries e.low e.high mode).length → ℤ,
      (∀ k, (countRow P (queryCoefficients (t :: cellQueries e.low e.high mode))
        (queryBounds (t :: cellQueries e.low e.high mode)) k).withParity ε = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+5*q+4)*((2*q+1)*uniformRowBits q N M)

theorem computedCellSearch_payload_states (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : q ≤ N) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) :
    SearchStates (linearSpanOracle (rowCellOracle solve ε e mode) computedCountForms)
      (ComputedCellSearchPayload P ε e mode N M) (q+1) ∅ := by
  have hor := linearSpanOracle_spec (parityCellSet P ε e mode) (rowCellOracle solve ε e mode)
    (rowCellOracle_spec P hWF solve hs ε e mode) computedCountForms computedCountForms_spec
  apply searchStates_of_containment (parityCellSet P ε e mode) _ (fun B z hz => (hor.found B z hz).1)
  · intro B hB t ht
    apply forms_cell_system_payload P N M hN hM hq hm hw hc hb hd e.low e.high mode
    · intro j
      rw [← e.lower_eq j]
      exact ((e.lower_mem j).1 j).trans (hm j)
    · intro j
      rw [← e.upper_eq j]
      exact ((e.upper_mem j).1 j).trans (hm j)
    · exact computedCountForms_bound B N hN (fun z hz j => ((hB hz).1.1 j).trans (hm j))
    · exact ht
  · simp

theorem computedNormalPipeline_payload_states (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    SearchStates
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) computedCountForms)
      (ComputedCellSearchPayload P ε (rowSearchedExtrema P hWF solve hs ε hn) mode
        (Fintype.card (Item m)+1) M) (q+1) ∅ :=
  computedCellSearch_payload_states P hWF solve hs ε _ mode _ M (by omega) hM
    ((coefficient_classes_le_items P hWF).trans (Nat.le_succ _))
    (fun j => (class_size_le_items j).trans (Nat.le_succ _)) hw hc hb hd

end MOR34
