import MOR34.ChargedParityDecode

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def chargedDenseCellQuery (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) (t : IntegerQuery q) :
    Option (Counts q) × ℕ :=
  chargedDecodedRequest ε (chargedDenseCountSolve P R solve ε (t::cellQueries e.low e.high mode)) D

theorem chargedDenseCellQuery_value (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) (t : IntegerQuery q) :
    (chargedDenseCellQuery P R D solve ε e mode t).1 =
      rowCellOracle (denseCountOracle P R solve) ε e mode t := by
  simp only [chargedDenseCellQuery,chargedDecodedRequest_value,rowCellOracle,
    restrictedQueryOracle,parityListSolver,denseCountOracle]

def denseCellQueryBudget (q n L D I c : ℕ) : ℕ :=
  2048*(n+1)^4+I*(180*(n+L+2)^4)^c+q*(D+2)+3

def denseCellLoopBudget (q n L Rnormal D I c J : ℕ) : ℕ :=
  (q+1)*(chargedCellStepBudget q Rnormal (denseCellQueryBudget q n L D I c)+J+1)+1

/-- A complete charged cell loop, relative only to the dense solver, scalar
arithmetic allowances and a standard bounded-point insertion primitive. -/
def chargedDenseCellBasis (P : Model m) (R D Rnormal : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ) :
    Finset (Counts q) × ℕ :=
  chargedCellBasis (chargedDenseCellQuery P R D solve ε e mode) Rnormal put

theorem chargedDenseCellBasis_value (P : Model m) (hWF : WellFormed P) (R D Rnormal : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z)
    (mode : CellMode q) (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) :
    (chargedDenseCellBasis P R D Rnormal solve ε
      (rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn)
      mode put).1 =
    (computedCellSelection P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs)).basis ε hn mode := by
  rw [chargedDenseCellBasis,chargedCellBasis_value _ _ _ hp,computedCellSelection_basis]
  simp only [chargedDenseCellQuery_value]

theorem chargedDenseCellBasis_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (R D Rnormal I c J : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hcost : DenseSolverCostBound solve I c)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B)
    (hi : ∀ z B, B.card ≤ q+1 → BoundedCounts (m := m) z →
      (∀ x ∈ B, BoundedCounts (m := m) x) → (put z B).2 ≤ J) :
    let oracle := denseCountOracle P R solve
    let spec := denseCountOracle_spec P R solve hs
    let e := rowSearchedExtrema P hWF oracle spec ε hn
    (chargedDenseCellBasis P R D Rnormal solve ε e mode put).2 ≤
      denseCellLoopBudget q (Fintype.card (Item m)) L Rnormal D I c J := by
  dsimp only
  let e := rowSearchedExtrema P hWF (denseCountOracle P R solve)
    (denseCountOracle_spec P R solve hs) ε hn
  let query := chargedDenseCellQuery P R D solve ε e mode
  have hquery : (fun t => (query t).1) = rowCellOracle (denseCountOracle P R solve) ε e mode :=
    funext (chargedDenseCellQuery_value P R D solve ε e mode)
  have hstates := denseCellRequests_cost_on_states P hWF solve hs R I c hR hcost
    M L hM hML hw hc hb hd ε hn mode
  have hdecoded : SearchStates (linearSpanOracle (fun t => (query t).1) computedCountForms)
      (fun B => ∀ t ∈ outsideQueries (computedCountForms B),
        (query t).2 ≤ denseCellQueryBudget q (Fintype.card (Item m)) L D I c) (q+1) ∅ := by
    rw [hquery]
    apply searchStates_mono _ _ _ ?_ _ _ hstates
    intro B hB t ht
    have hh := chargedDecodedRequest_cost ε
      (chargedDenseCountSolve P R solve ε (t::cellQueries e.low e.high mode)) D
    have hreq := hB t ht
    dsimp only [query,chargedDenseCellQuery,denseCellQueryBudget]
    omega
  apply chargedCellBasis_cost_on_contained_states (parityCellSet P ε e mode) query
  · rw [hquery]
    exact rowCellOracle_spec P hWF _ (denseCountOracle_spec P R solve hs) ε e mode
  · exact hp
  · intro z B hcard hz hB
    exact hi z B hcard hz.1.1 (fun x hx => (hB hx).1.1)
  · exact hdecoded

end MOR34
