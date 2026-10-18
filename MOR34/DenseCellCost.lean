import MOR34.DenseSolverSize

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Construction and the solver are charged on the same materialized request.
This is an arithmetic-reference charge; bit weighting of construction is separate. -/
theorem actualCellRequest_cost (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (e : ParityExtrema P ε) (mode : CellMode q) (L : ℕ) (B : Finset (Counts q))
    (hp : PolynomialCellSearchPayload P ε e mode L B)
    (t : IntegerQuery q) (ht : t ∈ outsideQueries (computedCountForms B)) (R I c : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) :
    (chargedDenseCountSolve P R solve ε (t::cellQueries e.low e.high mode)).2 ≤
      2048*(Fintype.card (Item m)+1)^4+
        I*(180*(Fintype.card (Item m)+L+2)^4)^c+1 := by
  apply chargedDenseCountSolve_cost P hWF R solve ε _ _ hR
  · rw [List.length_cons,cellQueries_length]
  · exact actualCellSolver_cost P hWF ε e mode L B hp t ht R I c solve hcost

/-- All actual reached cell states inherit the concrete request bound. The
payload invariant is derived from solver correctness, not postulated by callers. -/
theorem denseCellRequests_cost_on_states (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (R I c : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hcost : DenseSolverCostBound solve I c)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    let oracle := denseCountOracle P R solve
    let spec := denseCountOracle_spec P R solve hs
    let e := rowSearchedExtrema P hWF oracle spec ε hn
    SearchStates (linearSpanOracle (rowCellOracle oracle ε e mode) computedCountForms)
      (fun B => ∀ t ∈ outsideQueries (computedCountForms B),
        (chargedDenseCountSolve P R solve ε (t::cellQueries e.low e.high mode)).2 ≤
          2048*(Fintype.card (Item m)+1)^4+
            I*(180*(Fintype.card (Item m)+L+2)^4)^c+1) (q+1) ∅ := by
  dsimp only
  apply searchStates_mono _
    (PolynomialCellSearchPayload P ε
      (rowSearchedExtrema P hWF (denseCountOracle P R solve)
        (denseCountOracle_spec P R solve hs) ε hn) mode L) _ ?_ _ _
    (computedPipeline_polynomial_payload P hWF (denseCountOracle P R solve)
      (denseCountOracle_spec P R solve hs) M L hM hML hw hc hb hd ε hn mode)
  intro B hp t ht
  exact actualCellRequest_cost P hWF ε _ mode L B hp t ht R I c hR solve hcost

end MOR34
