import MOR34.WeightedReachedRequests
import MOR34.WeightedRemainingRequests
import MOR34.DenseCellLoop

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedDenseCountSolve (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) : Option (IntegerRowSolution q) × ℕ :=
  let request := weightedCompiledCountRequest arith P ε Q R
  let result := solve request.1
  (result.1,request.2+result.2+1)

theorem weightedDenseCountSolve_value (arith : IntegerArithmeticCharge) (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) :
    (weightedDenseCountSolve arith P R solve ε Q).1 = denseCountOracle P R solve ε Q := by
  simp only [weightedDenseCountSolve,weightedCompiledCountRequest_value,denseCountOracle,
    chargedDenseCountSolve]

def weightedDenseCellQuery (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) (t : IntegerQuery q) :
    Option (Counts q) × ℕ :=
  let restrictions := chargedCellRestrictions e.low e.high mode
  let out := chargedDecodedRequest ε (weightedDenseCountSolve arith P R solve ε (t::restrictions.1)) D
  (out.1,restrictions.2+out.2+1)

theorem weightedDenseCellQuery_value (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) (t : IntegerQuery q) :
    (weightedDenseCellQuery arith P R D solve ε e mode t).1 =
      rowCellOracle (denseCountOracle P R solve) ε e mode t := by
  simp only [weightedDenseCellQuery,chargedCellRestrictions_value,chargedDecodedRequest_value,
    weightedDenseCountSolve_value,rowCellOracle,restrictedQueryOracle,parityListSolver]

def weightedCellQueryBudget (q n L D I c H a : ℕ) : ℕ :=
  (144*H*2000^a+1260)*(n+L+2)^(4*a+4)+I*(180*(n+L+2)^4)^c+
    q*(D+2)+20*(q+1)^3+4

/-- Integer-row arithmetic is now priced inside the actual cell loop, with the
same queries, witnesses, and stopping decisions as the retained reference path.
Normal generation and collection still have their separately declared charges. -/
theorem weightedCellQuery_cost_on_states (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (R D I c M L H a : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hcost : DenseSolverCostBound solve I c)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (arith : IntegerArithmeticCharge)
    (hA : arith.Bounded (2000*(Fintype.card (Item m)+L+2)^4)
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
    SearchStates (linearSpanOracle (rowCellOracle (denseCountOracle P R solve) ε e mode) computedCountForms)
      (fun B => ∀ t ∈ outsideQueries (computedCountForms B),
        (weightedDenseCellQuery arith P R D solve ε e mode t).2 ≤
          weightedCellQueryBudget q (Fintype.card (Item m)) L D I c H a) (q+1) ∅ := by
  dsimp only
  let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
  have hlit := weightedReachedCellRequests_polynomial P hWF solve hs R M L H a hR hM hML
    (fun i => by exact_mod_cast hw i) (fun j => by exact_mod_cast hc j)
    (by exact_mod_cast hd) (by exact_mod_cast hb) arith hA ε e mode
  have hp := computedPipeline_polynomial_payload P hWF (denseCountOracle P R solve)
    (denseCountOracle_spec P R solve hs) M L hM hML hw hc hb hd ε hn mode
  have hboth := searchStates_and _ _ _ _ _ hlit hp
  apply searchStates_mono _ _ _ ?_ _ _ hboth
  intro B hB t ht
  have hbuild := hB.1 t ht
  have hsolve := actualCellSolver_cost P hWF ε e mode L B hB.2 t ht R I c solve hcost
  have hdecode := chargedDecodedRequest_cost ε
    (weightedDenseCountSolve arith P R solve ε (t::cellQueries e.low e.high mode)) D
  have hrestr := chargedCellRestrictions_cost e.low e.high mode
  dsimp only [weightedDenseCountSolve] at hdecode
  rw [weightedCompiledCountRequest_value] at hdecode
  dsimp only [weightedDenseCellQuery,weightedCellQueryBudget]
  rw [chargedCellRestrictions_value]
  dsimp only [e] at hbuild hsolve hdecode hrestr ⊢
  omega

def weightedDenseCellBasis (arith : IntegerArithmeticCharge) (P : Model m) (R D N : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ) :
    Finset (Counts q) × ℕ :=
  chargedCellBasis (weightedDenseCellQuery arith P R D solve ε e mode) N put

theorem weightedDenseCellBasis_value (arith : IntegerArithmeticCharge) (P : Model m) (R D N : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) :
    (weightedDenseCellBasis arith P R D N solve ε e mode put).1 =
      (chargedDenseCellBasis P R D N solve ε e mode put).1 := by
  simp only [weightedDenseCellBasis,chargedDenseCellBasis,chargedCellBasis_value _ _ _ hp,
    weightedDenseCellQuery_value,chargedDenseCellQuery_value]

theorem weightedDenseCellBasis_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (R D N I c J M L H a : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hcost : DenseSolverCostBound solve I c)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (arith : IntegerArithmeticCharge)
    (hA : arith.Bounded (2000*(Fintype.card (Item m)+L+2)^4)
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q)
    (put : Counts q → Finset (Counts q) → Finset (Counts q) × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B)
    (hi : ∀ z B, B.card ≤ q+1 → BoundedCounts (m := m) z →
      (∀ x ∈ B, BoundedCounts (m := m) x) → (put z B).2 ≤ J) :
    let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
    (weightedDenseCellBasis arith P R D N solve ε e mode put).2 ≤
      (q+1)*(chargedCellStepBudget q N
        (weightedCellQueryBudget q (Fintype.card (Item m)) L D I c H a)+J+1)+1 := by
  dsimp only
  let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
  have hquery : (fun t => (weightedDenseCellQuery arith P R D solve ε e mode t).1) =
      rowCellOracle (denseCountOracle P R solve) ε e mode :=
    funext (weightedDenseCellQuery_value arith P R D solve ε e mode)
  apply chargedCellBasis_cost_on_contained_states (parityCellSet P ε e mode)
  · rw [hquery]
    exact rowCellOracle_spec P hWF _ (denseCountOracle_spec P R solve hs) ε e mode
  · exact hp
  · intro z B hcard hz hB
    exact hi z B hcard hz.1.1 (fun x hx => (hB hx).1.1)
  · rw [hquery]
    exact weightedCellQuery_cost_on_states P hWF solve hs R D I c M L H a hR hcost
      hM hML hw hc hb hd arith hA ε hn mode

end MOR34
