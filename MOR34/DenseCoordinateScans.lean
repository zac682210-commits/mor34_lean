import MOR34.DenseCellLoop

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def chargedDenseListQuery (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) : Option (Counts q) × ℕ :=
  chargedDecodedRequest ε (chargedDenseCountSolve P R solve ε Q) D

theorem chargedDenseListQuery_value (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) :
    (chargedDenseListQuery P R D solve ε Q).1 =
      parityListSolver (denseCountOracle P R solve) ε Q := by
  simp only [chargedDenseListQuery,chargedDecodedRequest_value,parityListSolver,denseCountOracle]

theorem chargedDenseListQuery_cost (P : Model m) (hWF : WellFormed P)
    (R D I c M L : ℕ) (hR : R ≤ 4*(Fintype.card (Item m)+1)^2)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) (ε : Parity q) (Q : List (IntegerQuery q))
    (hQ : Q.length ≤ 3*q+1)
    (ht : ∀ t ∈ Q, t.Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3)) :
    (chargedDenseListQuery P R D solve ε Q).2 ≤
      denseCellQueryBudget q (Fintype.card (Item m)) L D I c := by
  have hs := boundedCountSolver_cost P hWF M L hM hML hw hc hb hd ε Q R I c hQ ht solve hcost
  have hr := chargedDenseCountSolve_cost P hWF R solve ε Q _ hR hQ hs
  have hh := chargedDecodedRequest_cost ε (chargedDenseCountSolve P R solve ε Q) D
  dsimp only [chargedDenseListQuery,denseCellQueryBudget]
  omega

/-- The sign, threshold arithmetic and query-record allocation are charged
before the list request. The callback reads the signed unit normal. -/
def chargedCoordinateQuery (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) (k : ℕ) : Option (Counts q) × ℕ :=
  let t := if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))
  let out := chargedDenseListQuery P R D solve ε [t]
  (out.1,out.2+q+4)

def chargedCoordinateScan (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) : Option (Counts q) × ℕ :=
  chargedDescendingSearch (chargedCoordinateQuery P R D solve ε j lower) (m j)

theorem chargedCoordinateScan_value (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) :
    (chargedCoordinateScan P R D solve ε j lower).1 =
      if lower then maximumSearch (rowBaseOracle (denseCountOracle P R solve) ε) j (m j)
      else minimumSearch (rowBaseOracle (denseCountOracle P R solve) ε) j (m j) := by
  cases lower <;> simp only [chargedCoordinateScan,chargedDescendingSearch_value,
    chargedCoordinateQuery,chargedDenseListQuery_value,Bool.false_eq_true,ite_false,ite_true,
    maximumSearch,minimumSearch,rowBaseOracle,restrictedQueryOracle]

theorem chargedCoordinateScan_cost (P : Model m) (hWF : WellFormed P)
    (R D I c M L : ℕ) (hR : R ≤ 4*(Fintype.card (Item m)+1)^2)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) (ε : Parity q) (j : Fin q) (lower : Bool) :
    (chargedCoordinateScan P R D solve ε j lower).2 ≤
      (m j+1)*(denseCellQueryBudget q (Fintype.card (Item m)) L D I c+q+5) := by
  let U := denseCellQueryBudget q (Fintype.card (Item m)) L D I c
  have hquery : ∀ k ≤ m j, (chargedCoordinateQuery P R D solve ε j lower k).2 ≤ U+q+4 := by
    intro k hk
    have ht : (if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))).Bounded
        (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
        ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3) := by
      cases lower
      · exact minimumScanQuery_bound P j k hk
      · exact maximumScanQuery_bound P j k hk
    have hh := chargedDenseListQuery_cost P hWF R D I c M L hR hM hML hw hc hb hd solve hcost ε
      [if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))]
      (by simp) (by simpa only [List.mem_singleton,forall_eq] using ht)
    exact Nat.add_le_add_right hh (q+4)
  have hh := chargedDescendingSearch_cost (chargedCoordinateQuery P R D solve ε j lower)
    (m j) (U+q+4) hquery
  have hc' := descendingSearch_calls_le (fun k => (chargedCoordinateQuery P R D solve ε j lower k).1) (m j)
  exact hh.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (U+q+4+1) hc')

end MOR34
