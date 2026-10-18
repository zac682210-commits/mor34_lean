import MOR34.WeightedCellExecution
import MOR34.ChargedExtremaTable
import MOR34.DenseModeComposition

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem normalBoundedQuery_literals (t : IntegerQuery q) (n M : ℕ) (hM : 1 ≤ M)
    (h : t.Bounded (normalCoefficientBound q (n+1)+1)
      ((n+1 : ℕ)+normalCoefficientBound q (n+1)+3)) :
    (∀ j, (t.coefficient j).natAbs ≤ uniformRowRadius q (n+1) M) ∧
      t.bound.natAbs ≤ uniformRowRadius q (n+1) M := by
  have hd := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hcoef : normalCoefficientBound q (n+1)+1 ≤ (uniformRowRadius q (n+1) M : ℤ) := by
    rw [← normalRadius_cast]
    exact_mod_cast (show normalRadius q (n+1)+1 ≤ uniformRowRadius q (n+1) M by omega)
  have hbound : ((n+1 : ℕ) : ℤ)+normalCoefficientBound q (n+1)+3 ≤
      (uniformRowRadius q (n+1) M : ℤ) := by
    rw [← normalRadius_cast]
    exact_mod_cast (show n+1+normalRadius q (n+1)+3 ≤ uniformRowRadius q (n+1) M by omega)
  constructor
  · intro j
    exact_mod_cast (show ((t.coefficient j).natAbs : ℤ) ≤ (uniformRowRadius q (n+1) M : ℤ) by
      simpa only [Int.natCast_natAbs] using (h.1 j).trans hcoef)
  · exact_mod_cast (show (t.bound.natAbs : ℤ) ≤ (uniformRowRadius q (n+1) M : ℤ) by
      simpa only [Int.natCast_natAbs] using h.2.trans hbound)

def weightedDenseListQuery (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) : Option (Counts q) × ℕ :=
  chargedDecodedRequest ε (weightedDenseCountSolve arith P R solve ε Q) D

theorem weightedDenseListQuery_value (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (Q : List (IntegerQuery q)) :
    (weightedDenseListQuery arith P R D solve ε Q).1 =
      parityListSolver (denseCountOracle P R solve) ε Q := by
  simp only [weightedDenseListQuery,chargedDecodedRequest_value,weightedDenseCountSolve_value,parityListSolver]

theorem weightedDenseListQuery_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : DenseCellPrimitives P solve) (arith : IntegerArithmeticCharge) (H a : ℕ)
    (hA : arith.Bounded (2000*(Fintype.card (Item m)+A.L+2)^4)
      (H*(2000*(Fintype.card (Item m)+A.L+2)^4)^a))
    (ε : Parity q) (Q : List (IntegerQuery q)) (hQ : Q.length ≤ 3*q+1)
    (ht : ∀ t ∈ Q, t.Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3)) :
    (weightedDenseListQuery arith P A.R A.D solve ε Q).2 ≤
      weightedCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c H a := by
  have toNatAbs (z : ℤ) (hz : |z| ≤ (A.M : ℤ)) : z.natAbs ≤ A.M := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (A.M : ℤ) by simpa only [Int.natCast_natAbs] using hz)
  have hb := weightedCompiledCountRequest_polynomial P hWF ε Q A.R A.M A.L H a
    A.read_bound hQ A.magnitude_pos A.magnitude_bits
    (fun i => toNatAbs _ (A.weights i)) (fun j => toNatAbs _ (A.coefficients j))
    (toNatAbs _ A.rhs) (toNatAbs _ A.capacity)
    (fun t ht' => normalBoundedQuery_literals t _ A.M A.magnitude_pos (ht t ht')) arith hA
  have hs := boundedCountSolver_cost P hWF A.M A.L A.magnitude_pos A.magnitude_bits
    A.weights A.coefficients A.capacity A.rhs ε Q A.R A.I A.c hQ ht solve A.solver_cost
  have hd := chargedDecodedRequest_cost ε (weightedDenseCountSolve arith P A.R solve ε Q) A.D
  dsimp only [weightedDenseCountSolve] at hd
  rw [weightedCompiledCountRequest_value] at hd
  dsimp only [weightedDenseListQuery,weightedDenseCountSolve,weightedCellQueryBudget]
  rw [weightedCompiledCountRequest_value]
  omega

def weightedCoordinateQuery (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) (k : ℕ) : Option (Counts q) × ℕ :=
  let t := if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))
  let out := weightedDenseListQuery arith P R D solve ε [t]
  (out.1,out.2+q+4)

def weightedCoordinateScan (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) : Option (Counts q) × ℕ :=
  chargedDescendingSearch (weightedCoordinateQuery arith P R D solve ε j lower) (m j)

theorem weightedCoordinateScan_value (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) :
    (weightedCoordinateScan arith P R D solve ε j lower).1 =
      (chargedCoordinateScan P R D solve ε j lower).1 := by
  simp only [weightedCoordinateScan,chargedCoordinateScan,chargedDescendingSearch_value,
    weightedCoordinateQuery,chargedCoordinateQuery,weightedDenseListQuery_value,chargedDenseListQuery_value]

theorem weightedCoordinateScan_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (A : DenseCellPrimitives P solve) (arith : IntegerArithmeticCharge) (H a : ℕ)
    (hA : arith.Bounded (2000*(Fintype.card (Item m)+A.L+2)^4)
      (H*(2000*(Fintype.card (Item m)+A.L+2)^4)^a))
    (ε : Parity q) (j : Fin q) (lower : Bool) :
    (weightedCoordinateScan arith P A.R A.D solve ε j lower).2 ≤
      (m j+1)*(weightedCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c H a+q+5) := by
  let U := weightedCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c H a
  have hquery : ∀ k ≤ m j,
      (weightedCoordinateQuery arith P A.R A.D solve ε j lower k).2 ≤ U+q+4 := by
    intro k hk
    have ht : (if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))).Bounded
        (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
        ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3) := by
      cases lower
      · exact minimumScanQuery_bound P j k hk
      · exact maximumScanQuery_bound P j k hk
    have hh := weightedDenseListQuery_cost P hWF solve A arith H a hA ε
      [if lower then coordinateLower j k else coordinateUpper j ((m j : ℤ)-(k : ℤ))]
      (by simp) (by simpa only [List.mem_singleton,forall_eq] using ht)
    exact Nat.add_le_add_right hh (q+4)
  have hh := chargedDescendingSearch_cost (weightedCoordinateQuery arith P A.R A.D solve ε j lower)
    (m j) (U+q+4) hquery
  have hl := descendingSearch_calls_le
    (fun k => (weightedCoordinateQuery arith P A.R A.D solve ε j lower k).1) (m j)
  exact hh.trans (by simpa only [Nat.add_assoc] using Nat.mul_le_mul_right (U+q+4+1) hl)

end MOR34
