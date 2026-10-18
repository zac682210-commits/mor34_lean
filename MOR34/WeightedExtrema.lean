import MOR34.WeightedBasicQueries

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedCoordinateWitness (arith : IntegerArithmeticCharge) (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) : Counts q × ℕ :=
  let out := weightedCoordinateScan arith P R D solve ε j lower
  (out.1.getD (fun _ => 0),out.2+1)

theorem weightedCoordinateWitness_value (arith : IntegerArithmeticCharge) (P : Model m)
    (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z)
    (j : Fin q) (lower : Bool) :
    (weightedCoordinateWitness arith P R D solve ε j lower).1 =
      if lower then
        (rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).upperWitness j
      else
        (rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).lowerWitness j := by
  simpa only [weightedCoordinateWitness,weightedCoordinateScan_value,chargedCoordinateWitness]
    using chargedCoordinateWitness_value P hWF R D solve hs ε hn j lower

def weightedDenseExtrema (arith : IntegerArithmeticCharge) (P : Model m)
    (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    ParityExtrema P ε × ℕ :=
  let lo := chargedFinTable (fun j => weightedCoordinateWitness arith P R D solve ε j false)
  let hi := chargedFinTable (fun j => weightedCoordinateWitness arith P R D solve ε j true)
  let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
  have hl : lo.1 = e.lowerWitness := by
    rw [chargedFinTable_value]
    exact funext (fun j => weightedCoordinateWitness_value arith P hWF R D solve hs ε hn j false)
  have hh : hi.1 = e.upperWitness := by
    rw [chargedFinTable_value]
    exact funext (fun j => weightedCoordinateWitness_value arith P hWF R D solve hs ε hn j true)
  (extremaFromTables e lo.1 hi.1 hl hh,lo.2+hi.2+2*q+1)

theorem weightedDenseExtrema_value (arith : IntegerArithmeticCharge) (P : Model m)
    (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (weightedDenseExtrema arith P hWF R D solve hs ε hn).1 =
      rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn := by
  simp only [weightedDenseExtrema,extremaFromTables_eq]

def weightedExtremaBudget (q n L D I c H a : ℕ) : ℕ :=
  2*q*((n+1)*(weightedCellQueryBudget q n L D I c H a+q+5)+3)+2*q+3

theorem weightedDenseExtrema_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (arith : IntegerArithmeticCharge) (H a : ℕ)
    (hA : arith.Bounded (2000*(Fintype.card (Item m)+A.L+2)^4)
      (H*(2000*(Fintype.card (Item m)+A.L+2)^4)^a))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (weightedDenseExtrema arith P hWF A.R A.D solve hs ε hn).2 ≤
      weightedExtremaBudget q (Fintype.card (Item m)) A.L A.D A.I A.c H a := by
  let U := weightedCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c H a
  let W := (Fintype.card (Item m)+1)*(U+q+5)+1
  have hwit (lower : Bool) (j : Fin q) :
      (weightedCoordinateWitness arith P A.R A.D solve ε j lower).2 ≤ W := by
    have hh := weightedCoordinateScan_cost P hWF solve A arith H a hA ε j lower
    have hm := Nat.mul_le_mul_right (U+q+5) (Nat.add_le_add_right (class_size_le_items (m := m) j) 1)
    exact Nat.add_le_add_right (hh.trans hm) 1
  have hlo := chargedFinTable_cost (fun j => weightedCoordinateWitness arith P A.R A.D solve ε j false) W (hwit false)
  have hhi := chargedFinTable_cost (fun j => weightedCoordinateWitness arith P A.R A.D solve ε j true) W (hwit true)
  dsimp only [weightedDenseExtrema,weightedExtremaBudget]
  dsimp [W] at hlo hhi
  change _ ≤ 2*q*((Fintype.card (Item m)+1)*(U+q+5)+3)+2*q+3
  nlinarith

end MOR34
