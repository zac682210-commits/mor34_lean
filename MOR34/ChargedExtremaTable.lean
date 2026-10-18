import MOR34.DenseCoordinateScans

namespace MOR34

/-- Build a table from charged callbacks; subsequent indexing uses retained
entries. Construction of the index list is charged separately. -/
def chargedFinTable {α : Type*} {q : ℕ} (f : Fin q → α × ℕ) : (Fin q → α) × ℕ :=
  let out := chargedMap f (List.ofFn (fun j : Fin q => j))
  have hlen : out.1.length = q := by simp [out,chargedMap_value]
  (fun j => out.1[j.val]'(by rw [hlen]; exact j.isLt),out.2+q+1)

theorem chargedFinTable_value {α : Type*} {q : ℕ} (f : Fin q → α × ℕ) :
    (chargedFinTable f).1 = fun j => (f j).1 := by
  funext j
  simp [chargedFinTable,chargedMap_value,List.map_ofFn]

theorem chargedFinTable_cost {α : Type*} {q : ℕ} (f : Fin q → α × ℕ)
    (C : ℕ) (hc : ∀ j, (f j).2 ≤ C) :
    (chargedFinTable f).2 ≤ q*(C+2)+1 := by
  have hh := chargedMap_cost f (List.ofFn (fun j : Fin q => j)) C (fun j _ => hc j)
  simp only [List.length_ofFn] at hh
  dsimp only [chargedFinTable]
  nlinarith

variable {q : ℕ} {m : Fin q → ℕ}

def chargedCoordinateWitness (P : Model m) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (j : Fin q) (lower : Bool) : Counts q × ℕ :=
  let out := chargedCoordinateScan P R D solve ε j lower
  (out.1.getD (fun _ => 0),out.2+1)

theorem chargedCoordinateWitness_value (P : Model m) (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z)
    (j : Fin q) (lower : Bool) :
    (chargedCoordinateWitness P R D solve ε j lower).1 =
      if lower then
        (rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).upperWitness j
      else
        (rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).lowerWitness j := by
  let oracle := rowBaseOracle (denseCountOracle P R solve) ε
  let spec := rowBaseOracle_spec P hWF _ (denseCountOracle_spec P R solve hs) ε
  cases lower
  · simp only [chargedCoordinateWitness,chargedCoordinateScan_value,Bool.false_eq_true,ite_false]
    rw [show minimumSearch (rowBaseOracle (denseCountOracle P R solve) ε) j (m j) =
      some ((rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).lowerWitness j) from
        searchedParityExtrema_lower_result P ε oracle spec hn j]
    rfl
  · simp only [chargedCoordinateWitness,chargedCoordinateScan_value,ite_true]
    rw [show maximumSearch (rowBaseOracle (denseCountOracle P R solve) ε) j (m j) =
      some ((rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn).upperWitness j) from
        searchedParityExtrema_upper_result P ε oracle spec hn j]
    rfl

/-- Rebuild the record from the returned tables. The old record occurs only in
proof fields; it does not re-run the pure extremum searches at execution time. -/
def extremaFromTables {P : Model m} {ε : Parity q} (e : ParityExtrema P ε)
    (lo hi : Fin q → Counts q) (hl : lo = e.lowerWitness) (hh : hi = e.upperWitness) :
    ParityExtrema P ε := {
  low := fun j => lo j j
  high := fun j => hi j j
  lowerWitness := lo
  upperWitness := hi
  lower_mem := fun j => by simpa only [hl] using e.lower_mem j
  upper_mem := fun j => by simpa only [hh] using e.upper_mem j
  lower_eq := fun _ => rfl
  upper_eq := fun _ => rfl
  bounds := fun z hz j => by simpa only [hl,hh,e.lower_eq,e.upper_eq] using e.bounds z hz j
}

theorem extremaFromTables_eq {P : Model m} {ε : Parity q} (e : ParityExtrema P ε)
    (lo hi : Fin q → Counts q) (hl : lo = e.lowerWitness) (hh : hi = e.upperWitness) :
    extremaFromTables e lo hi hl hh = e := by
  have hlow : (fun j => e.lowerWitness j j) = e.low := funext e.lower_eq
  have hhigh : (fun j => e.upperWitness j j) = e.high := funext e.upper_eq
  subst lo
  subst hi
  cases e
  dsimp at hlow hhigh ⊢
  cases hlow
  cases hhigh
  rfl

def chargedDenseExtrema (P : Model m) (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    ParityExtrema P ε × ℕ :=
  let lo := chargedFinTable (fun j => chargedCoordinateWitness P R D solve ε j false)
  let hi := chargedFinTable (fun j => chargedCoordinateWitness P R D solve ε j true)
  let e := rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn
  have hl : lo.1 = e.lowerWitness := by
    rw [chargedFinTable_value]
    exact funext (fun j => chargedCoordinateWitness_value P hWF R D solve hs ε hn j false)
  have hh : hi.1 = e.upperWitness := by
    rw [chargedFinTable_value]
    exact funext (fun j => chargedCoordinateWitness_value P hWF R D solve hs ε hn j true)
  (extremaFromTables e lo.1 hi.1 hl hh,lo.2+hi.2+2*q+1)

theorem chargedDenseExtrema_value (P : Model m) (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (chargedDenseExtrema P hWF R D solve hs ε hn).1 =
      rowSearchedExtrema P hWF (denseCountOracle P R solve) (denseCountOracle_spec P R solve hs) ε hn := by
  simp only [chargedDenseExtrema,extremaFromTables_eq]

theorem chargedDenseExtrema_cost (P : Model m) (hWF : WellFormed P)
    (R D I c M L : ℕ) (hR : R ≤ 4*(Fintype.card (Item m)+1)^2)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (hcost : DenseSolverCostBound solve I c)
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) :
    (chargedDenseExtrema P hWF R D solve hs ε hn).2 ≤
      2*q*((Fintype.card (Item m)+1)*
        (denseCellQueryBudget q (Fintype.card (Item m)) L D I c+q+5)+3)+2*q+3 := by
  let U := denseCellQueryBudget q (Fintype.card (Item m)) L D I c
  let W := (Fintype.card (Item m)+1)*(U+q+5)+1
  have hwit (lower : Bool) (j : Fin q) : (chargedCoordinateWitness P R D solve ε j lower).2 ≤ W := by
    have hh := chargedCoordinateScan_cost P hWF R D I c M L hR hM hML hw hc hb hd solve hcost ε j lower
    have hm := Nat.mul_le_mul_right (U+q+5) (Nat.add_le_add_right (class_size_le_items (m := m) j) 1)
    exact Nat.add_le_add_right (hh.trans hm) 1
  have hlo := chargedFinTable_cost (fun j => chargedCoordinateWitness P R D solve ε j false) W (hwit false)
  have hhi := chargedFinTable_cost (fun j => chargedCoordinateWitness P R D solve ε j true) W (hwit true)
  dsimp only [chargedDenseExtrema]
  dsimp [W] at hlo hhi
  change _ ≤ 2*q*((Fintype.card (Item m)+1)*(U+q+5)+3)+2*q+3
  nlinarith

end MOR34
