import MOR34.WeightedRowApplications
import MOR34.DensePayloadTransfer

namespace MOR34
variable {q : ℕ}

/-- A bit-priced implementation of parity substitution on retained dense rows.
Unlike substitution into the original expression, this reads stored entries. -/
def weightedDenseParityRow (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) : DenseIntegerRow q × ℕ :=
  weightedEvaluateRow A (parityRowConstruction
    (fun j => row.counts[j.val]?.getD 0) (fun j => row.costs[j.val]?.getD 0) row.bound ε)

theorem weightedDenseParityRow_value (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) (hs : row.WellSized) :
    (weightedDenseParityRow A row ε).1 = (denseParityRow row ε).1 := by
  rw [weightedDenseParityRow,weightedEvaluateRow_value,evaluateConstructedRow_arrays,denseParityRow_arrays]
  simp only [parityRowConstruction,IntegerConstruction.value,construction_fold_value,
    List.map_ofFn,List.sum_ofFn,Function.comp_def,sub_eq_add_neg]
  congr 1
  · congr 1
    funext j
    ring
  · exact storedList_ofFn row.costs q hs.2

theorem weightedDenseParityRow_polynomial (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) (n L M H a : ℕ) (hq : q ≤ n) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (ha : ∀ j : Fin q, (row.counts[j.val]?.getD 0).natAbs ≤ uniformRowRadius q (n+1) M)
    (hb : ∀ j : Fin q, (row.costs[j.val]?.getD 0).natAbs ≤ uniformRowRadius q (n+1) M)
    (hd : row.bound.natAbs ≤ uniformRowRadius q (n+1) M)
    (hA : A.Bounded (170*(n+L+2)^3) (H*(170*(n+L+2)^3)^a)) :
    (weightedDenseParityRow A row ε).2 ≤ (12*H*170^a+5)*(n+L+2)^(3*a+1) := by
  apply weightedEvaluateRow_polynomial A _ n L M H a hq hML
  · rw [parityRowConstruction_work]
    omega
  · apply parityRowConstruction_literals _ _ _ ε _ _ ha hb hd
    have h := uniformRowRadius_dominates q (n+1) M (by omega) hM
    omega
  · exact hA

/-- Compiling the original expression and parity transformation with actual
operand-based prices gives exactly the dense rows used by the solver. -/
def weightedCompileParityRow (A : IntegerArithmeticCharge) (row : ConstructedIntegerRow q × ℕ)
    (ε : Parity q) : DenseIntegerRow q × ℕ :=
  let original := weightedEvaluateRow A row.1
  let out := weightedDenseParityRow A original.1 ε
  (out.1,row.2+original.2+out.2+1)

theorem weightedCompileParityRow_value (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) :
    (weightedCompileParityRow A row ε).1 = (compileParityRow row ε).1 := by
  simp only [weightedCompileParityRow,weightedEvaluateRow_value]
  rw [weightedDenseParityRow_value A _ ε (evaluateConstructedRow_sized _)]
  rfl

end MOR34
