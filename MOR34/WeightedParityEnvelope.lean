import MOR34.WeightedDenseRequests

namespace MOR34
variable {q : ℕ}

theorem constructedRow_coordinate_work (row : ConstructedIntegerRow q) :
    (∀ j, (row.counts j).work ≤ row.work) ∧
    (∀ j, (row.costs j).work ≤ row.work) ∧ row.bound.work ≤ row.work := by
  refine ⟨?_,?_,?_⟩
  · intro j
    have h := Finset.single_le_sum (f := fun i => (row.counts i).work)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold ConstructedIntegerRow.work
    omega
  · intro j
    have h := Finset.single_le_sum (f := fun i => (row.costs i).work)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold ConstructedIntegerRow.work
    omega
  · unfold ConstructedIntegerRow.work
    omega

/-- Intermediate expressions, rather than just final rational-row data, control
all stored inputs subsequently read by parity substitution. -/
theorem evaluatedRow_magnitudes (row : ConstructedIntegerRow q) (M W : ℕ)
    (hl : row.LiteralsBounded M) (hw : row.work ≤ W) :
    (∀ j : Fin q, ((evaluateConstructedRow row).1.counts[j.val]?.getD 0).natAbs ≤ (M+2)^W) ∧
    (∀ j : Fin q, ((evaluateConstructedRow row).1.costs[j.val]?.getD 0).natAbs ≤ (M+2)^W) ∧
    (evaluateConstructedRow row).1.bound.natAbs ≤ (M+2)^W := by
  have hc := constructedRow_coordinate_work row
  have h (e : IntegerConstruction) (he : e.LiteralsBounded M) (hw' : e.work ≤ W) :
      e.value.natAbs ≤ (M+2)^W :=
    (expression_value_magnitude e M he).trans (pow_le_pow_right' (by omega) hw')
  rw [evaluateConstructedRow_arrays]
  simpa using And.intro (fun j => h (row.counts j) (hl.1 j) ((hc.1 j).trans hw))
    (And.intro (fun j => h (row.costs j) (hl.2.1 j) ((hc.2.1 j).trans hw))
      (h row.bound hl.2.2 (hc.2.2.trans hw)))

theorem expressionMagnitude_clog (M W : ℕ) :
    Nat.clog 2 ((M+2)^W+2) ≤ W*Nat.clog 2 (M+2)+2 := by
  apply (Nat.le_pow_iff_clog_le (by decide)).mp
  have h : (M+2)^W ≤ 2^(W*Nat.clog 2 (M+2)) := by
    calc
      _ ≤ (2^(Nat.clog 2 (M+2)))^W := pow_le_pow_left' (Nat.le_pow_clog (by decide) _) W
      _ = _ := by rw [← pow_mul,Nat.mul_comm]
  have hp : 1 ≤ 2^(W*Nat.clog 2 (M+2)) := Nat.one_le_pow _ _ (by decide)
  rw [pow_add]
  norm_num
  omega

/-- The price bound is local to actual arithmetic operands. Constructor reads
and index/list work remain explicit in the resulting cost. -/
theorem sharedWeightedCompileParityRow_cost (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) (M W K : ℕ)
    (hW : 1 ≤ W) (hl : row.1.LiteralsBounded M) (hw : row.1.work ≤ W)
    (hA : A.Bounded ((2*q+7)*(W*Nat.clog 2 (M+2)+2)+2) K) :
    (sharedWeightedCompileParityRow A row ε).2 ≤
      row.2+(W+8*q+4)*K+q*(q+6)+7*q+7 := by
  have hm : 2 ≤ (M+2)^W := by
    have h := le_self_pow₀ (by omega : 1 ≤ M+2) (by omega : W ≠ 0)
    omega
  have he : row.1.work*Nat.clog 2 (M+2)+2 ≤ (2*q+7)*(W*Nat.clog 2 (M+2)+2)+2 := by
    have hh := Nat.mul_le_mul_right (Nat.clog 2 (M+2)) hw
    nlinarith
  have hrow := weightedEvaluateRow_cost A row.1 M K hl
    (IntegerArithmeticCharge.Bounded.mono A hA he)
  have hmag := evaluatedRow_magnitudes row.1 M W hl hw
  have hpar := sharedWeightedDenseParityRow_cost A (evaluateConstructedRow row.1).1 ε
    ((M+2)^W) K hm (evaluateConstructedRow_sized row.1) hmag.1 hmag.2.2
    (IntegerArithmeticCharge.Bounded.mono A hA (by
      have hh := Nat.mul_le_mul_left (2*q+7) (expressionMagnitude_clog M W)
      omega))
  dsimp only [sharedWeightedCompileParityRow,weightedCompileRetainedRow]
  rw [weightedEvaluateRow_value]
  have hmul := Nat.mul_le_mul_right K hw
  nlinarith only [hrow,hpar,hmul]

end MOR34
