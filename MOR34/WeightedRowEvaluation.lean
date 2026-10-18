import MOR34.WeightedIntegerEvaluation
import MOR34.RemainingRowLiterals

namespace MOR34

theorem IntegerArithmeticCharge.Bounded.mono (A : IntegerArithmeticCharge)
    {B C K : ℕ} (hA : A.Bounded C K) (hBC : B ≤ C) : A.Bounded B K := by
  exact ⟨fun z hz => hA.1 z (hz.trans hBC),
    fun x y hx hy => hA.2.1 x y (hx.trans hBC) (hy.trans hBC),
    fun x y hx hy => hA.2.2.1 x y (hx.trans hBC) (hy.trans hBC),
    fun z hz => hA.2.2.2 z (hz.trans hBC)⟩

def weightedEvaluateRow {q : ℕ} (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q) : DenseIntegerRow q × ℕ :=
  let indices := List.ofFn (fun j : Fin q => j)
  let a := chargedMap (fun j => weightedEvaluateInteger A (row.counts j)) indices
  let b := chargedMap (fun j => weightedEvaluateInteger A (row.costs j)) indices
  let c := weightedEvaluateInteger A row.bound
  (⟨a.1,b.1,c.1⟩,a.2+b.2+c.2+q+2)

theorem weightedEvaluateRow_value {q : ℕ} (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q) :
    (weightedEvaluateRow A row).1 = (evaluateConstructedRow row).1 := by
  rw [evaluateConstructedRow_arrays]
  simp only [weightedEvaluateRow,chargedMap_value,List.map_ofFn,Function.comp_def,
    weightedEvaluateInteger_value]

/-- The same dense row arrays are emitted, now charging arithmetic by operand
bit size. List allocation and index-list construction remain separately counted. -/
theorem weightedEvaluateRow_cost {q : ℕ} (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q) (M K : ℕ) (hM : row.LiteralsBounded M)
    (hA : A.Bounded (row.work*Nat.clog 2 (M+2)+2) K) :
    (weightedEvaluateRow A row).2 ≤ row.work*K+3*q+2 := by
  have hcounts (j : Fin q) : (row.counts j).work ≤ row.work := by
    have hh := Finset.single_le_sum (f := fun i => (row.counts i).work)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold ConstructedIntegerRow.work
    omega
  have hcosts (j : Fin q) : (row.costs j).work ≤ row.work := by
    have hh := Finset.single_le_sum (f := fun i => (row.costs i).work)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold ConstructedIntegerRow.work
    omega
  have hbound : row.bound.work ≤ row.work := by unfold ConstructedIntegerRow.work; omega
  have ha : ∀ j, (weightedEvaluateInteger A (row.counts j)).2 ≤ (row.counts j).work*K :=
    fun j => weightedEvaluateInteger_cost_of_literals A _ M K (hM.1 j)
      (IntegerArithmeticCharge.Bounded.mono A hA (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hcounts j)) 2))
  have hb : ∀ j, (weightedEvaluateInteger A (row.costs j)).2 ≤ (row.costs j).work*K :=
    fun j => weightedEvaluateInteger_cost_of_literals A _ M K (hM.2.1 j)
      (IntegerArithmeticCharge.Bounded.mono A hA (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hcosts j)) 2))
  have hc := weightedEvaluateInteger_cost_of_literals A row.bound M K hM.2.2
    (IntegerArithmeticCharge.Bounded.mono A hA (Nat.add_le_add_right (Nat.mul_le_mul_right _ hbound) 2))
  have hsa := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => ha j)
  have hsb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => hb j)
  rw [← Finset.sum_mul] at hsa hsb
  simp only [weightedEvaluateRow,chargedMap_cost_eq,List.map_ofFn,Function.comp_def,
    List.sum_ofFn,List.length_ofFn,ConstructedIntegerRow.work]
  nlinarith

end MOR34
