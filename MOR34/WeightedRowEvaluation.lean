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
    dsimp only at hh
    unfold ConstructedIntegerRow.work
    omega
  have hcosts (j : Fin q) : (row.costs j).work ≤ row.work := by
    have hh := Finset.single_le_sum (f := fun i => (row.costs i).work)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    dsimp only at hh
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

/-- The common magnitude envelope itself has a polynomial logarithm. -/
theorem uniformRowRadius_clog (q N M : ℕ) (hN : 1 ≤ N) :
    Nat.clog 2 (uniformRowRadius q N M+2) ≤ uniformRowBits q N M := by
  let e := Nat.clog 2 N+Nat.clog 2 (M+1)+
    (Nat.clog 2 (q+1)+Nat.clog 2 N)*(q+1)+6
  have hh : uniformRowRadius q N M ≤ 2^e := uniformRowRadius_power_bound q N M hN
  have hp : 1 ≤ 2^e := Nat.one_le_pow _ _ (by decide)
  apply (Nat.le_pow_iff_clog_le (by decide)).mp
  have he : uniformRowBits q N M = e+2 := by rfl
  rw [he,pow_add]
  norm_num
  omega

theorem uniformRowRadius_dominates (q N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    N+M+normalRadius q N+3 ≤ uniformRowRadius q N M := by
  unfold uniformRowRadius
  nlinarith

/-- All three row families have at most 12(n+L+2) arithmetic nodes. Once their
literal bound is instantiated, their actual weighted evaluator has a uniform
polynomial bit-cost bound, independently of the parameter in the exponent. -/
theorem weightedEvaluateRow_polynomial {q : ℕ} (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q) (n L M H a : ℕ) (hq : q ≤ n) (hML : M ≤ 2^L)
    (hwork : row.work ≤ 12*(n+L+2))
    (hlit : row.LiteralsBounded (uniformRowRadius q (n+1) M))
    (hA : A.Bounded (170*(n+L+2)^3) (H*(170*(n+L+2)^3)^a)) :
    (weightedEvaluateRow A row).2 ≤ (12*H*170^a+5)*(n+L+2)^(3*a+1) := by
  let S := n+L+2
  change row.work ≤ 12*S at hwork
  change (weightedEvaluateRow A row).2 ≤ (12*H*170^a+5)*S^(3*a+1)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hlog : Nat.clog 2 (uniformRowRadius q (n+1) M+2) ≤ 14*S^2 :=
    (uniformRowRadius_clog q (n+1) M (by omega)).trans (uniformRowBits_polynomial q n M L hq hML)
  have hbits : row.work*Nat.clog 2 (uniformRowRadius q (n+1) M+2)+2 ≤ 170*S^3 := by
    have hh := Nat.mul_le_mul hwork hlog
    have hp : 1 ≤ S^3 := Nat.one_le_pow _ _ hS
    nlinarith
  have heval := weightedEvaluateRow_cost A row (uniformRowRadius q (n+1) M)
    (H*(170*S^3)^a) hlit (IntegerArithmeticCharge.Bounded.mono A hA hbits)
  have hmul := Nat.mul_le_mul_right (H*(170*S^3)^a) hwork
  have heq : (12*S)*(H*(170*S^3)^a) = (12*H*170^a)*S^(3*a+1) := by
    rw [mul_pow,← pow_mul,pow_succ]
    ring
  have hpow : S ≤ S^(3*a+1) := le_self_pow₀ hS (by omega)
  have hqn : q ≤ S := by dsimp [S]; omega
  have htail : 3*q+2 ≤ 5*S^(3*a+1) := by omega
  exact heval.trans (by rw [heq] at hmul; nlinarith)

end MOR34
