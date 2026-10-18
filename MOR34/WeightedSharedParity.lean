import MOR34.WeightedRowApplications
import MOR34.DensePayloadTransfer

namespace MOR34
variable {q : ℕ}

def pricedParityEntry (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) (j : Fin q) : (ℤ × ℤ) × ℕ :=
  let old := storedIntegerRead row.counts j.val
  let x := weightedEvaluateInteger A (.mul (.atom 2) (.atom old.1))
  let y := weightedEvaluateInteger A (.mul (.atom old.1) (.atom (ε j).val))
  ((x.1,y.1),old.2+x.2+y.2+4)

theorem pricedParityEntry_value (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) (j : Fin q) :
    (pricedParityEntry A row ε j).1 =
      (2*row.counts[j.val]?.getD 0,row.counts[j.val]?.getD 0*(ε j).val) := by
  simp [pricedParityEntry,weightedEvaluateInteger_value,IntegerConstruction.value,
    storedIntegerRead,chargedListRead_value]

/-- The existing dense routine's storage policy is preserved: one indexed read
per count coefficient, retained products, and a shared cost array. -/
def sharedWeightedDenseParityRow (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) : DenseIntegerRow q × ℕ :=
  let data := chargedMap (pricedParityEntry A row ε) (List.ofFn (fun j : Fin q => j))
  let total := weightedEvaluateInteger A
    (.add (.atom row.bound) (.neg (sumConstruction (data.1.map Prod.snd))))
  (⟨data.1.map Prod.fst,row.costs,total.1⟩,data.2+total.2+4*q+4)

theorem sharedWeightedDenseParityRow_value (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) :
    (sharedWeightedDenseParityRow A row ε).1 = (denseParityRow row ε).1 := by
  rw [denseParityRow_arrays]
  simp only [sharedWeightedDenseParityRow,chargedMap_value,pricedParityEntry_value,
    weightedEvaluateInteger_value,IntegerConstruction.value,sumConstruction_value,
    List.map_ofFn,Function.comp_def,List.sum_ofFn,sub_eq_add_neg]

theorem sharedWeightedDenseParityRow_cost (A : IntegerArithmeticCharge) (row : DenseIntegerRow q)
    (ε : Parity q) (M K : ℕ) (hM : 2 ≤ M) (hs : row.WellSized)
    (ha : ∀ j : Fin q, (row.counts[j.val]?.getD 0).natAbs ≤ M)
    (hd : row.bound.natAbs ≤ M)
    (hA : A.Bounded ((2*q+7)*Nat.clog 2 (M+2)+2) K) :
    (sharedWeightedDenseParityRow A row ε).2 ≤
      (8*q+4)*K+q*(q+6)+4*q+4 := by
  have hmul : A.Bounded (3*Nat.clog 2 (M+2)+2) K :=
    IntegerArithmeticCharge.Bounded.mono A hA (by gcongr; omega)
  have he (j : Fin q) : (pricedParityEntry A row ε j).2 ≤ q+5+6*K := by
    have hp : ((ε j).val : ℤ).natAbs ≤ M := by
      change (ε j).val ≤ M
      have hj := (ε j).isLt
      omega
    have hx := weightedEvaluateInteger_cost_of_literals A
      (.mul (.atom 2) (.atom (row.counts[j.val]?.getD 0))) M K
      ⟨by simpa using hM,ha j⟩ hmul
    have hy := weightedEvaluateInteger_cost_of_literals A
      (.mul (.atom (row.counts[j.val]?.getD 0)) (.atom (ε j).val)) M K
      ⟨ha j,hp⟩ hmul
    have hr := storedIntegerRead_cost row.counts j.val
    rw [hs.1] at hr
    simp only [IntegerConstruction.work] at hx hy
    dsimp only [pricedParityEntry]
    simp only [storedIntegerRead,chargedListRead_value] at hx hy ⊢
    omega
  let data := chargedMap (pricedParityEntry A row ε) (List.ofFn (fun j : Fin q => j))
  have hl : (data.1.map Prod.snd).length = q := by
    simp [data,chargedMap_value]
  have hlit : ∀ z ∈ data.1.map Prod.snd, z.natAbs ≤ M := by
    intro z hz
    simp only [data,chargedMap_value,List.map_ofFn,Function.comp_def,pricedParityEntry_value,
      List.mem_ofFn] at hz
    obtain ⟨j,rfl⟩ := hz
    have hp : (ε j).val ≤ 1 := by have hh := (ε j).isLt; omega
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,mul_one] using
      (Nat.mul_le_mul (ha j) hp)
  have hsum := weightedEvaluateInteger_cost_of_literals A
    (.add (.atom row.bound) (.neg (sumConstruction (data.1.map Prod.snd)))) M K
    ⟨hd,sumConstruction_literals _ M hlit⟩
    (IntegerArithmeticCharge.Bounded.mono A hA (by
      simp only [IntegerConstruction.work,sumConstruction_work,hl]
      gcongr <;> omega))
  simp only [IntegerConstruction.work,sumConstruction_work,hl] at hsum
  have hmap := chargedMap_cost (pricedParityEntry A row ε)
    (List.ofFn (fun j : Fin q => j)) (q+5+6*K) (fun j _ => he j)
  simp only [List.length_ofFn] at hmap
  change data.2 ≤ q*(q+5+6*K+1) at hmap
  change data.2+_+4*q+4 ≤ _
  nlinarith only [hsum,hmap]

end MOR34
