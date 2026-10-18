import MOR34.ForcedConstructionCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def violationRowConstruction (P : Model m) : ViolationRow m → ConstructedIntegerRow q
  | .inl k => countRowConstruction P (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (feasibleCountRowIndex k)
  | .inr _ => ⟨fun j => .neg (.atom (P.coefficient j)), fun _ => .atom 0,
      .neg (.add (.atom P.rhs) (.atom 1))⟩

theorem violationRowConstruction_value (P : Model m) (k : ViolationRow m) :
    (violationRowConstruction P k).value = violationRow P k := by
  cases k with
  | inl k =>
    rw [violationRowConstruction, countRowConstruction_value, violationRow,
      feasibleRow_as_countRow]
    congr 1 <;> funext i <;> exact Fin.elim0 i
  | inr u => rfl

theorem violationRowConstruction_work (P : Model m) (n : ℕ) (hm : ∀ j, m j ≤ n)
    (k : ViolationRow m) : (violationRowConstruction P k).work ≤ 4*q+2*n+6 := by
  cases k with
  | inl k => exact countRowConstruction_work P _ _ n hm _
  | inr u => simp [violationRowConstruction, ConstructedIntegerRow.work,
      IntegerConstruction.work] <;> omega

theorem violationConstructionWork_polynomial (P : Model m) (hWF : WellFormed P) (L : ℕ) :
    (∑ k : ViolationRow m, (violationRowConstruction P k).work) ≤
      144*(Fintype.card (Item m)+L+2)^2 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  calc
    _ ≤ ∑ _k : ViolationRow m, (4*q+2*n+6) :=
      Finset.sum_le_sum (fun k _ => violationRowConstruction_work P n hm k)
    _ = (n+2*q+2)*(4*q+2*n+6) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, violationRow_card]
    _ ≤ (6*(n+L+2))*(24*(n+L+2)) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

end MOR34
