import MOR34.MaterializedCountRows
import MOR34.ViolationConstructionCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- A row-major table for at most 3q+1 extra inequalities, including its right
hand side, permits a linear read within this quadratic number of cells. -/
theorem denseQueryTable_read_bound (n q r : ℕ) (hq : q ≤ n) (hr : r ≤ 3*q+1) :
    r*(q+1)+1 ≤ 4*(n+1)^2 := by
  have h := Nat.mul_le_mul (show r ≤ 3*n+1 by omega) (show q+1 ≤ n+1 by omega)
  nlinarith

def builtViolationRow (P : Model m) (R : ℕ) : ViolationRow m → ConstructedIntegerRow q × ℕ
  | .inl k => builtCountRow P (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) R (feasibleCountRowIndex k)
  | .inr k => (violationRowConstruction P (.inr k),12*(q+1)*(R+1))

theorem builtViolationRow_value (P : Model m) (R : ℕ) (k : ViolationRow m) :
    (builtViolationRow P R k).1 = violationRowConstruction P k := by
  cases k with
  | inl k => exact builtCountRow_value P _ _ R _
  | inr k => rfl

theorem builtViolationRow_interpret (P : Model m) (R : ℕ) (k : ViolationRow m) :
    (builtViolationRow P R k).1.value = violationRow P k := by
  rw [builtViolationRow_value, violationRowConstruction_value]

theorem builtViolationRow_cost (P : Model m) (n R : ℕ) (hq : q ≤ n)
    (hm : ∀ j, m j ≤ n) (hR : R ≤ 4*(n+1)^2) (k : ViolationRow m) :
    (builtViolationRow P R k).2 ≤ 128*(n+1)^3 := by
  cases k with
  | inl k => exact builtCountRow_cost P _ _ n R hq hm hR _
  | inr k =>
      have hd := Nat.mul_le_mul (show q+1 ≤ n+1 by omega)
        (show R+1 ≤ 4*(n+1)^2+1 by omega)
      dsimp only [builtViolationRow]
      nlinarith

theorem builtViolationRows_total_cost (P : Model m) (hWF : WellFormed P)
    (R : ℕ) (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) :
    (∑ k : ViolationRow m, (builtViolationRow P R k).2) ≤
      768*(Fintype.card (Item m)+1)^4 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ j, m j ≤ n := fun j => class_size_le_items j
  calc
    _ ≤ ∑ _k : ViolationRow m, 128*(n+1)^3 :=
      Finset.sum_le_sum (fun k _ => builtViolationRow_cost P n R hq hm hR k)
    _ = (n+2*q+2)*(128*(n+1)^3) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, violationRow_card]; rfl
    _ ≤ (6*(n+1))*(128*(n+1)^3) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end MOR34
