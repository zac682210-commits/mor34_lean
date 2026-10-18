import MOR34.MaterializedRowConstruction

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

/-- Count rows also use explicit prefix construction. All non-prefix literals
are input or retained query-table entries. -/
def builtCountRow (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ) (R : ℕ) :
    CountRow m r → ConstructedIntegerRow q × ℕ
  | .inr (.inr (.inl ⟨j,t⟩)) => builtPrefixRow P j t R
  | k => (countRowConstruction P A b k,12*(q+1)*(R+1))

theorem builtCountRow_value (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (R : ℕ) (k : CountRow m r) :
    (builtCountRow P A b R k).1 = countRowConstruction P A b k := by
  rcases k with (j | j) | ((u | u) | (⟨j,t⟩ | (u | i)))
  all_goals simp only [builtCountRow, countRowConstruction, builtPrefixRow_value]

theorem builtCountRow_interpret (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (R : ℕ) (k : CountRow m r) :
    (builtCountRow P A b R k).1.value =
      countRow P (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ)) k := by
  rw [builtCountRow_value, countRowConstruction_value]

/-- A quadratic scalar-access budget accommodates a flattened dense query
coefficient table. The total polynomial exponent remains independent of q. -/
theorem builtCountRow_cost (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (n R : ℕ) (hq : q ≤ n) (hm : ∀ j, m j ≤ n) (hR : R ≤ (n+1)^2)
    (k : CountRow m r) : (builtCountRow P A b R k).2 ≤ 32*(n+1)^3 := by
  have hd : 12*(q+1)*(R+1) ≤ 32*(n+1)^3 := by
    have hh := Nat.mul_le_mul (show q+1 ≤ n+1 by omega)
      (show R+1 ≤ (n+1)^2+1 by omega)
    nlinarith
  rcases k with (j | j) | ((u | u) | (⟨j,t⟩ | (u | i)))
  · exact hd
  · exact hd
  · exact hd
  · exact hd
  · have hp := chargedPrefixConstruction_cost (fun u => P.weight ⟨j,u⟩) t.val R
    have hp' := Nat.mul_le_mul (hm j) (show R+8 ≤ (n+1)^2+8 by omega)
    have hh := Nat.mul_le_mul (show q+1 ≤ n+1 by omega)
      (show R+1 ≤ (n+1)^2+1 by omega)
    dsimp only [builtCountRow, builtPrefixRow]
    nlinarith
  · exact hd
  · exact hd

theorem builtCountRows_total_cost (P : Model m) (hWF : WellFormed P)
    (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (R : ℕ) (hR : R ≤ (Fintype.card (Item m)+1)^2) (hr : r ≤ 3*q+1) :
    (∑ k : CountRow m r, (builtCountRow P A b R k).2) ≤
      192*(Fintype.card (Item m)+1)^4 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ j, m j ≤ n := fun j => class_size_le_items j
  calc
    _ ≤ ∑ _k : CountRow m r, 32*(n+1)^3 :=
      Finset.sum_le_sum (fun k _ => builtCountRow_cost P A b n R hq hm hR k)
    _ = (n+2*q+r+3)*(32*(n+1)^3) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, countRow_card]; rfl
    _ ≤ (6*(n+1))*(32*(n+1)^3) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end MOR34
