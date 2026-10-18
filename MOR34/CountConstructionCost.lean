import MOR34.IntegerConstructionTrace
import MOR34.NormalBitCost

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

def prefixRowConstruction (P : Model m) (j : Fin q) (t : Fin (m j)) :
    ConstructedIntegerRow q :=
  ⟨fun k => .atom (integerPick j (P.weight ⟨j,t⟩) k),
    fun k => .atom (integerPick j (-1) k),
    .add (.mul (.atom (P.weight ⟨j,t⟩)) (.atom t.val))
      (.neg (prefixConstruction (fun u => P.weight ⟨j,u⟩) t.val))⟩

theorem prefixRowConstruction_value (P : Model m) (j : Fin q) (t : Fin (m j)) :
    (prefixRowConstruction P j t).value =
      integerRow (integerPick j (P.weight ⟨j,t⟩)) (integerPick j (-1))
        (P.weight ⟨j,t⟩*(t.val : ℤ)-prefixCost (fun u => P.weight ⟨j,u⟩) t.val) := by
  simp only [ConstructedIntegerRow.value, prefixRowConstruction, IntegerConstruction.value,
    prefixConstruction_value, sub_eq_add_neg]

theorem prefixRowConstruction_work (P : Model m) (j : Fin q) (t : Fin (m j)) :
    (prefixRowConstruction P j t).work ≤ 2*q+2*m j+6 := by
  have hh := prefixConstruction_work (fun u => P.weight ⟨j,u⟩) t.val
  simp only [ConstructedIntegerRow.work, prefixRowConstruction, IntegerConstruction.work,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]
  omega

/-- An explicit integer expression constructor for all original count rows.
The extra A,b rows are already stored outputs of the query-construction phase. -/
def countRowConstruction (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ) :
    CountRow m r → ConstructedIntegerRow q
  | .inl (.inl j) => atomicIntegerRow (integerPick j (-1)) 0 0
  | .inl (.inr j) => atomicIntegerRow (integerPick j 1) 0 (m j)
  | .inr (.inl (.inl _)) => atomicIntegerRow P.coefficient 0 P.rhs
  | .inr (.inl (.inr _)) =>
      ⟨fun j => .neg (.atom (P.coefficient j)), fun _ => .atom 0, .neg (.atom P.rhs)⟩
  | .inr (.inr (.inl ⟨j,t⟩)) => prefixRowConstruction P j t
  | .inr (.inr (.inr (.inl _))) => atomicIntegerRow 0 (fun _ => 1) P.capacity
  | .inr (.inr (.inr (.inr i))) => atomicIntegerRow (A i) 0 (b i)

theorem countRowConstruction_value (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (k : CountRow m r) :
    (countRowConstruction P A b k).value = countRow P (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ)) k := by
  rcases k with (j | j) | ((u | u) | (⟨j,t⟩ | (u | i)))
  all_goals simp only [countRowConstruction, atomicIntegerRow_value, prefixRowConstruction_value,
    countRow, ConstructedIntegerRow.value, IntegerConstruction.value, integerRow, integerPick,
    pickCoeff]
  all_goals congr 1 <;> simp <;> push_cast <;> ring

theorem countRowConstruction_work (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (n : ℕ) (hm : ∀ j, m j ≤ n) (k : CountRow m r) :
    (countRowConstruction P A b k).work ≤ 4*q+2*n+6 := by
  rcases k with (j | j) | ((u | u) | (⟨j,t⟩ | (u | i)))
  · simp only [countRowConstruction, atomicIntegerRow_work]; omega
  · simp only [countRowConstruction, atomicIntegerRow_work]; omega
  · simp only [countRowConstruction, atomicIntegerRow_work]; omega
  · simp [countRowConstruction, ConstructedIntegerRow.work, IntegerConstruction.work]
    omega
  · exact (prefixRowConstruction_work P j t).trans (by have hh := hm j; omega)
  · simp only [countRowConstruction, atomicIntegerRow_work]; omega
  · simp only [countRowConstruction, atomicIntegerRow_work]; omega

/-- Arithmetic/read work for explicit dense row construction followed by parity
substitution; row dispatch, list storage and bit costs are separate primitives. -/
def countParityConstructionWork (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (ε : Parity q) : ℕ :=
  ∑ k : CountRow m r,
    (countRowConstruction P A b k).work +
    (parityRowConstruction
      (fun j => ((countRowConstruction P A b k).counts j).value)
      (fun j => ((countRowConstruction P A b k).costs j).value)
      (countRowConstruction P A b k).bound.value ε).work

theorem countParityConstructionWork_bound (P : Model m) (A : Fin r → Fin q → ℤ)
    (b : Fin r → ℤ) (ε : Parity q) (n : ℕ) (hm : ∀ j, m j ≤ n) :
    countParityConstructionWork P A b ε ≤
      (Fintype.card (Item m)+2*q+r+3)*(12*q+2*n+10) := by
  calc
    _ ≤ ∑ _k : CountRow m r, (12*q+2*n+10) := by
      apply Finset.sum_le_sum
      intro k _
      rw [parityRowConstruction_work]
      have hh := countRowConstruction_work P A b n hm k
      omega
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, countRow_card]

/-- Even recomputing each prefix independently yields a fixed quadratic
arithmetic/read count for every scalar cell row system. -/
theorem cellConstructionWork_polynomial (P : Model m) (A : Fin r → Fin q → ℤ)
    (b : Fin r → ℤ) (ε : Parity q) (hWF : WellFormed P) (L : ℕ) (hr : r ≤ 3*q+1) :
    countParityConstructionWork P A b ε ≤ 144*(Fintype.card (Item m)+L+2)^2 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ j, m j ≤ n := fun j => class_size_le_items j
  have hh := countParityConstructionWork_bound P A b ε n hm
  have hrows : n+2*q+r+3 ≤ 6*(n+L+2) := by omega
  have hops : 12*q+2*n+10 ≤ 24*(n+L+2) := by omega
  calc
    _ ≤ (n+2*q+r+3)*(12*q+2*n+10) := hh
    _ ≤ (6*(n+L+2))*(24*(n+L+2)) := Nat.mul_le_mul hrows hops
    _ = _ := by ring

end MOR34
