import MOR34.AggregateArithmeticCost
import MOR34.NormalCheckIntermediates
import MOR34.DeterminantIntermediates

namespace MOR34

/-- A signed-bit envelope for minors and annihilation partial sums, including
candidate normals later rejected by the search. -/
def normalWorkBits (q n : ℕ) : ℕ :=
  (Nat.clog 2 (q+2)+Nat.clog 2 (n+1))*(q+2)+3

theorem normalWorkBits_polynomial (q n : ℕ) (hq : q ≤ n) :
    normalWorkBits q n ≤ 3*(n+2)^2 := by
  have h₁ := clog_two_le_input (q+2)
  have h₂ := clog_two_le_input (n+1)
  have h₃ : (Nat.clog 2 (q+2)+Nat.clog 2 (n+1))*(q+2) ≤
      (2*(n+2))*(n+2) := Nat.mul_le_mul (by omega) (by omega)
  unfold normalWorkBits
  nlinarith

/-- Instantiation at the augmented count-matrix dimension q+1. -/
theorem normalCheck_signed_bits {q s r : ℕ} (M : Matrix (Fin s) (Fin (q+1)) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin (q+1)) (n : ℕ)
    (hM : ∀ i j, |M i j| ≤ ((n+1 : ℕ) : ℤ))
    (i : Fin s) (j : Fin (q+1)) (S : Finset (Fin (q+1))) :
    signedIntegerBits (∑ l ∈ S, M i l * concreteColumnNormal (M.submatrix a id) c j l) ≤
      normalWorkBits q n := by
  have hh := normalCheck_partial_sum_bits M a c (n+1) (by omega) hM i j S
  simp only [show q+1+1=q+2 by omega] at hh
  unfold signedIntegerBits normalWorkBits
  omega

/-- The same envelope contains the signed bits of every Laplace partial sum
in any recursively encountered minor of dimension at most q+1. -/
theorem determinant_signed_bits {r : ℕ} (A : Matrix (Fin (r+1)) (Fin (r+1)) ℤ)
    (q n : ℕ) (hr : r+1 ≤ q+1)
    (hA : ∀ i j, |A i j| ≤ ((n+1 : ℕ) : ℤ)) (J : Finset (Fin (r+1))) :
    signedIntegerBits (∑ j ∈ J, laplaceTerm A j) ≤ normalWorkBits q n := by
  have hD : r+1 ≤ 2^(Nat.clog 2 (q+2)) := hr.trans
    ((by omega : q+1 ≤ q+2).trans ((Nat.le_pow_iff_clog_le (by decide)).mpr le_rfl))
  have hN : n+1 ≤ 2^(Nat.clog 2 (n+1)) :=
    (Nat.le_pow_iff_clog_le (by decide)).mpr le_rfl
  have hh := laplace_partial_sum_bits A (n+1) (Nat.clog 2 (q+2)) (Nat.clog 2 (n+1)) hD hN hA J
  have hm := Nat.mul_le_mul_left (Nat.clog 2 (q+2)+Nat.clog 2 (n+1))
    (show r+1 ≤ q+2 by omega)
  unfold signedIntegerBits normalWorkBits
  omega

variable {q : ℕ} {m : Fin q → ℕ}

/-- Standard integer-operation costs are supplied only at the bit envelope;
the exponent 2a in n is then derived, independently of q. This still excludes
construction/storage/indexing outside the arithmetic/comparison trace. -/
theorem counted_normal_bit_cost (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (H a perOperation : ℕ)
    (hop : perOperation ≤ H*(normalWorkBits q (Fintype.card (Item m)))^a) :
    allNormalArithmeticCharge P hWF solve hs*perOperation ≤
      ((q+4)^(6*q+13)*H*3^a)*(Fintype.card (Item m)+2)^(2*a) := by
  have hbits := normalWorkBits_polynomial q (Fintype.card (Item m))
    (coefficient_classes_le_items P hWF)
  calc
    _ ≤ (q+4)^(6*q+13)*(H*(3*(Fintype.card (Item m)+2)^2)^a) :=
      Nat.mul_le_mul (allNormalArithmeticCharge_parameter P hWF solve hs)
        (hop.trans (Nat.mul_le_mul_left _ (pow_le_pow_left' hbits a)))
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end MOR34
