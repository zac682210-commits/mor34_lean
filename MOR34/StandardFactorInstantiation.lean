import MOR34.StrongPreparationCost

namespace MOR34

/-- The cited fixed-dimensional feasibility factor at dimension 2q is of the
required q^{O(q)} form. Constants are fixed before q. -/
theorem doubled_dimension_factor (C : ℕ) :
    ParameterGrowth (fun q => (2*q+2)^(C*(2*q+2))) := by
  refine ⟨4*C,fun q => ?_⟩
  have hb : 2*q+2 ≤ (q+6)^2 := by nlinarith
  calc
    _ ≤ ((q+6)^2)^(C*(2*q+2)) := pow_le_pow_left' hb _
    _ = (q+6)^((4*C)*(q+1)) := by rw [← pow_mul]; congr 1; ring

/-- The same global integer envelope covers the minors, normal dot products
and their partial sums at all reached count matrices. -/
theorem normal_envelope_from_global {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    (hWF : WellFormed P) (L H a : ℕ) (arith : IntegerArithmeticCharge)
    (h : arith.Bounded (2000*(Fintype.card (Item m)+L+2)^4)
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a)) :
    arith.Bounded (normalWorkBits q (Fintype.card (Item m)))
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a) := by
  have hn := normalWorkBits_polynomial q (Fintype.card (Item m)) (coefficient_classes_le_items P hWF)
  have hs : (Fintype.card (Item m)+2)^2 ≤ (Fintype.card (Item m)+L+2)^4 :=
    (pow_le_pow_left' (by omega) 2).trans (pow_le_pow_right' (by omega) (by decide))
  exact IntegerArithmeticCharge.Bounded.mono arith h (by omega)

/-- The common normal instruction allowance has an input-polynomial degree
independent of the number of coefficient classes. -/
theorem normal_instruction_price_polynomial (n L H a : ℕ) :
    H*(2000*(n+L+2)^4)^a = H*2000^a*(n+L+2)^(4*a) := by
  rw [mul_pow,← pow_mul]
  ring

end MOR34
