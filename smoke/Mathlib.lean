import Mathlib.Tactic
-- Gate 3: Mathlib tactic import and one elementary proof.
theorem mor34_mathlib_smoke (a b : Int) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  omega
#print axioms mor34_mathlib_smoke
