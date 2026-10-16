import Mathlib.Tactic

/-!
Small arithmetic proof candidates. These scripts have NOT been compiled in this
checkpoint. Their existence is not a certificate for the combinatorial lemma.
-/

namespace MOR34

/-- Only one repartition needs to stay feasible. -/
theorem one_feasible_of_pair_sum (s t u v b : ℤ)
    (hs : s ≤ b) (ht : t ≤ b) (hpair : u + v = s + t) :
    u ≤ b ∨ v ≤ b := by
  omega

/-- Equal candidate values of the two balanced outputs imply tightness. -/
theorem balanced_values_are_tight (s t u v d : ℤ)
    (hs : s = d) (ht : t = d) (huv : u = v)
    (hpair : u + v = s + t) : u = d ∧ v = d := by
  omega

/-- Interior cuts leave at least two positions on each side. -/
theorem interior_cut_arithmetic (l r h : ℕ)
    (hlr : l + 2 ≤ r) (hrh : r + 2 ≤ h) :
    2 ≤ r - l ∧ 2 ≤ h - r ∧ 4 ≤ h - l := by
  omega

end MOR34
