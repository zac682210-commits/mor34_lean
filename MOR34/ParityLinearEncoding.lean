import MOR34.LinearEncoding

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

/-- Substitute z=2v+epsilon in a row without adding integer variables. -/
def CountInequality.withParity (L : CountInequality q) (ε : Fin q → Fin 2) : CountInequality q :=
  ⟨fun j => L.counts j * 2, L.costs,
    L.bound - ∑ j, L.counts j * ((ε j).val : ℚ)⟩

theorem row_parity_iff (L : CountInequality q) (ε : Fin q → Fin 2) (v y : Fin q → ℤ) :
    (L.withParity ε).Holds v y ↔ L.Holds (paritySubstitution ε v) y := by
  have he : (∑ j, L.counts j * ((paritySubstitution ε v j : ℤ) : ℚ)) =
      (∑ j, (L.counts j * 2) * (v j : ℚ)) +
      ∑ j, L.counts j * ((ε j).val : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [paritySubstitution, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast]
    ring
  unfold CountInequality.Holds CountInequality.withParity
  rw [he]
  constructor <;> intro h <;> linarith

theorem exact_parity_linear_count_encoding (P : Model m) (hWF : WellFormed P)
    (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ) (ε : Fin q → Fin 2) :
    (∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧
      (∀ j, z j % 2 = (ε j).val) ∧ RationalRestrictions A b (encodeCounts z)) ↔
    ∃ v y : Fin q → ℤ, ∀ k : CountRow m r,
      ((countRow P A b k).withParity ε).Holds v y := by
  rw [parity_restricted_epigraph P hWF ε (RationalRestrictions A b)]
  simp only [row_parity_iff, countRows_iff]

end MOR34
