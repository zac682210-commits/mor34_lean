import MOR34.RawInputPipeline
import MOR34.CellQueryBounds
import MOR34.ForcedRowBounds
import MOR34.ViolationRowBounds

namespace MOR34
variable {n : ℕ}

def RawMagnitudeBound (a c : Fin n → ℤ) (b d M : ℤ) : Prop :=
  (∀ i, |a i| ≤ M) ∧ (∀ i, |c i| ≤ M) ∧ |b| ≤ M ∧ |d| ≤ M

theorem rawNormalization_magnitude {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (M : ℤ) (h : RawMagnitudeBound a c b d M) :
    (∀ i, |N.model.weight i| ≤ M) ∧ (∀ j, |N.model.coefficient j| ≤ M) ∧
      |N.model.capacity| ≤ M ∧ |N.model.rhs| ≤ M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [N.weight_eq]; exact h.1 _
  · intro j
    let i : Item N.sizes := ⟨j, ⟨0, N.wellFormed.2.1 j⟩⟩
    have he := N.coefficient_eq i
    change N.model.coefficient j = c (N.itemEquiv i) at he
    rw [he]
    exact h.2.1 _
  · rw [N.capacity_eq]; exact h.2.2.1
  · rw [N.rhs_eq]; exact h.2.2.2

theorem rawNormalization_class_size {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) : ∀ j, N.sizes j ≤ n := by
  have he : Fintype.card (Item N.sizes) = n := by simpa using Fintype.card_congr N.itemEquiv
  intro j
  simpa only [he] using class_size_le_items (m := N.sizes) j

/-- Original input magnitudes control every forced exchange row after grouping/sorting. -/
theorem original_forced_rows_bounded {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (M : ℤ) (hM : 1 ≤ M) (h : RawMagnitudeBound a c b d M)
    (j : Fin N.classes) (u v : Fin (N.sizes j)) (k : ForcedRow N.sizes j u v) :
    (forcedRow N.model j u v k).IntegerBounded (M+1) 1 (rowConstantBound n M 0) := by
  obtain ⟨hw, hc, hb, hd⟩ := rawNormalization_magnitude N M h
  exact forcedRows_integer_bounded N.model n M hM (rawNormalization_class_size N) hw hc hb hd j u v k

theorem original_violation_rows_bounded {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (M : ℤ) (hM : 1 ≤ M) (h : RawMagnitudeBound a c b d M)
    (k : ViolationRow N.sizes) :
    (violationRow N.model k).IntegerBounded (M+1) 1 (rowConstantBound n M 0) := by
  obtain ⟨hw, hc, hb, hd⟩ := rawNormalization_magnitude N M h
  exact violationRows_integer_bounded N.model n M hM (rawNormalization_class_size N) hw hc hb hd k

theorem original_parity_rows_bounded {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (M C D : ℤ) (hM : 1 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : RawMagnitudeBound a c b d M) (L : List (IntegerQuery N.classes))
    (hL : ∀ t ∈ L, t.Bounded C D) (ε : Parity N.classes) (k : CountRow N.sizes L.length) :
    ((countRow N.model (queryCoefficients L) (queryBounds L) k).withParity ε).IntegerBounded
      (2*(M+C+1)) 1 (rowConstantBound n M D + N.classes*(M+C+1)) := by
  obtain ⟨hw, hc, hb, hd⟩ := rawNormalization_magnitude N M h
  exact parityRows_integer_bounded N.model n M C D hM hC hD (rawNormalization_class_size N)
    hw hc hb hd L hL ε k

end MOR34
