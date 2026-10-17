import MOR34.LinearEncoding
import MOR34.CountValidation

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Feasible count profiles: no candidate-equality restriction. -/
def FeasibleCountEpigraph (P : Model m) (z y : Fin q → ℤ) : Prop :=
  IntegerCountBounds (m := m) z ∧
  (∀ j (t : Fin (m j)), prefixLine (fun u => P.weight ⟨j, u⟩) t (z j) ≤ y j) ∧
  (∑ j, y j) ≤ P.capacity

abbrev FeasibleRow (m : Fin q → ℕ) := (Fin q ⊕ Fin q) ⊕ (Item m ⊕ Unit)

def feasibleRow (P : Model m) : FeasibleRow m → CountInequality q
  | Sum.inl (Sum.inl j) => ⟨pickCoeff j (-1), 0, 0⟩
  | Sum.inl (Sum.inr j) => ⟨pickCoeff j 1, 0, (m j : ℚ)⟩
  | Sum.inr (Sum.inl ⟨j, t⟩) =>
      ⟨pickCoeff j (P.weight ⟨j, t⟩), pickCoeff j (-1),
        (P.weight ⟨j, t⟩ : ℚ) * (t.val : ℚ) -
          (prefixCost (fun u => P.weight ⟨j, u⟩) t.val : ℚ)⟩
  | Sum.inr (Sum.inr _) => ⟨0, fun _ => 1, P.capacity⟩

theorem feasibleRows_iff (P : Model m) (z y : Fin q → ℤ) :
    (∀ k : FeasibleRow m, (feasibleRow P k).Holds z y) ↔ FeasibleCountEpigraph P z y := by
  constructor
  · intro h
    have hl (j : Fin q) := h (Sum.inl (Sum.inl j))
    have hu (j : Fin q) := h (Sum.inl (Sum.inr j))
    have hc := h (Sum.inr (Sum.inr ()))
    simp only [feasibleRow, CountInequality.Holds, pickCoeff_sum, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul, one_mul, zero_add] at hl hu hc
    refine ⟨?_, ?_, ?_⟩
    · intro j
      constructor
      · have hh : (0 : ℚ) ≤ (z j : ℚ) := by linarith [hl j]
        exact_mod_cast hh
      · exact_mod_cast hu j
    · intro j t
      apply (prefixLine_rational_iff _ t _ _).mpr
      have hh := h (Sum.inr (Sum.inl ⟨j, t⟩))
      simpa only [feasibleRow, CountInequality.Holds, pickCoeff_sum, neg_one_mul, sub_eq_add_neg] using hh
    · exact_mod_cast hc
  · rintro ⟨hb, hp, hc⟩ k
    rcases k with (j | j) | (⟨j, t⟩ | u)
    · have hh : (0 : ℚ) ≤ (z j : ℚ) := by exact_mod_cast (hb j).1
      simp only [feasibleRow, CountInequality.Holds, pickCoeff_sum, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul]
      linarith
    · have hh : (z j : ℚ) ≤ (m j : ℚ) := by exact_mod_cast (hb j).2
      simpa [feasibleRow, CountInequality.Holds, pickCoeff_sum] using hh
    · have hh := (prefixLine_rational_iff _ t _ _).mp (hp j t)
      simpa only [feasibleRow, CountInequality.Holds, pickCoeff_sum, neg_one_mul, sub_eq_add_neg] using hh
    · have hh : (∑ j, (y j : ℚ)) ≤ (P.capacity : ℚ) := by exact_mod_cast hc
      simpa [feasibleRow, CountInequality.Holds] using hh

/-- The validity branch adds a violation inequality to feasible rows, never to tight rows. -/
def violationInequality (P : Model m) : CountInequality q :=
  ⟨fun j => -(P.coefficient j : ℚ), 0, -((P.rhs : ℚ) + 1)⟩

theorem violationInequality_iff (P : Model m) (z y : Fin q → ℤ) :
    (violationInequality P).Holds z y ↔ P.rhs + 1 ≤ ∑ j, P.coefficient j * z j := by
  simp only [violationInequality, CountInequality.Holds, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, neg_mul, Finset.sum_neg_distrib]
  have he : - (∑ j, (P.coefficient j : ℚ) * (z j : ℚ)) ≤ -((P.rhs : ℚ) + 1) ↔
      (P.rhs : ℚ) + 1 ≤ ∑ j, (P.coefficient j : ℚ) * (z j : ℚ) := by constructor <;> intro h <;> linarith
  rw [he]
  constructor <;> intro h <;> exact_mod_cast h

abbrev ViolationRow (m : Fin q → ℕ) := FeasibleRow m ⊕ Unit

def violationRow (P : Model m) : ViolationRow m → CountInequality q
  | Sum.inl k => feasibleRow P k
  | Sum.inr _ => violationInequality P

theorem violationRows_iff (P : Model m) (z y : Fin q → ℤ) :
    (∀ k : ViolationRow m, (violationRow P k).Holds z y) ↔
      FeasibleCountEpigraph P z y ∧ P.rhs + 1 ≤ ∑ j, P.coefficient j * z j := by
  constructor
  · intro h
    exact ⟨(feasibleRows_iff P z y).mp (fun k => h (Sum.inl k)),
      (violationInequality_iff P z y).mp (h (Sum.inr ()))⟩
  · rintro ⟨hf, hv⟩ k
    cases k with
    | inl k => exact (feasibleRows_iff P z y).mpr hf k
    | inr u => exact (violationInequality_iff P z y).mpr hv

theorem feasibleEpigraph_decode (P : Model m) (hWF : WellFormed P) (z y : Fin q → ℤ)
    (h : FeasibleCountEpigraph P z y) :
    BoundedCounts (m := m) (decodeCounts z) ∧ Feasible P (prefixSet (decodeCounts z)) := by
  have hb := decodeCounts_bounded z h.1
  have he := encode_decodeCounts z h.1
  refine ⟨hb, (prefix_feasible_epigraph P hWF _ hb).mpr ⟨y, ?_, h.2.2⟩⟩
  intro j t
  have hh := h.2.1 j t
  have hj := congrFun he j
  change ((decodeCounts z j : ℕ) : ℤ) = z j at hj
  simpa only [hj] using hh

/-- Exact 2q-variable row encoding of invalidity of the original candidate inequality. -/
theorem invalid_iff_violation_rows (P : Model m) (hWF : WellFormed P) :
    ¬ Valid P ↔ ∃ z y : Fin q → ℤ, ∀ k : ViolationRow m, (violationRow P k).Holds z y := by
  rw [invalid_iff_count_violation P hWF]
  constructor
  · rintro ⟨z, hz, hf, hv⟩
    obtain ⟨y, hy, hb⟩ := (prefix_feasible_epigraph P hWF z hz).mp hf
    refine ⟨encodeCounts z, y, (violationRows_iff P _ _).mpr ⟨?_, hv⟩⟩
    exact ⟨(integerCountBounds_encode z).mpr hz, hy, hb⟩
  · rintro ⟨z, y, hh⟩
    obtain ⟨he, hv⟩ := (violationRows_iff P z y).mp hh
    obtain ⟨hb, hf⟩ := feasibleEpigraph_decode P hWF z y he
    have hid := encode_decodeCounts z he.1
    refine ⟨decodeCounts z, hb, hf, ?_⟩
    change P.rhs + 1 ≤ ∑ j, P.coefficient j * encodeCounts (decodeCounts z) j
    rw [hid]
    exact hv

theorem violationRow_card (m : Fin q → ℕ) :
    Fintype.card (ViolationRow m) = Fintype.card (Item m) + 2 * q + 2 := by
  simp [ViolationRow, FeasibleRow]; omega

end MOR34
