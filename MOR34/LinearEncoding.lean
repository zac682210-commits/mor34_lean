import MOR34.CountEncoding

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

/-- A rational inequality on two blocks of q integer variables. -/
structure CountInequality (q : ℕ) where
  counts : Fin q → ℚ
  costs : Fin q → ℚ
  bound : ℚ

def CountInequality.Holds (L : CountInequality q) (z y : Fin q → ℤ) : Prop :=
  (∑ j, L.counts j * (z j : ℚ)) + (∑ j, L.costs j * (y j : ℚ)) ≤ L.bound

abbrev CountRow (m : Fin q → ℕ) (r : ℕ) :=
  (Fin q ⊕ Fin q) ⊕ ((Unit ⊕ Unit) ⊕ (Item m ⊕ (Unit ⊕ Fin r)))

def pickCoeff (j : Fin q) (a : ℚ) : Fin q → ℚ := fun k => if k = j then a else 0

theorem pickCoeff_sum (j : Fin q) (a : ℚ) (z : Fin q → ℤ) :
    (∑ k, pickCoeff j a k * (z k : ℚ)) = a * (z j : ℚ) := by
  simp [pickCoeff, ite_mul]

/-- Every row is explicitly linear; prefix costs occur only as input-dependent constants. -/
def countRow (P : Model m) (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ) :
    CountRow m r → CountInequality q
  | Sum.inl (Sum.inl j) => ⟨pickCoeff j (-1), 0, 0⟩
  | Sum.inl (Sum.inr j) => ⟨pickCoeff j 1, 0, (m j : ℚ)⟩
  | Sum.inr (Sum.inl (Sum.inl _)) => ⟨fun j => P.coefficient j, 0, P.rhs⟩
  | Sum.inr (Sum.inl (Sum.inr _)) => ⟨fun j => -(P.coefficient j : ℚ), 0, -(P.rhs : ℚ)⟩
  | Sum.inr (Sum.inr (Sum.inl ⟨j, t⟩)) =>
      ⟨pickCoeff j (P.weight ⟨j, t⟩), pickCoeff j (-1),
        (P.weight ⟨j, t⟩ : ℚ) * (t.val : ℚ) -
          (prefixCost (fun u => P.weight ⟨j, u⟩) t.val : ℚ)⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => ⟨0, fun _ => 1, P.capacity⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) => ⟨A i, 0, b i⟩

theorem prefixLine_rational_iff {s : ℕ} (w : Fin s → ℤ) (t : Fin s) (z y : ℤ) :
    prefixLine w t z ≤ y ↔
      (w t : ℚ) * (z : ℚ) - (y : ℚ) ≤
        (w t : ℚ) * (t.val : ℚ) - (prefixCost w t.val : ℚ) := by
  have he : prefixLine w t z ≤ y ↔ w t * z - y ≤ w t * (t.val : ℤ) - prefixCost w t.val := by
    unfold prefixLine
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> exact_mod_cast h

/-- The finite row system is equivalent to the exact count epigraph and the extra rows. -/
theorem countRows_iff (P : Model m) (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ)
    (z y : Fin q → ℤ) :
    (∀ k : CountRow m r, (countRow P A b k).Holds z y) ↔
      CountEpigraph P z y ∧ RationalRestrictions A b z := by
  constructor
  · intro h
    have hl (j : Fin q) := h (Sum.inl (Sum.inl j))
    have hu (j : Fin q) := h (Sum.inl (Sum.inr j))
    have he₁ := h (Sum.inr (Sum.inl (Sum.inl ())))
    have he₂ := h (Sum.inr (Sum.inl (Sum.inr ())))
    have hc := h (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
    simp only [countRow, CountInequality.Holds, pickCoeff_sum, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul, one_mul, zero_add] at hl hu he₁ he₂ hc
    have he₁' : (∑ j, P.coefficient j * z j) ≤ P.rhs := by exact_mod_cast he₁
    have he₂' : -(∑ j, P.coefficient j * z j) ≤ -P.rhs := by
      have hh : -(∑ j, (P.coefficient j : ℚ) * (z j : ℚ)) ≤ -(P.rhs : ℚ) := by
        simpa only [neg_mul, Finset.sum_neg_distrib] using he₂
      exact_mod_cast hh
    refine ⟨⟨?_, le_antisymm he₁' (by omega), ?_, ?_⟩, ?_⟩
    · intro j
      constructor
      · have hh : (0 : ℚ) ≤ (z j : ℚ) := by linarith [hl j]
        exact_mod_cast hh
      · exact_mod_cast hu j
    · intro j t
      apply (prefixLine_rational_iff _ t _ _).mpr
      have hh := h (Sum.inr (Sum.inr (Sum.inl ⟨j, t⟩)))
      simpa only [countRow, CountInequality.Holds, pickCoeff_sum, neg_one_mul, sub_eq_add_neg] using hh
    · exact_mod_cast hc
    · intro i
      have hh := h (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))
      simpa [countRow, CountInequality.Holds] using hh
  · rintro ⟨⟨hb, he, hp, hc⟩, hr⟩ k
    rcases k with (j | j) | ((u | u) | (⟨j, t⟩ | (u | i)))
    · have hh : (0 : ℚ) ≤ (z j : ℚ) := by exact_mod_cast (hb j).1
      simp only [countRow, CountInequality.Holds, pickCoeff_sum, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero, neg_one_mul]
      linarith
    · have hh : (z j : ℚ) ≤ (m j : ℚ) := by exact_mod_cast (hb j).2
      simpa [countRow, CountInequality.Holds, pickCoeff_sum] using hh
    · have hh : (∑ j, (P.coefficient j : ℚ) * (z j : ℚ)) = (P.rhs : ℚ) := by exact_mod_cast he
      simpa [countRow, CountInequality.Holds, hh] using le_of_eq hh
    · have hh : (∑ j, (P.coefficient j : ℚ) * (z j : ℚ)) = (P.rhs : ℚ) := by exact_mod_cast he
      simp [countRow, CountInequality.Holds, neg_mul, Finset.sum_neg_distrib, hh]
    · have hh := (prefixLine_rational_iff _ t _ _).mp (hp j t)
      simpa only [countRow, CountInequality.Holds, pickCoeff_sum, neg_one_mul, sub_eq_add_neg] using hh
    · have hh : (∑ j, (y j : ℚ)) ≤ (P.capacity : ℚ) := by exact_mod_cast hc
      simpa [countRow, CountInequality.Holds] using hh
    · simpa [countRow, CountInequality.Holds] using hr i

theorem countRow_card (m : Fin q → ℕ) (r : ℕ) :
    Fintype.card (CountRow m r) = Fintype.card (Item m) + 2 * q + r + 3 := by
  simp [CountRow]; omega

theorem exact_linear_count_encoding (P : Model m) (hWF : WellFormed P)
    (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ) :
    (∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧
      RationalRestrictions A b (encodeCounts z)) ↔
    ∃ z y : Fin q → ℤ, ∀ k : CountRow m r, (countRow P A b k).Holds z y := by
  rw [restricted_linear_epigraph P hWF A b]
  simp only [countRows_iff]

end MOR34
