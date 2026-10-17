import MOR34.BoundedNormalFamily
import MOR34.ParityLinearEncoding

namespace MOR34
variable {q : ℕ}

def IntegerQuery.Bounded (a : IntegerQuery q) (C D : ℤ) : Prop :=
  (∀ j, |a.coefficient j| ≤ C) ∧ |a.bound| ≤ D

theorem positiveQuery_bound (f : IntegerForm q) (C : ℤ)
    (hc : |f.constant| ≤ C) (ha : ∀ j, |f.coefficient j| ≤ C) :
    f.positiveQuery.Bounded C (C + 1) := by
  constructor
  · intro j
    simpa [IntegerForm.positiveQuery] using ha j
  · have hh := abs_sub_le f.constant 0 1
    simp only [sub_zero, zero_sub, abs_neg, abs_one] at hh
    exact hh.trans (by linarith)

theorem negativeQuery_bound (f : IntegerForm q) (C : ℤ)
    (hc : |f.constant| ≤ C) (ha : ∀ j, |f.coefficient j| ≤ C) :
    f.negativeQuery.Bounded C (C + 1) := by
  constructor
  · exact ha
  · have hh := abs_sub_le (-1 : ℤ) 0 f.constant
    simp only [sub_zero, zero_sub, abs_neg, abs_one] at hh
    exact hh.trans (by linarith)

theorem outsideQueries_bound (forms : List (IntegerForm q)) (N : ℕ)
    (hf : FormsBounded forms N) :
    ∀ a ∈ outsideQueries forms,
      a.Bounded (normalCoefficientBound q N) (normalCoefficientBound q N + 1) := by
  intro a ha
  obtain ⟨f, hfl, ha⟩ := List.mem_flatMap.mp ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact positiveQuery_bound f _ (hf f hfl).1 (hf f hfl).2
  · exact negativeQuery_bound f _ (hf f hfl).1 (hf f hfl).2

def IntegerQuery.parityTransform (a : IntegerQuery q) (ε : Fin q → Fin 2) : IntegerQuery q :=
  ⟨fun j => 2 * a.coefficient j, a.bound - ∑ j, a.coefficient j * (ε j).val⟩

def IntegerQuery.asCountRow (a : IntegerQuery q) : CountInequality q :=
  ⟨fun j => (a.coefficient j : ℚ), 0, (a.bound : ℚ)⟩

theorem query_parity_row (a : IntegerQuery q) (ε : Fin q → Fin 2) :
    (a.parityTransform ε).asCountRow = a.asCountRow.withParity ε := by
  ext j <;> simp [IntegerQuery.parityTransform, IntegerQuery.asCountRow,
    CountInequality.withParity, Int.cast_sum, mul_comm]

theorem query_parity_bound (a : IntegerQuery q) (ε : Fin q → Fin 2)
    (C D : ℤ) (hC : 0 ≤ C) (ha : a.Bounded C D) :
    (a.parityTransform ε).Bounded (2 * C) (D + q * C) := by
  have hp (j : Fin q) : |a.coefficient j * ((ε j).val : ℤ)| ≤ C := by
    have he : (ε j).val = 0 ∨ (ε j).val = 1 := by have := (ε j).isLt; omega
    rcases he with he | he
    · simpa [he] using hC
    · simpa [he] using ha.1 j
  have hs : |∑ j, a.coefficient j * ((ε j).val : ℤ)| ≤ (q : ℤ) * C := by
    calc
      _ ≤ ∑ j, |a.coefficient j * ((ε j).val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin q, C := Finset.sum_le_sum (fun j _ => hp j)
      _ = (q : ℤ) * C := by simp
  constructor
  · intro j
    change |2 * a.coefficient j| ≤ 2 * C
    rw [abs_mul]
    norm_num
    linarith [ha.1 j]
  · change |a.bound - ∑ j, a.coefficient j * ((ε j).val : ℤ)| ≤ D + (q : ℤ) * C
    have hh := abs_sub_le a.bound 0 (∑ j, a.coefficient j * ((ε j).val : ℤ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith [ha.2]

end MOR34
