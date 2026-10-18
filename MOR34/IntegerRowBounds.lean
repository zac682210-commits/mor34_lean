import MOR34.NormalQueryBounds
import MOR34.PrefixEncodingBounds
import MOR34.ForcedRows

namespace MOR34
variable {q : ℕ}

/-- Integer representatives and separate magnitude bounds for the two variable blocks. -/
def CountInequality.IntegerBounded (L : CountInequality q) (C E D : ℤ) : Prop :=
  ∃ a b : Fin q → ℤ, ∃ d : ℤ, L = integerRow a b d ∧
    (∀ j, |a j| ≤ C) ∧ (∀ j, |b j| ≤ E) ∧ |d| ≤ D

theorem integerRow_bounded (a b : Fin q → ℤ) (d C E D : ℤ)
    (ha : ∀ j, |a j| ≤ C) (hb : ∀ j, |b j| ≤ E) (hd : |d| ≤ D) :
    (integerRow a b d).IntegerBounded C E D := ⟨a, b, d, rfl, ha, hb, hd⟩

theorem integerRow_bound_mono (L : CountInequality q) {C E D C' E' D' : ℤ}
    (h : L.IntegerBounded C E D) (hC : C ≤ C') (hE : E ≤ E') (hD : D ≤ D') :
    L.IntegerBounded C' E' D' := by
  obtain ⟨a, b, d, he, ha, hb, hd⟩ := h
  exact ⟨a, b, d, he, fun j => (ha j).trans hC, fun j => (hb j).trans hE, hd.trans hD⟩

theorem integerPick_abs_bound (j : Fin q) (v C : ℤ) (hC : 0 ≤ C) (hv : |v| ≤ C) :
    ∀ k, |integerPick j v k| ≤ C := by
  intro k
  by_cases hk : k = j <;> simp [integerPick, hk, hC, hv]

theorem integerRow_withParity (a b : Fin q → ℤ) (d : ℤ) (ε : Fin q → Fin 2) :
    (integerRow a b d).withParity ε =
      integerRow (fun j => 2 * a j) b (d - ∑ j, a j * ((ε j).val : ℤ)) := by
  simp [integerRow, CountInequality.withParity, Int.cast_sum, mul_comm]

theorem integerRow_parity_bounded (L : CountInequality q) (ε : Fin q → Fin 2)
    (C E D : ℤ) (hC : 0 ≤ C) (h : L.IntegerBounded C E D) :
    (L.withParity ε).IntegerBounded (2 * C) E (D + q * C) := by
  obtain ⟨a, b, d, rfl, ha, hb, hd⟩ := h
  have hq := query_parity_bound (⟨a, d⟩ : IntegerQuery q) ε C D hC ⟨ha, hd⟩
  rw [integerRow_withParity]
  exact integerRow_bounded _ _ _ _ _ _ hq.1 hb hq.2

theorem queryRow_integer_bounded (a : IntegerQuery q) (C D : ℤ)
    (h : a.Bounded C D) : a.asCountRow.IntegerBounded C 0 D := by
  exact ⟨a.coefficient, 0, a.bound, rfl, h.1, by simp, h.2⟩

/-- Magnitude bits plus a separate sign bit; zero is encoded by one bit. -/
def signedIntegerBits (z : ℤ) : ℕ := magnitudeBits z + 1

def integerRowBits (a b : Fin q → ℤ) (d : ℤ) : ℕ :=
  (∑ j, signedIntegerBits (a j)) + (∑ j, signedIntegerBits (b j)) + signedIntegerBits d

theorem signedIntegerBits_bound (z : ℤ) (N : ℕ) (hz : |z| ≤ (N : ℤ)) :
    signedIntegerBits z ≤ Nat.clog 2 (N + 1) + 1 := by
  have hn : z.natAbs ≤ N := by
    exact_mod_cast (show (z.natAbs : ℤ) ≤ (N : ℤ) by simpa using hz)
  have hc : magnitudeBits z ≤ Nat.clog 2 (N + 1) :=
    Nat.clog_mono_right 2 (Nat.add_le_add_right hn 1)
  exact Nat.add_le_add_right hc 1

theorem integerRowBits_bound (a b : Fin q → ℤ) (d : ℤ) (C E D : ℕ)
    (ha : ∀ j, |a j| ≤ (C : ℤ)) (hb : ∀ j, |b j| ≤ (E : ℤ)) (hd : |d| ≤ (D : ℤ)) :
    integerRowBits a b d ≤ q * (Nat.clog 2 (C + 1) + 1) +
      q * (Nat.clog 2 (E + 1) + 1) + Nat.clog 2 (D + 1) + 1 := by
  have h1 : (∑ j, signedIntegerBits (a j)) ≤ q * (Nat.clog 2 (C + 1) + 1) := by
    calc
      _ ≤ ∑ _j : Fin q, (Nat.clog 2 (C + 1) + 1) :=
        Finset.sum_le_sum (fun j _ => signedIntegerBits_bound _ _ (ha j))
      _ = _ := by simp
  have h2 : (∑ j, signedIntegerBits (b j)) ≤ q * (Nat.clog 2 (E + 1) + 1) := by
    calc
      _ ≤ ∑ _j : Fin q, (Nat.clog 2 (E + 1) + 1) :=
        Finset.sum_le_sum (fun j _ => signedIntegerBits_bound _ _ (hb j))
      _ = _ := by simp
  have h3 := signedIntegerBits_bound d D hd
  unfold integerRowBits
  omega

theorem bounded_row_encoding_exists (L : CountInequality q) (C E D : ℕ)
    (h : L.IntegerBounded C E D) :
    ∃ a b : Fin q → ℤ, ∃ d : ℤ, L = integerRow a b d ∧
      integerRowBits a b d ≤ q * (Nat.clog 2 (C + 1) + 1) +
        q * (Nat.clog 2 (E + 1) + 1) + Nat.clog 2 (D + 1) + 1 := by
  obtain ⟨a, b, d, he, ha, hb, hd⟩ := h
  exact ⟨a, b, d, he, integerRowBits_bound a b d C E D ha hb hd⟩

end MOR34
