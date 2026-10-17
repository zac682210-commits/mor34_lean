import MOR34.BoundedCountForms

namespace MOR34
variable {q : ℕ}

/-- A positive bound on all coordinates of a finite count selection. -/
def countRadius (B : Finset (Counts q)) : ℕ :=
  max 1 (B.sup (fun z => Finset.univ.sup z))

theorem countRadius_pos (B : Finset (Counts q)) : 1 ≤ countRadius B := le_max_left _ _

theorem countRadius_bounds (B : Finset (Counts q)) : ∀ z ∈ B, ∀ j, z j ≤ countRadius B := by
  intro z hz j
  calc
    z j ≤ Finset.univ.sup z := Finset.le_sup (Finset.mem_univ j)
    _ ≤ B.sup (fun z => Finset.univ.sup z) := Finset.le_sup hz
    _ ≤ countRadius B := le_max_right _ _

theorem countRadius_le (B : Finset (Counts q)) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ N) : countRadius B ≤ N := by
  apply max_le hN
  apply Finset.sup_le_iff.mpr
  intro z hz
  exact Finset.sup_le_iff.mpr (fun j _ => hB z hz j)

theorem normalCoefficientBound_mono (q : ℕ) {N M : ℕ} (h : N ≤ M) :
    normalCoefficientBound q N ≤ normalCoefficientBound q M := by
  unfold normalCoefficientBound
  gcongr
  exact_mod_cast h

/-- A fixed choice of bounded normal forms for every finite count set.
This retains classical pivot/row choices; an executable generator is separate. -/
noncomputable def boundedCountForms (B : Finset (Counts q)) : List (IntegerForm q) :=
  Classical.choose (bounded_count_forms_exist B (countRadius B) (countRadius_pos B) (countRadius_bounds B))

theorem boundedCountForms_spec (B : Finset (Counts q)) : FormsDescribe B (boundedCountForms B) :=
  (Classical.choose_spec (bounded_count_forms_exist B (countRadius B)
    (countRadius_pos B) (countRadius_bounds B))).1

theorem boundedCountForms_length (B : Finset (Counts q)) : (boundedCountForms B).length = q + 1 :=
  (Classical.choose_spec (bounded_count_forms_exist B (countRadius B)
    (countRadius_pos B) (countRadius_bounds B))).2.1

theorem boundedCountForms_bound (B : Finset (Counts q)) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ N) : FormsBounded (boundedCountForms B) N := by
  have hb := (Classical.choose_spec (bounded_count_forms_exist B (countRadius B)
    (countRadius_pos B) (countRadius_bounds B))).2.2
  have hle := normalCoefficientBound_mono q (countRadius_le B N hN hB)
  intro f hf
  exact ⟨((hb f hf).1).trans hle, fun j => ((hb f hf).2 j).trans hle⟩

/-- The chosen forms have the explicit logarithmic coefficient-bit bound. -/
theorem normalCoefficient_magnitudeBits (z : ℤ) (q N : ℕ)
    (hz : |z| ≤ normalCoefficientBound q N) :
    magnitudeBits z ≤ (Nat.clog 2 (q + 1) + Nat.clog 2 N) * (q + 1) + 2 := by
  let e := (Nat.clog 2 (q + 1) + Nat.clog 2 N) * (q + 1)
  have hn : z.natAbs ≤ 2 * (q + 1).factorial * N ^ (q + 1) := by
    have hi : (z.natAbs : ℤ) ≤ ((2 * (q + 1).factorial * N ^ (q + 1) : ℕ) : ℤ) := by
      simpa only [normalCoefficientBound, Int.natCast_natAbs, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow] using hz
    exact_mod_cast hi
  have hp := factorial_power_bound (q + 1) N (Nat.clog 2 (q + 1)) (Nat.clog 2 N)
    (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
  have hb : z.natAbs ≤ 2 ^ (e + 1) := by
    calc
      z.natAbs ≤ 2 * ((q + 1).factorial * N ^ (q + 1)) := by simpa [mul_assoc] using hn
      _ ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 hp
      _ = 2 ^ (e + 1) := by rw [pow_succ]; omega
  simpa only [e, Nat.add_assoc] using magnitudeBits_le_of_power_bound z (e + 1) hb

end MOR34
