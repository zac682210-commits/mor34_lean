import MOR34.ColumnNormals

namespace MOR34
variable {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At most one selected pivot column contributes at each coordinate. -/
theorem injective_coordinate_sum_bound (c : Fin r ↪ ι) (v : Fin r → ℤ)
    (D : ℤ) (hD : 0 ≤ D) (hv : ∀ i, |v i| ≤ D) (k : ι) :
    |∑ i, if c i = k then v i else 0| ≤ D := by
  by_cases hk : ∃ i, c i = k
  · obtain ⟨i, rfl⟩ := hk
    have he (j : Fin r) : c j = c i ↔ j = i := c.injective.eq_iff
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hv i
  · have he : ∀ i, c i ≠ k := by simpa using hk
    simpa [he] using hD

theorem columnNormal_bound (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι)
    (N : ℤ) (hN : 0 ≤ N) (hM : ∀ i j, |M i j| ≤ N) :
    ∀ j k, |columnNormal M c j k| ≤ 2 * (r.factorial : ℤ) * N ^ r := by
  intro j k
  let D : ℤ := (r.factorial : ℤ) * N ^ r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : ∀ i l, |(M.submatrix id c) i l| ≤ N := fun i l => hM i (c l)
  have hd := integer_det_bound (M.submatrix id c) N hA
  have hc := integer_cramer_bound (M.submatrix id c) (fun i => M i j) N hA (fun i => hM i j)
  have hs := injective_coordinate_sum_bound c
    ((M.submatrix id c).cramer (fun i => M i j)) D hD hc k
  have ht : |(if k = j then (M.submatrix id c).det else 0 : ℤ)| ≤ D := by
    by_cases hk : k = j
    · simpa [hk, D] using hd
    · simpa [hk] using hD
  have hh := abs_sub_le (if k = j then (M.submatrix id c).det else 0 : ℤ) 0
    (∑ i, if c i = k then (M.submatrix id c).cramer (fun a => M a j) i else 0)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  dsimp only [columnNormal]
  dsimp [D] at ht hs
  linarith

/-- A uniform bound uses only the total number of columns. -/
theorem columnNormal_uniform_bound (M : Matrix (Fin r) ι ℤ) (c : Fin r ↪ ι)
    (N : ℕ) (hN : 1 ≤ N) (hM : ∀ i j, |M i j| ≤ (N : ℤ)) :
    ∀ j k, |columnNormal M c j k| ≤
      2 * ((Fintype.card ι).factorial : ℤ) * (N : ℤ) ^ Fintype.card ι := by
  have hr : r ≤ Fintype.card ι := by simpa using Fintype.card_le_of_injective c c.injective
  have hf : (r.factorial : ℤ) ≤ ((Fintype.card ι).factorial : ℤ) := by
    exact_mod_cast Nat.factorial_le hr
  have hp : (N : ℤ) ^ r ≤ (N : ℤ) ^ Fintype.card ι :=
    pow_le_pow_right₀ (by exact_mod_cast hN) hr
  intro j k
  apply (columnNormal_bound M c N (by positivity) hM j k).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num)) hp (by positivity) (by positivity)

end MOR34
