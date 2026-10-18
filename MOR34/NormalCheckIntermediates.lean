import MOR34.ExecutableMatrixNormals
import MOR34.BoundedNormalFamily

namespace MOR34

/-- The entry bound is valid even for a candidate later rejected by annihilation checks. -/
theorem concreteColumnNormal_bound {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d) (N : ℕ) (hN : 1 ≤ N)
    (hM : ∀ i j, |M i j| ≤ (N : ℤ)) :
    ∀ j l, |concreteColumnNormal (M.submatrix a id) c j l| ≤
      2*(d.factorial : ℤ)*(N : ℤ)^d := by
  rw [concreteColumnNormal_eq]
  simpa only [Fintype.card_fin] using columnNormal_uniform_bound
    (M.submatrix a id) c N hN (fun i j => hM (a i) j)

/-- A single product in an integer annihilation check has bounded magnitude. -/
theorem normalCheck_term_bound {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d) (N : ℕ) (hN : 1 ≤ N)
    (hM : ∀ i j, |M i j| ≤ (N : ℤ)) (i : Fin s) (j l : Fin d) :
    |M i l * concreteColumnNormal (M.submatrix a id) c j l| ≤
      (N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d) := by
  rw [abs_mul]
  exact mul_le_mul (hM i l) (concreteColumnNormal_bound M a c N hN hM j l)
    (abs_nonneg _) (by positivity)

/-- Every partial dot product is controlled before cancellation, not just the final zero. -/
theorem normalCheck_partial_sum_bound {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d) (N : ℕ) (hN : 1 ≤ N)
    (hM : ∀ i j, |M i j| ≤ (N : ℤ)) (i : Fin s) (j : Fin d) (S : Finset (Fin d)) :
    |∑ l ∈ S, M i l * concreteColumnNormal (M.submatrix a id) c j l| ≤
      (d : ℤ)*(N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d) := by
  have hn : S.card ≤ d := by simpa using (Finset.card_le_univ S)
  have hcard : (S.card : ℤ) ≤ d := by exact_mod_cast hn
  calc
    _ ≤ ∑ l ∈ S, |M i l * concreteColumnNormal (M.submatrix a id) c j l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ S, (N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d) :=
      Finset.sum_le_sum (fun l _ => normalCheck_term_bound M a c N hN hM i j l)
    _ = (S.card : ℤ)*((N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d)) := by simp
    _ ≤ (d : ℤ)*((N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem normalCheck_partial_sum_bits {s r d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (a : Fin r → Fin s) (c : Fin r ↪ Fin d) (N : ℕ) (hN : 1 ≤ N)
    (hM : ∀ i j, |M i j| ≤ (N : ℤ)) (i : Fin s) (j : Fin d) (S : Finset (Fin d)) :
    magnitudeBits (∑ l ∈ S, M i l * concreteColumnNormal (M.submatrix a id) c j l) ≤
      (Nat.clog 2 (d+1)+Nat.clog 2 N)*(d+1)+2 := by
  apply normalCoefficient_magnitudeBits _ d N
  calc
    _ ≤ (d : ℤ)*(N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d) :=
      normalCheck_partial_sum_bound M a c N hN hM i j S
    _ ≤ ((d : ℤ)+1)*(N : ℤ)*(2*(d.factorial : ℤ)*(N : ℤ)^d) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right (by omega) (by positivity)
    _ = normalCoefficientBound d N := by
      simp only [normalCoefficientBound, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      ring

end MOR34
