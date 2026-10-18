import MOR34.IntegerRowBounds
import MOR34.ParitySolver
import MOR34.ViolationEncoding

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

/-- A loose common bound avoids cancellation assumptions and includes strict offsets. -/
def rowConstantBound (N : ℕ) (M D : ℤ) : ℤ := (2 * (N : ℤ) + 2) * M + N + D + 1

theorem countRow_integer_bounded (P : Model m) (N : ℕ) (M C D : ℤ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M)
    (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (hA : ∀ i j, |A i j| ≤ C) (hbb : ∀ i, |b i| ≤ D) (k : CountRow m r) :
    (countRow P (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ)) k).IntegerBounded
      (M + C + 1) 1 (rowConstantBound N M D) := by
  have hM0 : 0 ≤ M := by omega
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hprod : 0 ≤ (2 * (N : ℤ)) * M := mul_nonneg (by positivity) hM0
  have hR0 : 0 ≤ rowConstantBound N M D := by unfold rowConstantBound; nlinarith [hprod]
  have hRM : M ≤ rowConstantBound N M D := by unfold rowConstantBound; nlinarith
  have hRN : (N : ℤ) ≤ rowConstantBound N M D := by unfold rowConstantBound; nlinarith [hprod]
  have hRD : D ≤ rowConstantBound N M D := by unfold rowConstantBound; nlinarith [hprod]
  have hp (j : Fin q) (t : Fin (m j)) :
      |P.weight ⟨j, t⟩ * (t.val : ℤ) - prefixCost (fun u => P.weight ⟨j, u⟩) t.val| ≤
        rowConstantBound N M D := by
    have ht := prefixIntercept_abs_bound (fun u => P.weight ⟨j, u⟩) M hM0 (fun u => hw ⟨j, u⟩) t
    have hm' : (m j : ℤ) ≤ N := by exact_mod_cast hm j
    unfold rowConstantBound
    nlinarith
  rcases k with (j | j) | ((u | u) | (⟨j, t⟩ | (u | i)))
  · have h := integerRow_bounded (integerPick j (-1)) 0 0 (M+C+1) 1 (rowConstantBound N M D)
      (integerPick_abs_bound j _ _ (by omega) (by norm_num; omega))
      (by simp) (by simpa using hR0)
    simpa [countRow, integerRow, pickCoeff, integerPick] using h
  · have hj : |(m j : ℤ)| ≤ rowConstantBound N M D := by
      rw [abs_of_nonneg (by positivity)]
      exact (by exact_mod_cast hm j : (m j : ℤ) ≤ N).trans hRN
    have h := integerRow_bounded (integerPick j 1) 0 (m j) (M+C+1) 1 (rowConstantBound N M D)
      (integerPick_abs_bound j _ _ (by omega) (by norm_num; omega)) (by simp) hj
    simpa [countRow, integerRow, pickCoeff, integerPick] using h
  · have h := integerRow_bounded P.coefficient 0 P.rhs (M+C+1) 1 (rowConstantBound N M D)
      (fun j => (hc j).trans (by omega)) (by simp) (hd.trans hRM)
    simpa [countRow, integerRow] using h
  · have h := integerRow_bounded (fun j => -P.coefficient j) 0 (-P.rhs) (M+C+1) 1 (rowConstantBound N M D)
      (fun j => by simpa using (hc j).trans (show M ≤ M+C+1 by omega))
      (by simp) (by simpa using hd.trans hRM)
    simpa [countRow, integerRow] using h
  · have h := integerRow_bounded (integerPick j (P.weight ⟨j, t⟩)) (integerPick j (-1))
      (P.weight ⟨j, t⟩ * (t.val : ℤ) - prefixCost (fun u => P.weight ⟨j, u⟩) t.val)
      (M+C+1) 1 (rowConstantBound N M D)
      (integerPick_abs_bound j _ _ (by omega) ((hw _).trans (by omega)))
      (integerPick_abs_bound j _ _ (by norm_num) (by norm_num)) (hp j t)
    simpa [countRow, integerRow, pickCoeff, integerPick] using h
  · have h := integerRow_bounded 0 (fun _ : Fin q => 1) P.capacity (M+C+1) 1 (rowConstantBound N M D)
      (by intro j; simp; omega) (by simp) (hb.trans hRM)
    simpa [countRow, integerRow] using h
  · have h := integerRow_bounded (A i) 0 (b i) (M+C+1) 1 (rowConstantBound N M D)
      (fun j => (hA i j).trans (by omega)) (by simp) ((hbb i).trans hRD)
    simpa [countRow, integerRow] using h

/-- This is the actual parity row family passed to the solver, with integer extra queries. -/
theorem parityRows_integer_bounded (P : Model m) (N : ℕ) (M C D : ℤ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M)
    (L : List (IntegerQuery q)) (hL : ∀ a ∈ L, a.Bounded C D) (ε : Parity q)
    (k : CountRow m L.length) :
    ((countRow P (queryCoefficients L) (queryBounds L) k).withParity ε).IntegerBounded
      (2 * (M+C+1)) 1 (rowConstantBound N M D + q * (M+C+1)) := by
  apply integerRow_parity_bounded _ ε _ _ _ (by omega)
  exact countRow_integer_bounded P N M C D hM hC hD hm hw hc hb hd
    (fun i => (L.get i).coefficient) (fun i => (L.get i).bound)
    (fun i => (hL _ (List.get_mem L i)).1) (fun i => (hL _ (List.get_mem L i)).2) k

end MOR34
