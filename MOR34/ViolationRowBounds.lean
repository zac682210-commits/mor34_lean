import MOR34.CountRowBounds

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def feasibleCountRowIndex : FeasibleRow m → CountRow m 0
  | .inl (.inl j) => .inl (.inl j)
  | .inl (.inr j) => .inl (.inr j)
  | .inr (.inl t) => .inr (.inr (.inl t))
  | .inr (.inr u) => .inr (.inr (.inr (.inl u)))

theorem feasibleRow_as_countRow (P : Model m) (k : FeasibleRow m) :
    feasibleRow P k = countRow P (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
      (feasibleCountRowIndex k) := by
  rcases k with (j | j) | (t | u) <;> rfl

theorem feasibleRows_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M) (k : FeasibleRow m) :
    (feasibleRow P k).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  rw [feasibleRow_as_countRow]
  have hh := countRow_integer_bounded P N M 0 0 hM (by omega) (by omega) hm hw hc hb hd
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (feasibleCountRowIndex k)
  have hA : (fun i : Fin 0 => (Fin.elim0 i : Fin q → ℚ)) =
      (fun i j => ((Fin.elim0 i : Fin q → ℤ) j : ℚ)) := by
    funext i
    exact Fin.elim0 i
  have hB : (fun i : Fin 0 => (Fin.elim0 i : ℚ)) =
      (fun i => ((Fin.elim0 i : ℤ) : ℚ)) := by
    funext i
    exact Fin.elim0 i
  rw [hA, hB]
  simpa only [add_zero] using hh

theorem violationInequality_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M) (hd : |P.rhs| ≤ M) :
    (violationInequality P).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  have hM0 : 0 ≤ M := by omega
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hprod : 0 ≤ (2 * (N : ℤ)) * M := mul_nonneg (by positivity) hM0
  have hRD : M+1 ≤ rowConstantBound N M 0 := by unfold rowConstantBound; nlinarith [hprod]
  have hh : |-(P.rhs + 1)| ≤ rowConstantBound N M 0 := by
    rw [abs_neg]
    have h := abs_add_le P.rhs 1
    norm_num at h
    linarith
  have h := integerRow_bounded (fun j => -P.coefficient j) 0 (-(P.rhs+1))
    (M+1) 1 (rowConstantBound N M 0)
    (fun j => by simpa using (hc j).trans (show M ≤ M+1 by omega)) (by simp) hh
  simpa [violationInequality, integerRow] using h

theorem violationRows_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M) (k : ViolationRow m) :
    (violationRow P k).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  cases k with
  | inl k => exact feasibleRows_integer_bounded P N M hM hm hw hc hb hd k
  | inr u => exact violationInequality_integer_bounded P N M hM hc hd

end MOR34
