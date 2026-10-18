import MOR34.RowPayload
import MOR34.ForcedRowBounds
import MOR34.ViolationRowBounds

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem basicRow_uniform_bound (L : CountInequality q) (N M : ℕ) (hM : 1 ≤ M)
    (h : L.IntegerBounded ((M : ℤ)+1) 1 (rowConstantBound N M 0)) :
    L.IntegerBounded (uniformRowRadius q N M) (uniformRowRadius q N M) (uniformRowRadius q N M) := by
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hN' : (0 : ℤ) ≤ N := by positivity
  have hH : (0 : ℤ) ≤ normalCoefficientBound q N := by unfold normalCoefficientBound; positivity
  have hNM : (0 : ℤ) ≤ (N : ℤ)*M := by positivity
  have hNH := mul_nonneg hN' hH
  have hR : (uniformRowRadius q N M : ℤ) =
      (6*(N : ℤ)+10)*((M : ℤ)+normalCoefficientBound q N+1) := by
    simp only [uniformRowRadius, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, normalRadius_cast]
  apply integerRow_bound_mono L h
  · rw [hR]; nlinarith
  · rw [hR]; nlinarith
  · rw [hR]; unfold rowConstantBound; nlinarith

theorem forced_system_payload (P : Model m) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hm : ∀ j, m j ≤ N) (hw : ∀ i, |P.weight i| ≤ (M : ℤ))
    (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ)) (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (j : Fin q) (u v : Fin (m j)) :
    ∃ a b : ForcedRow m j u v → Fin q → ℤ, ∃ d : ForcedRow m j u v → ℤ,
      (∀ k, forcedRow P j u v k = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+2*q+(pairAllowed u v).card+6)*((2*q+1)*uniformRowBits q N M) := by
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hh := uniform_system_payload (forcedRow P j u v) N M hN
    (fun k => basicRow_uniform_bound _ N M hM
      (forcedRows_integer_bounded P N M hM' hm hw hc hb hd j u v k))
  simpa only [forcedRow_card] using hh

theorem violation_system_payload (P : Model m) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hm : ∀ j, m j ≤ N) (hw : ∀ i, |P.weight i| ≤ (M : ℤ))
    (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ)) (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) :
    ∃ a b : ViolationRow m → Fin q → ℤ, ∃ d : ViolationRow m → ℤ,
      (∀ k, violationRow P k = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+2*q+2)*((2*q+1)*uniformRowBits q N M) := by
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hh := uniform_system_payload (violationRow P) N M hN
    (fun k => basicRow_uniform_bound _ N M hM
      (violationRows_integer_bounded P N M hM' hm hw hc hb hd k))
  simpa only [violationRow_card] using hh

end MOR34
