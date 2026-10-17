import MOR34.LinearOracle
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.List.OfFn

namespace MOR34

/-- A finite rational family has a common nonzero integer multiplier. -/
theorem finite_rational_integer_multiple {ι : Type*} [Finite ι] (c : ι → ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ a : ι → ℤ, ∀ i, (a i : ℚ) = (d : ℚ) * c i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) c
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  intro i
  simpa only [Algebra.smul_def, Int.algebraMap_eq_intCast] using ha i

/-- A rational linear functional on augmented counts is an affine expression in the counts. -/
theorem count_functional_coefficients {q : ℕ} (f : (ℚ × (Fin q → ℚ)) →ₗ[ℚ] ℚ) :
    ∃ c : Option (Fin q) → ℚ, ∀ z : Counts q,
      f (rationalCountPoint z) = c none + ∑ j, c (some j) * (z j : ℚ) := by
  classical
  let e : (Option (Fin q) → ℚ) ≃ₗ[ℚ] ℚ × (Fin q → ℚ) := LinearEquiv.piOptionEquivProd ℚ
  let g := f.comp e.toLinearMap
  let c : Option (Fin q) → ℚ := fun i => g (fun j => if i = j then 1 else 0)
  refine ⟨c, ?_⟩
  intro z
  have h := LinearMap.pi_apply_eq_sum_univ g (e.symm (rationalCountPoint z))
  simpa [g, c, e, LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd,
    rationalCountPoint, smul_eq_mul, mul_comm] using h

/-- Clearing denominators preserves the zero set; no bound on coefficient bits is asserted. -/
theorem integer_form_of_functional {q : ℕ} (f : (ℚ × (Fin q → ℚ)) →ₗ[ℚ] ℚ) :
    ∃ a : IntegerForm q, ∀ z : Counts q, a.eval z = 0 ↔ f (rationalCountPoint z) = 0 := by
  obtain ⟨c, hc⟩ := count_functional_coefficients f
  obtain ⟨d, hd, a, ha⟩ := finite_rational_integer_multiple c
  let a' : IntegerForm q := ⟨fun j => a (some j), a none⟩
  have he (z : Counts q) : (a'.eval z : ℚ) = (d : ℚ) * f (rationalCountPoint z) := by
    rw [hc]
    simp only [IntegerForm.eval, a', Int.cast_add, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ha]
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨a', ?_⟩
  intro z
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  constructor
  · intro hz
    have hh : (d : ℚ) * f (rationalCountPoint z) = 0 := by rw [← he, hz]; simp
    exact (mul_eq_zero.mp hh).resolve_left hd'
  · intro hz
    have hh : (a'.eval z : ℚ) = 0 := by rw [he, hz, mul_zero]
    exact_mod_cast hh

end MOR34

namespace MOR34

/-- At most q+1 integer equations describe the augmented span of any finite count selection. -/
theorem bounded_integer_forms_exist {q : ℕ} (B : Finset (Counts q)) :
    ∃ forms : List (IntegerForm q), FormsDescribe B forms ∧ forms.length ≤ q + 1 := by
  classical
  let V := ℚ × (Fin q → ℚ)
  let W : Submodule ℚ V := selectedSpan (K := ℚ) rationalCountPoint B
  let d := Module.finrank ℚ (V ⧸ W)
  let b := Module.finBasis ℚ (V ⧸ W)
  let f : Fin d → V →ₗ[ℚ] ℚ := fun i => (b.coord i).comp W.mkQ
  have hmem (z : Counts q) : rationalCountPoint z ∈ W ↔ ∀ i, f i (rationalCountPoint z) = 0 := by
    constructor
    · intro hz i
      have hh : W.mkQ (rationalCountPoint z) = 0 := Submodule.Quotient.mk_eq_zero.mpr hz
      simp [f, hh]
    · intro hz
      have hr : b.repr (W.mkQ (rationalCountPoint z)) = 0 := by
        ext i
        exact hz i
      have hh : W.mkQ (rationalCountPoint z) = 0 := b.repr.injective (by simpa using hr)
      exact Submodule.Quotient.mk_eq_zero.mp hh
  choose a ha using fun i => integer_form_of_functional (f i)
  refine ⟨List.ofFn a, ?_, ?_⟩
  · intro z
    rw [show selectedSpan (K := ℚ) rationalCountPoint B = W from rfl, hmem]
    simp only [List.forall_mem_ofFn_iff]
    exact forall_congr' (fun i => (ha i z).symm)
  · simp only [List.length_ofFn]
    have hd := Submodule.finrank_quotient_le W
    have hv : Module.finrank ℚ V = q + 1 := by
      simp [V, Module.finrank_prod, Module.finrank_pi, Nat.add_comm]
    change Module.finrank ℚ (V ⧸ W) ≤ q + 1
    omega

/-- The normal-list contract is inhabited; no normal-generation bit bound is asserted. -/
theorem bounded_integer_forms_family {q : ℕ} :
    ∃ forms : Finset (Counts q) → List (IntegerForm q),
      (∀ B, FormsDescribe B (forms B)) ∧ ∀ B, (forms B).length ≤ q + 1 := by
  classical
  choose forms hf hs using (bounded_integer_forms_exist (q := q))
  exact ⟨forms, hf, hs⟩

/-- Only the linear feasibility interface remains an assumption in this query-bound theorem. -/
theorem count_basis_from_linear_oracle {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q),
    let B := basisSearch (linearSpanOracle solve forms) (q + 1) ∅
    (B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      (∀ z ∈ C, rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B) ∧
      linearBasisCalls solve forms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  obtain ⟨forms, hf, hsize⟩ := bounded_integer_forms_family (q := q)
  exact ⟨forms, linear_count_basis_correct C solve hs forms hf hsize⟩

end MOR34
