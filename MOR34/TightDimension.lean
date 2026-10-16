import MOR34.ExchangeKernel
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

namespace MOR34

variable {q : ℕ} {m : Fin q → ℕ}

def pointVector (S : Finset (Item m)) : Item m → ℝ := fun i => if i ∈ S then 1 else 0

def tightPointSet (P : Model m) : Set (Item m → ℝ) :=
  {x | ∃ S : Finset (Item m), Tight P S ∧ x = pointVector S}

theorem pointVector_swap_difference (S : Finset (Item m)) (u v : Item m)
    (hu : u ∉ S) (hv : v ∈ S) :
    pointVector (insert u (S.erase v)) - pointVector S = unitVector u - unitVector v := by
  have huv : u ≠ v := by intro h; subst v; exact hu hv
  ext i
  by_cases hiu : i = u
  · subst i
    simp [pointVector, unitVector, hu, huv]
  · by_cases hiv : i = v
    · subst i
      simp [pointVector, unitVector, hv, hiu]
    · simp [pointVector, unitVector, hiu, hiv]

theorem exchangeDirectionSpan_le_tightVectorSpan (P : Model m) (hWF : WellFormed P) :
    exchangeDirectionSpan P ≤ vectorSpan ℝ (tightPointSet P) := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, u, v, ⟨huv, S, hS, hnu, hyv⟩, rfl⟩
  have hsort := hWF.2.2.2.2.2.2.2
  have hT := tight_swap P hS hnu hyv (hsort j u v (le_of_lt huv)) rfl
  have hmem := vsub_mem_vectorSpan ℝ
    (show pointVector (insert (⟨j, u⟩ : Item m) (S.erase ⟨j, v⟩)) ∈ tightPointSet P from
      ⟨_, hT, rfl⟩)
    (show pointVector S ∈ tightPointSet P from ⟨S, hS, rfl⟩)
  change pointVector (insert (⟨j, u⟩ : Item m) (S.erase ⟨j, v⟩)) - pointVector S ∈
      vectorSpan ℝ (tightPointSet P) at hmem
  rw [pointVector_swap_difference S _ _ hnu hyv] at hmem
  exact hmem

/-- Rank-nullity on a subspace containing the full kernel. -/
theorem finrank_subspace_map {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] W) (D : Submodule ℝ V) (hD : LinearMap.ker f ≤ D) :
    Module.finrank ℝ D = Module.finrank ℝ (LinearMap.ker f) + Module.finrank ℝ (D.map f) := by
  have hk : (LinearMap.ker (f.domRestrict D)).map D.subtype = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hD hx⟩, hx, rfl⟩
  have hkd : Module.finrank ℝ (LinearMap.ker (f.domRestrict D)) =
      Module.finrank ℝ (LinearMap.ker f) := by
    rw [← hk, Submodule.finrank_map_subtype_eq]
  have h := (f.domRestrict D).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hkd] at h
  omega

/-- For a nonempty tight set this is the real affine-dimension formula in Lemma 3. -/
theorem tight_dimension_quotient (P : Model m) (hWF : WellFormed P)
    (_hT : (tightPointSet P).Nonempty) :
    Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) =
      (Fintype.card (Item m) - Fintype.card (ExchangeComponent P)) +
      Module.finrank ℝ (vectorSpan ℝ ((componentCountMap P) '' tightPointSet P)) := by
  have hk : LinearMap.ker (componentCountMap P) ≤ vectorSpan ℝ (tightPointSet P) := by
    rw [← exchangeDirectionSpan_eq_ker]
    exact exchangeDirectionSpan_le_tightVectorSpan P hWF
  have hd := finrank_subspace_map (componentCountMap P) (vectorSpan ℝ (tightPointSet P)) hk
  have hi : (vectorSpan ℝ (tightPointSet P)).map (componentCountMap P) =
      vectorSpan ℝ ((componentCountMap P) '' tightPointSet P) :=
    (componentCountMap P).toAffineMap.vectorSpan_image_eq_submodule_map
  rw [hi, ← exchangeDirectionSpan_eq_ker] at hd
  have he := exchangeDirectionSpan_finrank P
  omega

end MOR34
