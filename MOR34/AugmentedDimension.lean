import MOR34.AugmentedSpan
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace MOR34
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem augmentedSpan_anchor {T : Set V} {a : V} (ha : a ∈ T) :
    augmentedSpan T = (ℝ ∙ pointAugment a) ⊔ (vectorSpan ℝ T).map zeroAugment := by
  let N := (ℝ ∙ pointAugment a) ⊔ (vectorSpan ℝ T).map zeroAugment
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    have hd : x - a ∈ vectorSpan ℝ T := vsub_mem_vectorSpan ℝ hx ha
    have hm : zeroAugment (x - a) ∈ N :=
      (show (vectorSpan ℝ T).map zeroAugment ≤ N from le_sup_right) ⟨x - a, hd, rfl⟩
    have hp : pointAugment a ∈ N :=
      (show (ℝ ∙ pointAugment a) ≤ N from le_sup_left) (Submodule.mem_span_singleton_self _)
    have he : pointAugment x = pointAugment a + zeroAugment (x - a) := by
      ext <;> simp [pointAugment, zeroAugment]
    rw [he]
    exact N.add_mem hp hm
  · apply sup_le
    · exact Submodule.span_singleton_le_iff_mem.mpr (Submodule.subset_span ⟨a, ha, rfl⟩)
    · exact zero_vectorSpan_le_augmentedSpan T

theorem augment_anchor_disjoint (a : V) (D : Submodule ℝ V) :
    Disjoint (ℝ ∙ pointAugment a) (D.map zeroAugment) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨v, hv, he⟩ := hy
  have hc0 : c = 0 := by
    have h := congrArg Prod.fst (hc.trans he.symm)
    simpa [pointAugment, zeroAugment] using h
  rw [← hc, hc0, zero_smul]

theorem augmentedSpan_finrank [FiniteDimensional ℝ V] {T : Set V} (hT : T.Nonempty) :
    Module.finrank ℝ (augmentedSpan T) = Module.finrank ℝ (vectorSpan ℝ T) + 1 := by
  obtain ⟨a, ha⟩ := hT
  have hne : pointAugment a ≠ (0 : ℝ × V) := by
    intro h
    have h' := congrArg Prod.fst h
    simpa [pointAugment] using h'
  have hi : Function.Injective (zeroAugment : V →ₗ[ℝ] ℝ × V) := by
    intro x y h
    exact congrArg Prod.snd h
  have hd := (Submodule.equivMapOfInjective zeroAugment hi (vectorSpan ℝ T)).finrank_eq
  have hr := Submodule.finrank_sup_add_finrank_inf_eq
    (ℝ ∙ pointAugment a) ((vectorSpan ℝ T).map zeroAugment)
  rw [(augment_anchor_disjoint a (vectorSpan ℝ T)).eq_bot,
    finrank_bot, add_zero, finrank_span_singleton hne] at hr
  rw [augmentedSpan_anchor ha]
  omega

end MOR34
