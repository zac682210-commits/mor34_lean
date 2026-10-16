import MOR34.CellSpan
import MOR34.AdjacentSpan

namespace MOR34
section Augmentation
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]

def zeroAugment : V →ₗ[ℝ] ℝ × V where
  toFun x := (0, x)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

noncomputable def pointAugment : V →ᵃ[ℝ] ℝ × V where
  toFun x := (1, x)
  linear := zeroAugment
  map_vadd' p v := by ext <;> simp [zeroAugment]

def augmentedSpan (T : Set V) : Submodule ℝ (ℝ × V) :=
  Submodule.span ℝ (pointAugment '' T)

theorem augment_mem_of_affineSpan {T : Set V} {x : V} (hx : x ∈ affineSpan ℝ T) :
    pointAugment x ∈ augmentedSpan T := by
  have h := AffineSubspace.mem_map_of_mem (pointAugment : V →ᵃ[ℝ] ℝ × V) hx
  rw [AffineSubspace.map_span] at h
  exact affineSpan_subset_span h

theorem zero_vectorSpan_le_augmentedSpan (T : Set V) :
    (vectorSpan ℝ T).map zeroAugment ≤ augmentedSpan T := by
  rw [vectorSpan_def, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  have ha' : pointAugment a ∈ augmentedSpan T := Submodule.subset_span ⟨a, ha, rfl⟩
  have hb' : pointAugment b ∈ augmentedSpan T := Submodule.subset_span ⟨b, hb, rfl⟩
  convert Submodule.sub_mem (augmentedSpan T) ha' hb' using 1 <;>
    ext <;> simp [pointAugment, zeroAugment]

/-- Recover the full augmented span from its quotient and the kernel directions. -/
theorem augmented_span_lift (f : V →ₗ[ℝ] W) (T B : Set V) (hB : B ⊆ T)
    (hker : LinearMap.ker f ≤ vectorSpan ℝ T)
    (himage : ∀ x ∈ T, f x ∈ affineSpan ℝ (f '' B)) :
    augmentedSpan T = augmentedSpan B ⊔ (LinearMap.ker f).map zeroAugment := by
  let N := augmentedSpan B ⊔ (LinearMap.ker f).map zeroAugment
  let Q : (ℝ × V) →ₗ[ℝ] (ℝ × W) := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap f
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    have hmap : augmentedSpan (f '' B) ≤ N.map Q := by
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨pointAugment b, le_sup_left (Submodule.subset_span ⟨b, hb, rfl⟩), rfl⟩
    have hm := hmap (augment_mem_of_affineSpan (himage x hx))
    obtain ⟨y, hy, he⟩ := hm
    have hfst : y.1 = 1 := congrArg Prod.fst he
    have hsnd : f y.2 = f x := congrArg Prod.snd he
    have hk : x - y.2 ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hsnd, sub_self]
    have hd : pointAugment x - y = zeroAugment (x - y.2) := by
      ext <;> simp [pointAugment, zeroAugment, hfst]
    have hn : pointAugment x - y ∈ N := by
      rw [hd]
      exact le_sup_right (show zeroAugment (x - y.2) ∈ (LinearMap.ker f).map zeroAugment from
        ⟨x - y.2, hk, rfl⟩)
    have hh := N.add_mem hn hy
    simpa using hh
  · apply sup_le
    · exact Submodule.span_mono (Set.image_mono hB)
    · exact (Submodule.map_mono hker).trans (zero_vectorSpan_le_augmentedSpan T)
end Augmentation
end MOR34
