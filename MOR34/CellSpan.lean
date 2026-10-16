import MOR34.ParityCells

namespace MOR34

/-- Transfer a spanning set through a map that is affine on the specified domain. -/
theorem affine_on_set_span_image {X U V : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] (embed : X → U) (g : X → V)
    (C B : Set X) (hB : B ⊆ C) (f : U →ᵃ[ℝ] V)
    (hf : ∀ x ∈ C, f (embed x) = g x)
    (hs : ∀ x ∈ C, embed x ∈ affineSpan ℝ (embed '' B)) :
    affineSpan ℝ (g '' C) = affineSpan ℝ (g '' B) := by
  apply le_antisymm
  · apply affineSpan_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    have hm := AffineSubspace.mem_map_of_mem f (hs x hx)
    rw [AffineSubspace.map_span] at hm
    have he : f '' (embed '' B) = g '' B := by
      ext y
      constructor
      · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨b, hb, (hf b (hB hb)).symm⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨embed b, ⟨b, hb, rfl⟩, hf b (hB hb)⟩
    rw [he, hf x hx] at hm
    exact hm
  · exact affineSpan_mono ℝ (Set.image_mono hB)

variable {q : ℕ} {m : Fin q → ℕ}

def parityCellSet (P : Model m) (ε : Parity q) (e : ParityExtrema P ε)
    (mode : CellMode q) : Set (Counts q) :=
  {z | TightParity P ε z ∧ CellCondition e.low e.high mode z}

theorem actual_cell_span_image (P : Model m) (hWF : WellFormed P)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q)
    (B : Set (Counts q)) (hB : B ⊆ parityCellSet P ε e mode)
    (hs : ∀ z ∈ parityCellSet P ε e mode, countReal z ∈ affineSpan ℝ (countReal '' B)) :
    affineSpan ℝ ((fun z => componentCountMap P (pointVector (prefixSet z))) ''
      parityCellSet P ε e mode) =
    affineSpan ℝ ((fun z => componentCountMap P (pointVector (prefixSet z))) '' B) := by
  obtain ⟨f, hf⟩ := actual_cell_affine P hWF ε e mode
  exact affine_on_set_span_image countReal _ _ B hB f (fun z hz => hf z hz.1 hz.2) hs

end MOR34
