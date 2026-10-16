import MOR34.FiniteCellBases
import MOR34.AugmentedDimension
import MOR34.RankScalar

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Exact real dimension recovered from any valid selection of cell bases. -/
theorem selected_dimension (P : Model m) (hWF : WellFormed P)
    (S : CellBasisSelection P) (hT : (tightPointSet P).Nonempty) :
    Module.finrank ℝ ((augmentedSpan (selectedPoints P S) ⊔
      (adjacentDirectionSpan P).map zeroAugment : Submodule ℝ (ℝ × (Item m → ℝ)))) =
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  rw [← selected_augmented_span P hWF S]
  exact augmentedSpan_finrank hT

/-- The structural dimension theorem; no running time or executable oracle is asserted. -/
theorem small_selected_dimension (P : Model m) (hWF : WellFormed P)
    (hT : (tightPointSet P).Nonempty) :
    ∃ S : CellBasisSelection P,
      (selectionFinset P S).card ≤ (q + 1) * 6 ^ q ∧
      Module.finrank ℝ ((augmentedSpan (selectedPoints P S) ⊔
        (adjacentDirectionSpan P).map zeroAugment : Submodule ℝ (ℝ × (Item m → ℝ)))) =
        Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  obtain ⟨S, hs⟩ := small_cellBasisSelection_exists P
  exact ⟨S, selectionFinset_card P S hs, selected_dimension P hWF S hT⟩

end MOR34
