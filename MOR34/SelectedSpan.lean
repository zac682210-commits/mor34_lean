import MOR34.AugmentedSpan

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Output contract of the cell-basis subroutine. Its implementation is a separate obligation. -/
structure CellBasisSelection (P : Model m) where
  extrema : (ε : Parity q) → (∃ z, TightParity P ε z) → ParityExtrema P ε
  basis : (ε : Parity q) → (∃ z, TightParity P ε z) → CellMode q → Finset (Counts q)
  contained : ∀ ε hn mode, (↑(basis ε hn mode) : Set (Counts q)) ⊆
    parityCellSet P ε (extrema ε hn) mode
  spanning : ∀ ε hn mode z, z ∈ parityCellSet P ε (extrema ε hn) mode →
    countReal z ∈ affineSpan ℝ (countReal '' (↑(basis ε hn mode) : Set (Counts q)))

def selectedCounts (P : Model m) (S : CellBasisSelection P) : Set (Counts q) :=
  {z | ∃ ε hn mode, z ∈ S.basis ε hn mode}

def selectedPoints (P : Model m) (S : CellBasisSelection P) : Set (Item m → ℝ) :=
  (fun z => pointVector (prefixSet z)) '' selectedCounts P S

theorem selectedPoints_tight (P : Model m) (S : CellBasisSelection P) :
    selectedPoints P S ⊆ tightPointSet P := by
  rintro _ ⟨z, ⟨ε, hn, mode, hz⟩, rfl⟩
  exact ⟨prefixSet z, (S.contained ε hn mode hz).1.2.1, rfl⟩

theorem selectedPoints_quotient_spans (P : Model m) (hWF : WellFormed P)
    (S : CellBasisSelection P) : ∀ x ∈ tightPointSet P,
    componentCountMap P x ∈ affineSpan ℝ ((componentCountMap P) '' selectedPoints P S) := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ε, hε⟩ := tight_has_parity P (counts_bounded t) (prefix_tight P hWF ht)
  let hn : ∃ z, TightParity P ε z := ⟨counts t, hε⟩
  let e := S.extrema ε hn
  obtain ⟨mode, hm⟩ := parity_cell_cover P ε e hε
  let B : Set (Counts q) := ↑(S.basis ε hn mode)
  have heq := actual_cell_span_image P hWF ε e mode B (S.contained ε hn mode)
    (S.spanning ε hn mode)
  have hmem : componentCountMap P (pointVector (prefixSet (counts t))) ∈
      affineSpan ℝ ((fun z => componentCountMap P (pointVector (prefixSet z))) '' B) := by
    rw [← heq]
    exact subset_affineSpan ℝ _ ⟨counts t, ⟨hε, hm⟩, rfl⟩
  have hsub : ((fun z => componentCountMap P (pointVector (prefixSet z))) '' B) ⊆
      (componentCountMap P) '' selectedPoints P S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨pointVector (prefixSet z), ⟨z, ⟨ε, hn, mode, hz⟩, rfl⟩, rfl⟩
  rw [componentCountMap_prefix P ht] at hmem
  exact affineSpan_mono ℝ hsub hmem

/-- Paper Theorem 8's structural span identity, conditional on the stated basis-output contract. -/
theorem selected_augmented_span (P : Model m) (hWF : WellFormed P)
    (S : CellBasisSelection P) :
    augmentedSpan (tightPointSet P) = augmentedSpan (selectedPoints P S) ⊔
      (adjacentDirectionSpan P).map zeroAugment := by
  rw [adjacentDirectionSpan_eq_ker P hWF]
  apply augmented_span_lift (componentCountMap P) _ _ (selectedPoints_tight P S)
  · rw [← exchangeDirectionSpan_eq_ker]
    exact exchangeDirectionSpan_le_tightVectorSpan P hWF
  · exact selectedPoints_quotient_spans P hWF S

end MOR34
