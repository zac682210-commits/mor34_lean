import MOR34.EdgeWitnesses
import MOR34.CountBasisBridge

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Actual binary sets obtained from retained prefixes and both sides of returned exchanges. -/
noncomputable def returnedSets (P : Model m) (hWF : WellFormed P)
    (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) : Finset (Finset (Item m)) := by
  classical
  exact (selectionFinset P S).image prefixSet ∪
    Finset.univ.image (computedEdgeWitness P hWF solve hs) ∪
    Finset.univ.image (computedEdgeSwap P hWF solve hs)

def returnedPointSet (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) : Set (Item m → ℝ) :=
  pointVector '' (returnedSets P hWF S solve hs : Set (Finset (Item m)))

theorem returnedSets_tight (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    ∀ t ∈ returnedSets P hWF S solve hs, Tight P t := by
  classical
  intro t ht
  simp only [returnedSets, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at ht
  rcases ht with (⟨z, hz, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩
  · have hz' : z ∈ selectedCounts P S := by
      rw [← selectionFinset_coe]; exact hz
    obtain ⟨ε, hn, mode, hz⟩ := hz'
    exact (S.contained ε hn mode hz).1.2.1
  · exact (computedEdgeWitness_pair P hWF solve hs e).1
  · exact (computedEdgeWitness_pair P hWF solve hs e).2.1

theorem returnedPointSet_subset (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    returnedPointSet P hWF S solve hs ⊆ tightPointSet P := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, returnedSets_tight P hWF S solve hs t ht, rfl⟩

theorem selectedPoints_returned (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    selectedPoints P S ⊆ returnedPointSet P hWF S solve hs := by
  classical
  rintro x ⟨z, hz, rfl⟩
  refine ⟨prefixSet z, ?_, rfl⟩
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, rfl⟩
  rw [← selectionFinset_coe] at hz
  exact hz

theorem returnedSets_card (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve)
    (hsmall : ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) :
    (returnedSets P hWF S solve hs).card ≤ (q + 1) * 6 ^ q + 2 * Fintype.card (Item m) := by
  classical
  have hp := Finset.card_image_le (s := selectionFinset P S) (f := prefixSet)
  have hw := Finset.card_image_le (s := Finset.univ) (f := computedEdgeWitness P hWF solve hs)
  have hv := Finset.card_image_le (s := Finset.univ) (f := computedEdgeSwap P hWF solve hs)
  have hu := Finset.card_union_le
    ((selectionFinset P S).image prefixSet)
    (Finset.univ.image (computedEdgeWitness P hWF solve hs))
  have hu' := Finset.card_union_le
    ((selectionFinset P S).image prefixSet ∪ Finset.univ.image (computedEdgeWitness P hWF solve hs))
    (Finset.univ.image (computedEdgeSwap P hWF solve hs))
  have hb := selectionFinset_card P S hsmall
  have he := computedEdges_card solve
  simp only [Finset.card_univ, Fintype.card_coe] at hw hv
  unfold returnedSets
  omega

/-- The two returned points generate each retained augmented direction. -/
theorem returned_direction_span (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    (adjacentDirectionSpan P).map zeroAugment ≤
      augmentedSpan (returnedPointSet P hWF S solve hs) := by
  classical
  rw [← computedEdges_span P hWF solve hs, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, ⟨e, he, rfl⟩, rfl⟩
  let E : computedEdges solve := ⟨e, he⟩
  have hw : pointVector (computedEdgeWitness P hWF solve hs E) ∈
      returnedPointSet P hWF S solve hs := by
    refine ⟨_, ?_, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨E, Finset.mem_univ _, rfl⟩))
  have hv : pointVector (computedEdgeSwap P hWF solve hs E) ∈
      returnedPointSet P hWF S solve hs := by
    refine ⟨_, ?_, rfl⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨E, Finset.mem_univ _, rfl⟩)
  have hh := (augmentedSpan (returnedPointSet P hWF S solve hs)).sub_mem
    (Submodule.subset_span ⟨_, hv, rfl⟩) (Submodule.subset_span ⟨_, hw, rfl⟩)
  have hd := (computedEdgeWitness_pair P hWF solve hs E).2.2
  have heq : pointAugment (pointVector (computedEdgeSwap P hWF solve hs E)) -
      pointAugment (pointVector (computedEdgeWitness P hWF solve hs E)) =
      zeroAugment (unitVector (⟨e.val.1, e.val.2.1⟩ : Item m) -
        unitVector (⟨e.val.1, e.val.2.2⟩ : Item m)) := by
    apply Prod.ext
    · simp [pointAugment, zeroAugment]
    · exact hd
  rwa [heq] at hh

theorem returned_augmented_span (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    augmentedSpan (returnedPointSet P hWF S solve hs) = augmentedSpan (tightPointSet P) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono (returnedPointSet_subset P hWF S solve hs))
  · rw [selected_augmented_span P hWF S]
    exact sup_le (Submodule.span_mono (Set.image_mono (selectedPoints_returned P hWF S solve hs)))
      (returned_direction_span P hWF S solve hs)

theorem returned_affineSpan (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    affineSpan ℝ (returnedPointSet P hWF S solve hs) = affineSpan ℝ (tightPointSet P) := by
  apply le_antisymm
  · exact affineSpan_mono ℝ (returnedPointSet_subset P hWF S solve hs)
  · apply affineSpan_le.mpr
    intro x hx
    apply affineSpan_of_augment_mem
    rw [returned_augmented_span P hWF S solve hs]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

/-- Classical independent subset extraction, not an implemented elimination algorithm. -/
theorem returned_affine_basis_exists (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    ∃ B : Set (Item m → ℝ), B ⊆ returnedPointSet P hWF S solve hs ∧ B.Finite ∧
      affineSpan ℝ B = affineSpan ℝ (tightPointSet P) ∧
      AffineIndependent ℝ ((↑) : B → (Item m → ℝ)) := by
  obtain ⟨B, hB, heq, hi⟩ := exists_affineIndependent ℝ (Item m → ℝ)
    (returnedPointSet P hWF S solve hs)
  exact ⟨B, hB, finite_set_of_fin_dim_affineIndependent ℝ hi,
    heq.trans (returned_affineSpan P hWF S solve hs), hi⟩
end MOR34
