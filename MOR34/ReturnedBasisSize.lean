import MOR34.BinaryPointBasis
import MOR34.FacetBridge

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- A nonempty spanning affine basis has exactly dimension plus one points. -/
theorem tight_basis_card (P : Model m) (B : Finset (Finset (Item m)))
    (hi : AffineIndependent ℝ (fun t : B => pointVector t.val))
    (hspan : affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P))
    (hT : (tightPointSet P).Nonempty) :
    B.card = Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  classical
  have hbne : B.Nonempty := by
    by_contra hn
    have hem : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := hT
    have hx' : x ∈ affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) := by
      rw [hspan]
      exact subset_affineSpan ℝ _ hx
    simpa [hem] using hx'
  letI : Nonempty B := ⟨⟨hbne.choose, hbne.choose_spec⟩⟩
  have heq : Set.range (fun t : B => pointVector t.val) =
      pointVector '' (B : Set (Finset (Item m))) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t.val, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  have hv := congrArg AffineSubspace.direction hspan
  simp only [direction_affineSpan] at hv
  have hh := hi.finrank_vectorSpan_add_one
  rw [heq, hv] at hh
  simpa using hh.symm

theorem searched_returned_basis_card (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve)
    (rankEval : Finset (Finset (Item m)) → ℕ)
    (hr : ∀ B, rankEval B = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank)
    (hT : (tightPointSet P).Nonempty) :
    (binaryBasisSearch (returnedSets P hWF S solve hs).toList rankEval).card =
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  have hh := searched_returned_basis P hWF S solve hs rankEval hr
  exact tight_basis_card P _ hh.2.2.1 hh.2.2.2 hT

/-- In particular, an accepted facet returns exactly n tight binary basis points. -/
theorem facet_returned_basis_card (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve)
    (rankEval : Finset (Finset (Item m)) → ℕ)
    (hr : ∀ B, rankEval B = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank)
    (hv : Valid P) (hf : IsCodimensionOneFace (knapsackPolytope P) (candidateFace P)) :
    (binaryBasisSearch (returnedSets P hWF S solve hs).toList rankEval).card = Fintype.card (Item m) := by
  obtain ⟨hT, hd⟩ := (candidate_facet_iff_dimension P hWF hv).mp hf
  rw [searched_returned_basis_card P hWF S solve hs rankEval hr hT, hd]
end MOR34
