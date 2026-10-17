import MOR34.FiniteBasisSearch
import MOR34.ReturnedPoints

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Augmented 0/1 matrix of a finite list of actual binary sets. -/
def binaryPointMatrix (B : Finset (Finset (Item m))) : Matrix B (Option (Item m)) ℤ
  | t, none => 1
  | t, some i => indicator t.val i

theorem binaryPointMatrix_cast (B : Finset (Finset (Item m))) (t : B) :
    (LinearEquiv.piOptionEquivProd ℝ : (Option (Item m) → ℝ) ≃ₗ[ℝ] ℝ × (Item m → ℝ))
      (fun k => (binaryPointMatrix B t k : ℝ)) = pointAugment (pointVector t.val) := by
  ext <;> simp [binaryPointMatrix, LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd,
    pointAugment, pointVector, indicator]

theorem binaryPointMatrix_rank (B : Finset (Finset (Item m))) :
    ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank =
      Module.finrank ℝ (selectedSpan (K := ℝ) (fun t => pointAugment (pointVector t)) B) := by
  classical
  rw [← integer_matrix_rank, Matrix.rank_eq_finrank_span_row]
  let e : (Option (Item m) → ℝ) ≃ₗ[ℝ] ℝ × (Item m → ℝ) := LinearEquiv.piOptionEquivProd ℝ
  have hm : (Submodule.span ℝ (Set.range ((binaryPointMatrix B).map (Int.castRingHom ℝ)))).map
      e.toLinearMap = selectedSpan (K := ℝ) (fun t => pointAugment (pointVector t)) B := by
    rw [Submodule.map_span, selectedSpan]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.val, t.property, (binaryPointMatrix_cast B t).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, binaryPointMatrix_cast B ⟨t, ht⟩⟩
  rw [← hm]
  exact (e.finrank_map_eq _).symm

/-- Extraction from a supplied list uses only exact ranks of finite integer 0/1 matrices. -/
def binaryBasisSearch (L : List (Finset (Item m)))
    (rankEval : Finset (Finset (Item m)) → ℕ) : Finset (Finset (Item m)) :=
  basisSearch (finiteSpanOracle L (rankOutside rankEval)) (Fintype.card (Item m) + 1) ∅

theorem binaryBasisSearch_correct (L : List (Finset (Item m)))
    (rankEval : Finset (Finset (Item m)) → ℕ)
    (hr : ∀ B, rankEval B = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank) :
    let B := binaryBasisSearch L rankEval
    (∀ t ∈ B, t ∈ L) ∧ B.card ≤ Fintype.card (Item m) + 1 ∧
      AffineIndependent ℝ (fun t : B => pointVector t.val) ∧
      (∀ t ∈ L, pointVector t ∈ affineSpan ℝ (pointVector '' (B : Set (Finset (Item m))))) := by
  have hr' : ∀ B, rankEval B = Module.finrank ℝ
      (selectedSpan (K := ℝ) (fun t => pointAugment (pointVector t)) B) :=
    fun B => (hr B).trans (binaryPointMatrix_rank B)
  have hh := finite_rank_basis_search (K := ℝ) L (fun t => pointAugment (pointVector t)) rankEval hr'
  have hd : Module.finrank ℝ (ℝ × (Item m → ℝ)) = Fintype.card (Item m) + 1 := by
    simp [Module.finrank_prod, Nat.add_comm]
  rw [hd] at hh
  refine ⟨hh.1, hh.2.1, affineIndependent_of_augmented _ hh.2.2.1, ?_⟩
  intro t ht
  apply affineSpan_of_augment_mem
  have hmem := hh.2.2.2 t ht
  simpa only [selectedSpan, augmentedSpan, Set.image_image, Function.comp_def] using hmem

/-- The actual returned finite family yields a searched tight-point affine basis. -/
theorem searched_returned_basis (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve)
    (rankEval : Finset (Finset (Item m)) → ℕ)
    (hr : ∀ B, rankEval B = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank) :
    let B := binaryBasisSearch (returnedSets P hWF S solve hs).toList rankEval
    (∀ t ∈ B, Tight P t) ∧ B.card ≤ Fintype.card (Item m) + 1 ∧
      AffineIndependent ℝ (fun t : B => pointVector t.val) ∧
      affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P) := by
  classical
  let B := binaryBasisSearch (returnedSets P hWF S solve hs).toList rankEval
  have hh := binaryBasisSearch_correct (returnedSets P hWF S solve hs).toList rankEval hr
  have ht : ∀ t ∈ B, Tight P t := by
    intro t ht
    exact returnedSets_tight P hWF S solve hs t (Finset.mem_toList.mp (hh.1 t ht))
  refine ⟨ht, hh.2.1, hh.2.2.1, ?_⟩
  apply le_antisymm
  · apply affineSpan_mono ℝ
    rintro x ⟨t, hb, rfl⟩
    exact ⟨t, ht t hb, rfl⟩
  · rw [← returned_affineSpan P hWF S solve hs]
    apply affineSpan_le.mpr
    rintro x ⟨t, ht, rfl⟩
    exact hh.2.2.2 t (Finset.mem_toList.mpr ht)
end MOR34
