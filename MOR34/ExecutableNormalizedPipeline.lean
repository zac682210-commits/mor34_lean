import MOR34.ExecutableReturnedSets
import MOR34.ExecutableRecognitionBranches

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Finite enumeration and rank-guided basis extraction, relative to the rank primitive. -/
def computedReturnedBasis (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) (ranker : ExactIntegerRank m) : Finset (Finset (Item m)) :=
  binaryBasisSearch (orderedBinarySets (computedReturnedSets P hWF solve hs edgeSolve he))
    (fun B => ranker.evaluate (binaryPointMatrix B))

theorem computedReturnedBasis_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) (ranker : ExactIntegerRank m) :
    let B := computedReturnedBasis P hWF solve hs edgeSolve he ranker
    (∀ t ∈ B, Tight P t) ∧ B.card ≤ Fintype.card (Item m)+1 ∧
      AffineIndependent ℝ (fun t : B => pointVector t.val) ∧
      affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P) := by
  let S := computedCellSelection P hWF solve hs
  let R := computedReturnedSets P hWF solve hs edgeSolve he
  let B := computedReturnedBasis P hWF solve hs edgeSolve he ranker
  have hR : R = returnedSets P hWF S edgeSolve he := computedReturnedSets_eq P hWF solve hs edgeSolve he
  have hh := binaryBasisSearch_correct (orderedBinarySets R)
    (fun B => ranker.evaluate (binaryPointMatrix B)) (fun B => ranker.correct _)
  have ht : ∀ t ∈ B, Tight P t := by
    intro t ht
    apply returnedSets_tight P hWF S edgeSolve he t
    rw [← hR]
    exact (orderedBinarySets_mem R t).mp (hh.1 t ht)
  refine ⟨ht, hh.2.1, hh.2.2.1, ?_⟩
  apply le_antisymm
  · apply affineSpan_mono ℝ
    rintro x ⟨t, hb, rfl⟩
    exact ⟨t, ht t hb, rfl⟩
  · rw [← returned_affineSpan P hWF S edgeSolve he]
    apply affineSpan_le.mpr
    rintro x ⟨t, ht, rfl⟩
    apply hh.2.2.2 t
    apply (orderedBinarySets_mem R t).mpr
    rwa [hR]

/-- The normalized-input procedure contains no classical data-producing choice.
ILP and exact rank remain supplied primitives, with separate contracts. -/
def executableNormalizedPipeline (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  match executableRecognitionBranch (m := m) violate solve with
  | .invalid t => ⟨.invalid t, ∅⟩
  | .empty => ⟨.empty, ∅⟩
  | .supported z =>
    let B := computedReturnedBasis P hWF solve hs edgeSolve he ranker
    ⟨.supported (prefixSet z) (B.card-1) (decide (B.card = Fintype.card (Item m))), B⟩

theorem executableNormalizedPipeline_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (executableNormalizedPipeline P hWF solve hs edgeSolve he violate ranker).Correct P := by
  have hb := executableRecognitionBranch_correct P hWF violate hv solve hs
  unfold executableNormalizedPipeline
  cases ho : executableRecognitionBranch (m := m) violate solve with
  | invalid t =>
    have hh : Feasible P t ∧ P.rhs < candidateValue P t := by
      simpa [ho, RecognitionBranch.Correct] using hb
    exact ⟨by simpa [executableNormalizedPipeline, ho, RecognitionOutput.Correct] using hh, rfl⟩
  | empty =>
    have hh : Valid P ∧ ¬ ∃ t, Tight P t := by simpa [ho, RecognitionBranch.Correct] using hb
    have hnil : tightPointSet P = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      rintro x ⟨t, ht, _⟩
      exact hh.2 ⟨t, ht⟩
    have hf : candidateFace P = ∅ := by rw [candidateFace_eq_hull P hh.1, hnil, convexHull_empty]
    exact ⟨by simpa [executableNormalizedPipeline, ho, RecognitionOutput.Correct] using And.intro hh.1 hf, rfl⟩
  | supported z =>
    have hh : Valid P ∧ BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
      simpa [ho, RecognitionBranch.Correct] using hb
    let B := computedReturnedBasis P hWF solve hs edgeSolve he ranker
    have hB := computedReturnedBasis_correct P hWF solve hs edgeSolve he ranker
    have hT : (tightPointSet P).Nonempty := ⟨pointVector (prefixSet z), _, hh.2.2, rfl⟩
    have hcard : B.card = Module.finrank ℝ (vectorSpan ℝ (tightPointSet P))+1 :=
      tight_basis_card P B hB.2.2.1 hB.2.2.2 hT
    have hd : B.card-1 = Module.finrank ℝ (vectorSpan ℝ (candidateFace P)) := by
      rw [candidateFace_vectorSpan P hh.1]
      omega
    have hf : decide (B.card = Fintype.card (Item m)) = true ↔ DefinesFacet P := by
      simp only [decide_eq_true_eq, DefinesFacet, and_iff_right hh.1]
      rw [candidate_facet_iff_dimension P hWF hh.1, and_iff_right hT, ← hcard]
    change (⟨RecognitionOutput.supported (prefixSet z) (B.card-1)
      (decide (B.card = Fintype.card (Item m))), B⟩ : NormalizedOutput m).Correct P
    refine ⟨⟨hh.1, hh.2.2, hd, hf⟩, hB.1, hB.2.2.1, hB.2.2.2, ?_⟩
    change B.card = B.card-1+1
    omega

theorem executableNormalizedPipeline_facet (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (executableNormalizedPipeline P hWF solve hs edgeSolve he violate ranker).decision.isFacet = true ↔ DefinesFacet P :=
  correct_output_facet P _ (executableNormalizedPipeline_correct P hWF solve hs edgeSolve he violate hv ranker).1

theorem executableNormalizedPipeline_dimension (P : Model m) (hWF : WellFormed P) (hv : Valid P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hviol : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (executableNormalizedPipeline P hWF solve hs edgeSolve he violate ranker).decision.dimension =
      some (candidateFaceDimension P) :=
  correct_output_dimension P _
    (executableNormalizedPipeline_correct P hWF solve hs edgeSolve he violate hviol ranker).1 hv

end MOR34
