import MOR34.FacetBridge
import MOR34.ExecutedCells
import MOR34.ReturnedPoints
import MOR34.RecognitionBranches

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Validity is part of saying that the candidate inequality defines a facet. -/
def DefinesFacet (P : Model m) : Prop :=
  Valid P ∧ IsCodimensionOneFace (knapsackPolytope P) (candidateFace P)

inductive RecognitionOutput (m : Fin q → ℕ) where
  | invalid (witness : Finset (Item m))
  | empty
  | supported (witness : Finset (Item m)) (dimension : ℕ) (facet : Bool)

def RecognitionOutput.isFacet : RecognitionOutput m → Bool
  | .invalid _ => false
  | .empty => false
  | .supported _ _ b => b

/-- The exact-rank primitive has a separate, explicit correctness hypothesis. -/
noncomputable def computedRecognition (P : Model m) (S : CellBasisSelection P)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (rankEval : Matrix (ComputedRowIndex P S edgeSolve) (Option (Item m)) ℤ → ℕ)
    (violate : Option (IntegerRowSolution q))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : RecognitionOutput m :=
  match recognitionBranch (m := m) violate solve with
  | .invalid t => .invalid t
  | .empty => .empty
  | .supported z =>
    let r := rankEval (computedMatrix P S edgeSolve)
    .supported (prefixSet z) (r - 1) (decide (r = Fintype.card (Item m)))

def RecognitionOutput.Correct (P : Model m) : RecognitionOutput m → Prop
  | .invalid t => Feasible P t ∧ P.rhs < candidateValue P t
  | .empty => Valid P ∧ candidateFace P = ∅
  | .supported t d b => Valid P ∧ Tight P t ∧
      d = Module.finrank ℝ (vectorSpan ℝ (candidateFace P)) ∧
      (b = true ↔ DefinesFacet P)

/-- End-to-end branch and rank correctness for the normalized grouped model.
This does not implement ILP or exact rational elimination. -/
theorem computedRecognition_correct (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (rankEval : Matrix (ComputedRowIndex P S edgeSolve) (Option (Item m)) ℤ → ℕ)
    (hr : ∀ A, rankEval A = (A.map (Int.castRingHom ℚ)).rank)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    (computedRecognition P S edgeSolve rankEval violate solve).Correct P := by
  have hb := recognitionBranch_correct P hWF violate hv solve hs
  cases ht : recognitionBranch (m := m) violate solve with
  | invalid t =>
    simpa [computedRecognition, ht, RecognitionOutput.Correct, RecognitionBranch.Correct] using hb
  | empty =>
    have hh : Valid P ∧ ¬ ∃ t, Tight P t := by
      simpa [ht, RecognitionBranch.Correct] using hb
    have hnil : tightPointSet P = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      rintro x ⟨t, ht, _⟩
      exact hh.2 ⟨t, ht⟩
    have hf : candidateFace P = ∅ := by rw [candidateFace_eq_hull P hh.1, hnil, convexHull_empty]
    simpa [computedRecognition, ht, RecognitionOutput.Correct] using And.intro hh.1 hf
  | supported z =>
    have hh : Valid P ∧ BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
      simpa [ht, RecognitionBranch.Correct] using hb
    have hT : (tightPointSet P).Nonempty := ⟨pointVector (prefixSet z), _, hh.2.2, rfl⟩
    have hdim := computed_matrix_rank P hWF S edgeSolve he hT
    have hfacet := candidate_facet_iff_computed_rank P hWF hh.1 S edgeSolve he hT
    simp only [computedRecognition, ht, RecognitionOutput.Correct]
    refine ⟨hh.1, hh.2.2, ?_, ?_⟩
    · rw [hr, hdim, candidateFace_vectorSpan P hh.1]
      omega
    · simp only [decide_eq_true_eq, hr, DefinesFacet]
      exact hfacet.symm.trans (and_iff_right hh.1).symm

theorem correct_output_facet (P : Model m) (o : RecognitionOutput m) (h : o.Correct P) :
    o.isFacet = true ↔ DefinesFacet P := by
  cases o with
  | invalid t =>
    change (false = true) ↔ _
    have hn : ¬ DefinesFacet P := fun hf => not_lt_of_ge (hf.1 t h.1) h.2
    simp [hn]
  | empty =>
    change (false = true) ↔ _
    have hn : ¬ DefinesFacet P := by
      intro hf
      have hh := hf.2.1
      rw [h.2] at hh
      exact Set.not_nonempty_empty hh
    simp [hn]
  | supported t d b => exact h.2.2.2

/-- A well-formed input, its three row solvers and an exact rank evaluator decide facetness. -/
theorem computedRecognition_facet (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (rankEval : Matrix (ComputedRowIndex P S edgeSolve) (Option (Item m)) ℤ → ℕ)
    (hr : ∀ A, rankEval A = (A.map (Int.castRingHom ℚ)).rank)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    (computedRecognition P S edgeSolve rankEval violate solve).isFacet = true ↔ DefinesFacet P :=
  correct_output_facet P _ (computedRecognition_correct P hWF S edgeSolve he rankEval hr violate hv solve hs)
end MOR34
