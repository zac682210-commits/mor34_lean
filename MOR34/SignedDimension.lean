import MOR34.NormalizedPipeline

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Invalid candidates have no reported face dimension; empty faces report -1. -/
def RecognitionOutput.dimension : RecognitionOutput m → Option ℤ
  | .invalid _ => none
  | .empty => some (-1)
  | .supported _ d _ => some (d : ℤ)

noncomputable def candidateFaceDimension (P : Model m) : ℤ := by
  classical
  exact if (candidateFace P).Nonempty then
    (Module.finrank ℝ (vectorSpan ℝ (candidateFace P)) : ℤ) else -1

/-- The signed dimension convention agrees with the actual equality face on valid inputs. -/
theorem correct_output_dimension (P : Model m) (o : RecognitionOutput m)
    (hc : o.Correct P) (hv : Valid P) :
    o.dimension = some (candidateFaceDimension P) := by
  classical
  cases o with
  | invalid t =>
    exact False.elim (not_lt_of_ge (hv t hc.1) hc.2)
  | empty => simp [RecognitionOutput.dimension, candidateFaceDimension, hc.2]
  | supported t d b =>
    have ht : (tightPointSet P).Nonempty := ⟨pointVector t, t, hc.2.1, rfl⟩
    have hn := (candidateFace_nonempty_iff P hv).mpr ht
    simp only [RecognitionOutput.dimension, candidateFaceDimension, if_pos hn, hc.2.2.1]

theorem normalizedPipeline_dimension (P : Model m) (hWF : WellFormed P) (hv : Valid P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hviol : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (normalizedPipeline P hWF solve hs edgeSolve he violate ranker).decision.dimension =
      some (candidateFaceDimension P) :=
  correct_output_dimension P _
    (normalizedPipeline_correct P hWF solve hs edgeSolve he violate hviol ranker).1 hv
end MOR34
