import MOR34.RecognitionCertificate
import MOR34.ReturnedBasisSize

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- An external evaluator of exact rational ranks of integer matrices.
This interface does not assert an elimination implementation or a runtime bound. -/
structure ExactIntegerRank (m : Fin q → ℕ) where
  evaluate : {ι : Type} → [Fintype ι] → Matrix ι (Option (Item m)) ℤ → ℕ
  correct : ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Option (Item m)) ℤ),
    evaluate A = (A.map (Int.castRingHom ℚ)).rank

structure BuiltSelection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) where
  forms : Finset (Counts q) → List (IntegerForm q)
  selection : CellBasisSelection P
  extrema_eq : selection.extrema = rowSearchedExtrema P hWF solve hs
  basis_eq : ∀ ε hn mode, selection.basis ε hn mode = basisSearch
    (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) forms)
    (q + 1) ∅
  small : ∀ ε hn mode, (selection.basis ε hn mode).card ≤ q + 1

/-- Existence uses the previously proved integer-normal family construction. -/
theorem builtSelection_exists (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : Nonempty (BuiltSelection P hWF solve hs) := by
  obtain ⟨f, S, he, hb, hc, _, _⟩ := row_solver_cell_selection P hWF solve hs
  exact ⟨⟨f, S, he, hb, hc⟩⟩

/-- Normal forms are classically chosen; the remaining branches use the given solvers. -/
noncomputable def buildSelection (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : BuiltSelection P hWF solve hs :=
  Classical.choice (builtSelection_exists P hWF solve hs)

structure NormalizedOutput (m : Fin q → ℕ) where
  decision : RecognitionOutput m
  basis : Finset (Finset (Item m))

/-- One returned record. For invalid or empty candidates the basis is empty. -/
noncomputable def normalizedPipeline (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  let S := (buildSelection P hWF solve hs).selection
  match computedRecognition P S edgeSolve ranker.evaluate violate solve with
  | .invalid t => ⟨.invalid t, ∅⟩
  | .empty => ⟨.empty, ∅⟩
  | .supported t d b =>
    ⟨.supported t d b, binaryBasisSearch (returnedSets P hWF S edgeSolve he).toList
      (fun B => ranker.evaluate (binaryPointMatrix B))⟩

def NormalizedOutput.Correct (P : Model m) (out : NormalizedOutput m) : Prop :=
  out.decision.Correct P ∧
  match out.decision with
  | .invalid _ => out.basis = ∅
  | .empty => out.basis = ∅
  | .supported _ d _ =>
    (∀ t ∈ out.basis, Tight P t) ∧
    AffineIndependent ℝ (fun t : out.basis => pointVector t.val) ∧
    affineSpan ℝ (pointVector '' (out.basis : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P) ∧
    out.basis.card = d + 1

/-- The complete output contract for normalized input, relative to ILP and exact rank.
Classical normal selection, preprocessing and complexity remain separate obligations. -/
theorem normalizedPipeline_correct (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (normalizedPipeline P hWF solve hs edgeSolve he violate ranker).Correct P := by
  classical
  let S := (buildSelection P hWF solve hs).selection
  have hc := computedRecognition_correct P hWF S edgeSolve he
    ranker.evaluate ranker.correct violate hv solve hs
  have hr : ∀ B : Finset (Finset (Item m)),
      ranker.evaluate (binaryPointMatrix B) = ((binaryPointMatrix B).map (Int.castRingHom ℚ)).rank :=
    fun B => ranker.correct _
  change (match computedRecognition P S edgeSolve ranker.evaluate violate solve with
    | .invalid t => (⟨.invalid t, ∅⟩ : NormalizedOutput m)
    | .empty => ⟨.empty, ∅⟩
    | .supported t d b => ⟨.supported t d b,
      binaryBasisSearch (returnedSets P hWF S edgeSolve he).toList
        (fun B => ranker.evaluate (binaryPointMatrix B))⟩).Correct P
  cases ho : computedRecognition P S edgeSolve ranker.evaluate violate solve with
  | invalid t =>
    rw [ho] at hc
    exact ⟨hc, rfl⟩
  | empty =>
    rw [ho] at hc
    exact ⟨hc, rfl⟩
  | supported t d b =>
    rw [ho] at hc
    have hT : (tightPointSet P).Nonempty := ⟨pointVector t, t, hc.2.1, rfl⟩
    have hb := searched_returned_basis P hWF S edgeSolve he
      (fun B => ranker.evaluate (binaryPointMatrix B)) hr
    have hcard := searched_returned_basis_card P hWF S edgeSolve he
      (fun B => ranker.evaluate (binaryPointMatrix B)) hr hT
    have hd : d = Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) := by
      rw [hc.2.2.1, candidateFace_vectorSpan P hc.1]
    exact ⟨hc, hb.1, hb.2.2.1, hb.2.2.2, by simpa [hd] using hcard⟩
end MOR34
