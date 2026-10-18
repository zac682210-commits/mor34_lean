import MOR34.RawBasis

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

inductive RawDecision (n : ℕ) where
  | invalid (witness : Finset (Fin n))
  | empty
  | supported (witness : Finset (Fin n)) (dimension : ℕ) (facet : Bool)

def RawDecision.isFacet : RawDecision n → Bool
  | .invalid _ => false
  | .empty => false
  | .supported _ _ b => b

def RawDecision.dimension : RawDecision n → Option ℤ
  | .invalid _ => none
  | .empty => some (-1)
  | .supported _ d _ => some (d : ℤ)

def RawDecision.Correct (a c : Fin n → ℤ) (b d : ℤ) : RawDecision n → Prop
  | .invalid S => RawFeasible a b S ∧ d < ∑ i ∈ S, c i
  | .empty => RawValid a c b d ∧ rawCandidateFace a c b d = ∅
  | .supported S k f => RawValid a c b d ∧ RawTight a c b d S ∧
      k = Module.finrank ℝ (vectorSpan ℝ (rawCandidateFace a c b d)) ∧
      (f = true ↔ RawDefinesFacet a c b d)

def relabelDecision (e : Item m ≃ Fin n) : RecognitionOutput m → RawDecision n
  | .invalid S => .invalid (S.map e.toEmbedding)
  | .empty => .empty
  | .supported S k f => .supported (S.map e.toEmbedding) k f

structure RawOutput (n : ℕ) where
  decision : RawDecision n
  basis : Finset (Finset (Fin n))

def RawOutput.Correct (a c : Fin n → ℤ) (b d : ℤ) (out : RawOutput n) : Prop :=
  out.decision.Correct a c b d ∧
  match out.decision with
  | .invalid _ => out.basis = ∅
  | .empty => out.basis = ∅
  | .supported _ k _ =>
    (∀ S ∈ out.basis, RawTight a c b d S) ∧
    AffineIndependent ℝ (fun S : out.basis => rawPointVector S.val) ∧
    affineSpan ℝ (rawPointVector '' (out.basis : Set (Finset (Fin n)))) =
      affineSpan ℝ (rawTightPointSet a c b d) ∧
    out.basis.card = k + 1

def relabelOutput (e : Item m ≃ Fin n) (out : NormalizedOutput m) : RawOutput n :=
  ⟨relabelDecision e out.decision, relabelBasis e out.basis⟩

theorem relabelDecision_correct (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (out : RecognitionOutput m) (h : out.Correct P) :
    (relabelDecision e out).Correct a c P.capacity P.rhs := by
  cases out with
  | invalid S =>
    refine ⟨(relabel_feasible P e a ha S).mp h.1, ?_⟩
    rw [← relabel_candidate_sum P e c hc]
    exact h.2
  | empty =>
    refine ⟨(relabel_valid P e a c ha hc).mp h.1, ?_⟩
    rw [relabel_candidateFace P h.1 e a c ha hc, h.2, Set.image_empty]
  | supported S k f =>
    refine ⟨(relabel_valid P e a c ha hc).mp h.1,
      (relabel_tight P e a c ha hc S).mp h.2.1, ?_, ?_⟩
    · rw [relabel_face_finrank P h.1 e a c ha hc]
      exact h.2.2.1
    · exact h.2.2.2.trans (relabel_definesFacet P e a c ha hc).symm

theorem relabelOutput_correct (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (out : NormalizedOutput m) (h : out.Correct P) :
    (relabelOutput e out).Correct a c P.capacity P.rhs := by
  refine ⟨relabelDecision_correct P e a c ha hc out.decision h.1, ?_⟩
  rcases out with ⟨o, B⟩
  cases o with
  | invalid S =>
    have hB : B = ∅ := h.2
    simp [relabelOutput, relabelDecision, relabelBasis, hB]
  | empty =>
    have hB : B = ∅ := h.2
    simp [relabelOutput, relabelDecision, relabelBasis, hB]
  | supported S k f =>
    have hb : (∀ t ∈ B, Tight P t) ∧
        AffineIndependent ℝ (fun t : B => pointVector t.val) ∧
        affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P) ∧
        B.card = k + 1 := h.2
    exact ⟨relabelBasis_tight P e a c ha hc B hb.1, relabelBasis_independent e B hb.2.1,
      relabelBasis_affineSpan P e a c ha hc B hb.2.2.1, (relabelBasis_card e B).trans hb.2.2.2⟩

theorem raw_correct_output_facet (a c : Fin n → ℤ) (b d : ℤ) (out : RawDecision n)
    (h : out.Correct a c b d) : out.isFacet = true ↔ RawDefinesFacet a c b d := by
  cases out with
  | invalid S =>
    change (false = true) ↔ _
    have hn : ¬ RawDefinesFacet a c b d := fun hf => not_lt_of_ge (hf.1 S h.1) h.2
    simp [hn]
  | empty =>
    change (false = true) ↔ _
    have hn : ¬ RawDefinesFacet a c b d := by
      intro hf
      have hh := hf.2.1
      rw [h.2] at hh
      exact Set.not_nonempty_empty hh
    simp [hn]
  | supported S k f => exact h.2.2.2

theorem relabelDecision_dimension (e : Item m ≃ Fin n) (out : RecognitionOutput m) :
    (relabelDecision e out).dimension = out.dimension := by cases out <;> rfl

/-- The normalized bounded search, returned in the original item coordinates. -/
noncomputable def rawPipeline (P : Model m) (hWF : WellFormed P) (e : Item m ≃ Fin n)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (ranker : ExactIntegerRank m) : RawOutput n :=
  relabelOutput e (boundedPipeline P hWF solve hs edgeSolve he violate ranker)

theorem rawPipeline_correct (P : Model m) (hWF : WellFormed P) (e : Item m ≃ Fin n)
    (a c : Fin n → ℤ) (ha : ∀ i, P.weight i = a (e i))
    (hc : ∀ i, P.coefficient i.1 = c (e i))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (rawPipeline P hWF e solve hs edgeSolve he violate ranker).Correct a c P.capacity P.rhs :=
  relabelOutput_correct P e a c ha hc _
    (boundedPipeline_correct P hWF solve hs edgeSolve he violate hv ranker)

theorem rawPipeline_facet (P : Model m) (hWF : WellFormed P) (e : Item m ≃ Fin n)
    (a c : Fin n → ℤ) (ha : ∀ i, P.weight i = a (e i))
    (hc : ∀ i, P.coefficient i.1 = c (e i))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (rawPipeline P hWF e solve hs edgeSolve he violate ranker).decision.isFacet = true ↔
      RawDefinesFacet a c P.capacity P.rhs :=
  raw_correct_output_facet _ _ _ _ _
    (rawPipeline_correct P hWF e a c ha hc solve hs edgeSolve he violate hv ranker).1

theorem rawPipeline_dimension (P : Model m) (hWF : WellFormed P) (e : Item m ≃ Fin n)
    (a c : Fin n → ℤ) (ha : ∀ i, P.weight i = a (e i))
    (hc : ∀ i, P.coefficient i.1 = c (e i)) (hvalid : RawValid a c P.capacity P.rhs)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (rawPipeline P hWF e solve hs edgeSolve he violate ranker).decision.dimension =
      some (rawSignedDimension a c P.capacity P.rhs) := by
  change (relabelDecision e (boundedPipeline P hWF solve hs edgeSolve he violate ranker).decision).dimension = _
  rw [relabelDecision_dimension]
  exact boundedPipeline_raw_dimension P hWF ((relabel_valid P e a c ha hc).mpr hvalid)
    e a c ha hc solve hs edgeSolve he violate hv ranker

end MOR34
