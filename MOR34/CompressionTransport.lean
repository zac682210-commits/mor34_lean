import MOR34.CompressionSigns
import MOR34.ExecutableNormalization

namespace MOR34
variable {n : ℕ} {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}

/-- Only the two sign-preservation conclusions of the cited compression theorem. -/
structure RawCompression (a c a' c' : Fin n → ℤ) (b d b' d' : ℤ) : Prop where
  weightSigns : PreservesSmallSigns (n+1) (augmentedWeights a b) (augmentedWeights a' b')
  candidateSigns : PreservesSmallSigns (n+1) (augmentedWeights c d) (augmentedWeights c' d')

theorem compression_feasible (h : RawCompression a c a' c' b d b' d') (S : Finset (Fin n)) :
    RawFeasible a b S ↔ RawFeasible a' b' S := compression_subset_le h.weightSigns S

theorem compression_tight (h : RawCompression a c a' c' b d b' d') (S : Finset (Fin n)) :
    RawTight a c b d S ↔ RawTight a' c' b' d' S := by
  exact and_congr (compression_feasible h S) (compression_subset_eq h.candidateSigns S)

theorem compression_valid (h : RawCompression a c a' c' b d b' d') :
    RawValid a c b d ↔ RawValid a' c' b' d' := by
  constructor
  · intro hv S hS
    exact (compression_subset_le h.candidateSigns S).mp (hv S ((compression_feasible h S).mpr hS))
  · intro hv S hS
    exact (compression_subset_le h.candidateSigns S).mpr (hv S ((compression_feasible h S).mp hS))

theorem compression_tightPointSet (h : RawCompression a c a' c' b d b' d') :
    rawTightPointSet a c b d = rawTightPointSet a' c' b' d' := by
  ext x
  simp only [rawTightPointSet, Set.mem_setOf_eq, compression_tight h]

theorem compression_polytope (h : RawCompression a c a' c' b d b' d') :
    rawKnapsackPolytope a b = rawKnapsackPolytope a' b' := by
  have he : rawFeasiblePointSet a b = rawFeasiblePointSet a' b' := by
    ext x
    simp only [rawFeasiblePointSet, Set.mem_setOf_eq, compression_feasible h]
  simp only [rawKnapsackPolytope, he]

/-- Face equality uses validity; arbitrary intersecting hyperplanes need not be preserved. -/
theorem compression_face (h : RawCompression a c a' c' b d b' d') (hv : RawValid a c b d) :
    rawCandidateFace a c b d = rawCandidateFace a' c' b' d' := by
  rw [rawCandidateFace_eq_hull _ _ _ _ hv,
    rawCandidateFace_eq_hull _ _ _ _ ((compression_valid h).mp hv), compression_tightPointSet h]

theorem compression_facet (h : RawCompression a c a' c' b d b' d') :
    RawDefinesFacet a c b d ↔ RawDefinesFacet a' c' b' d' := by
  constructor
  · rintro ⟨hv,hf⟩
    refine ⟨(compression_valid h).mp hv, ?_⟩
    rwa [compression_polytope h, compression_face h hv] at hf
  · rintro ⟨hv,hf⟩
    have hv' := (compression_valid h).mpr hv
    refine ⟨hv', ?_⟩
    rwa [compression_polytope h, compression_face h hv']

theorem compression_signedDimension (h : RawCompression a c a' c' b d b' d') :
    rawSignedDimension a c b d = rawSignedDimension a' c' b' d' := by
  simp only [rawSignedDimension, compression_tightPointSet h]

theorem compression_hypotheses (hn : 0 < n) (h : RawCompression a c a' c' b d b' d')
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i) :
    (∀ i, 0 < a' i) ∧ 0 < b' ∧ (∀ i, a' i ≤ b') ∧ (∀ i, 0 ≤ c' i) := by
  have h1 : 1 ≤ n+1 := by omega
  have h2 : 2 ≤ n+1 := by omega
  exact ⟨fun i => (smallSigns_positive h.weightSigns h1 (some i)).mp (ha i),
    (smallSigns_positive h.weightSigns h1 none).mp hb,
    fun i => (smallSigns_order h.weightSigns h2 (some i) none).mp (hab i),
    fun i => (smallSigns_nonnegative h.candidateSigns h1 (some i)).mp (hc i)⟩

theorem compression_decision (h : RawCompression a c a' c' b d b' d') (out : RawDecision n) :
    out.Correct a c b d ↔ out.Correct a' c' b' d' := by
  cases out with
  | invalid S =>
    have he : d < ∑ i ∈ S, c i ↔ d' < ∑ i ∈ S, c' i := by
      simpa only [not_le] using (compression_subset_le h.candidateSigns S).not
    exact and_congr (compression_feasible h S) he
  | empty =>
    change (RawValid a c b d ∧ rawCandidateFace a c b d = ∅) ↔
      (RawValid a' c' b' d' ∧ rawCandidateFace a' c' b' d' = ∅)
    constructor
    · rintro ⟨hv,he⟩
      exact ⟨(compression_valid h).mp hv, (compression_face h hv).symm.trans he⟩
    · rintro ⟨hv,he⟩
      have hv' := (compression_valid h).mpr hv
      exact ⟨hv', (compression_face h hv').trans he⟩
  | supported S k f =>
    change (RawValid a c b d ∧ RawTight a c b d S ∧
      k = Module.finrank ℝ (vectorSpan ℝ (rawCandidateFace a c b d)) ∧
      (f = true ↔ RawDefinesFacet a c b d)) ↔ _
    by_cases hv : RawValid a c b d
    · simp only [hv, (compression_valid h).mp hv, true_and, compression_tight h,
        compression_face h hv, compression_facet h]
    · have hv' : ¬ RawValid a' c' b' d' := fun hh => hv ((compression_valid h).mpr hh)
      simp [RawDecision.Correct, hv, hv']

/-- The same actual output record, including its tight binary basis, transfers unchanged. -/
theorem compression_output (h : RawCompression a c a' c' b d b' d') (out : RawOutput n) :
    out.Correct a c b d ↔ out.Correct a' c' b' d' := by
  unfold RawOutput.Correct
  rw [compression_decision h]
  cases out.decision <;> simp only [compression_tight h, compression_tightPointSet h]

end MOR34
