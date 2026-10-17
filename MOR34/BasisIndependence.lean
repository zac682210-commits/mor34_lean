import MOR34.CountBasisBridge
import MOR34.RankScalar

namespace MOR34

/-- The growing selection remains independent, rather than merely small and spanning. -/
theorem basisSearch_independent {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq α] (C : Set α) (v : α → V)
    (oracle : Finset α → Option α) (ho : SpanOracleSpec (K := K) C v oracle)
    (n : ℕ) (B : Finset α) (hb : LinearIndepOn K v (B : Set α)) :
    LinearIndepOn K v (↑(basisSearch oracle n B) : Set α) := by
  induction n generalizing B with
  | zero => exact hb
  | succ n ih =>
    cases h : oracle B with
    | none => simpa [basisSearch, h] using hb
    | some a =>
      simp only [basisSearch, h]
      apply ih
      have hn := (ho.found B a h).2
      have ha : a ∉ (B : Set α) := by
        intro ha
        exact hn (Submodule.subset_span ⟨a, ha, rfl⟩)
      simpa only [Finset.coe_insert] using (linearIndepOn_insert ha).mpr ⟨hb, hn⟩

/-- Rational row independence survives the specific entrywise embedding into the reals. -/
theorem rational_row_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (hA : LinearIndependent ℚ A) :
    LinearIndependent ℝ (A.map (Rat.castHom ℝ)) := by
  classical
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ))))
  have h := linearIndependent_iff_card_eq_finrank_span.mp hA
  change Fintype.card ι = Module.finrank ℚ (Submodule.span ℚ (Set.range A)) at h
  calc
    Fintype.card ι = A.rank := by
      simpa only [Matrix.rank_eq_finrank_span_row, Matrix.row] using h
    _ = (A.map (Rat.castHom ℝ)).rank := (rational_matrix_rank A).symm
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)))) := by
      simpa only [Matrix.row] using Matrix.rank_eq_finrank_span_row (A.map (Rat.castHom ℝ))

theorem rational_augmented_independent_to_real {q : ℕ} (B : Finset (Counts q))
    (hB : LinearIndepOn ℚ rationalCountPoint (B : Set (Counts q))) :
    LinearIndependent ℝ (fun z : B => pointAugment (countReal z.val)) := by
  classical
  let eQ : (Option (Fin q) → ℚ) ≃ₗ[ℚ] ℚ × (Fin q → ℚ) := LinearEquiv.piOptionEquivProd ℚ
  let eR : (Option (Fin q) → ℝ) ≃ₗ[ℝ] ℝ × (Fin q → ℝ) := LinearEquiv.piOptionEquivProd ℝ
  let A : Matrix B (Option (Fin q)) ℚ := fun z => eQ.symm (rationalCountPoint z.val)
  have hi : LinearIndependent ℚ (fun z : B => rationalCountPoint z.val) := hB
  have hQ : LinearIndependent ℚ A := hi.map' eQ.symm.toLinearMap (LinearMap.ker_eq_bot.mpr eQ.symm.injective)
  have hR := (rational_row_independent A hQ).map' eR.toLinearMap (LinearMap.ker_eq_bot.mpr eR.injective)
  convert hR using 1
  funext z
  ext <;> simp [A, eQ, eR, Matrix.map, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd, pointAugment, rationalCountPoint, countReal]

/-- Augmented linear independence implies affine independence of the original real points. -/
theorem affineIndependent_of_augmented {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ι → V) (hp : LinearIndependent ℝ (fun i => pointAugment (p i))) :
    AffineIndependent ℝ p := by
  rw [affineIndependent_iff]
  intro s w hw hs i hi
  have he : ∑ j ∈ s, w j • pointAugment (p j) = 0 := by
    apply Prod.ext
    · simpa [pointAugment, Prod.fst_sum] using hw
    · simpa [pointAugment, Prod.snd_sum] using hs
  exact (linearIndependent_iff'.mp hp) s w he i hi

/-- The actual count procedure returns an affinely independent real generating set. -/
theorem real_count_search_independent {q : ℕ} (C : Set (Counts q))
    (oracle : Finset (Counts q) → Option (Counts q))
    (ho : SpanOracleSpec (K := ℚ) C rationalCountPoint oracle) :
    let B := basisSearch oracle (q + 1) ∅
    AffineIndependent ℝ (fun z : B => countReal z.val) := by
  classical
  apply affineIndependent_of_augmented
  apply rational_augmented_independent_to_real
  apply basisSearch_independent C rationalCountPoint oracle ho
  simp

end MOR34

namespace MOR34

/-- Full real affine-basis output and quadratic query count, relative to linear feasibility. -/
theorem real_affine_basis_from_linear_oracle {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q),
    let B := basisSearch (linearSpanOracle solve forms) (q + 1) ∅
    (B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      AffineIndependent ℝ (fun z : B => countReal z.val) ∧
      (∀ z ∈ C, countReal z ∈ affineSpan ℝ (countReal '' (B : Set (Counts q)))) ∧
      linearBasisCalls solve forms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  obtain ⟨forms, hf, hsize⟩ := bounded_integer_forms_family (q := q)
  have ho := linearSpanOracle_spec C solve hs forms hf
  have hc := linear_count_basis_correct C solve hs forms hf hsize
  dsimp at hc
  refine ⟨forms, hc.1, hc.2.1, real_count_search_independent C _ ho, ?_, hc.2.2.2⟩
  intro z hz
  exact countReal_affineSpan_of_rational_span _ z (hc.2.2.1 z hz)

end MOR34
