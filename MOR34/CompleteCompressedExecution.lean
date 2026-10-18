import MOR34.ChargedCompressionPreparation

namespace MOR34
variable {n : ℕ} {a v : Fin n → ℤ} {b rhs : ℤ}

/-- A single retained preparation result is used by the weighted core. -/
def runPreparedWeighted (prepared : CompressedPreparedInput a v b rhs × ℕ)
    (s : WeightedRunPrimitives prepared.1.normalization) : RawOutput n × ℕ :=
  let core := s.run prepared.1.normalization
  (core.1,prepared.2+core.2+1)

theorem runPreparedWeighted_correct (prepared : CompressedPreparedInput a v b rhs × ℕ)
    (s : WeightedRunPrimitives prepared.1.normalization) :
    (runPreparedWeighted prepared s).1.Correct a v b rhs :=
  (compression_output prepared.1.relation _).mpr (weightedRun_correct prepared.1.normalization s)

theorem compressedPrepared_exponent (n : ℕ) : 7*(n+1)^3 ≤ 18*(n+1)^4 := by
  have h := Nat.mul_le_mul_left (7*(n+1)^3) (show 1 ≤ n+1 by omega)
  nlinarith [show (n+1)^4=(n+1)^3*(n+1) by ring]

/-- The end budget is derived below from the three preprocessing calls and
all weighted core phases. Its input degree is independent of q. -/
def compressedEndBudget (q n L G ep W ec : ℕ) : ℕ :=
  preparationBudget n L G ep+(q+6)^(W*(q+1))*20^ec*(n+1)^(4*ec)+1

theorem compressedEndBudget_sharp (G ep W ec : ℕ) :
    SharpPolynomial (fun q n L => compressedEndBudget q n L G ep W ec) := by
  have hW : ParameterGrowth (fun q => (q+6)^(W*(q+1))) := ⟨W,fun _ => le_rfl⟩
  unfold compressedEndBudget preparationBudget
  sharp_polynomial

theorem sharp_parameter_transport (q K W : ℕ) (h : q ≤ K+1) :
    (q+6)^(W*(q+1)) ≤ (K+7)^((2*W)*(K+1)) := by
  exact (pow_le_pow_left' (by omega : q+6 ≤ K+7) _).trans
    (pow_le_pow_right' (by omega) (by nlinarith : W*(q+1) ≤ 2*W*(K+1)))

/-- Full original-input compressed application. The sole algorithmic premises
are contracts for standard compression, grouping/sorting, integer feasibility,
rank and elementary data/arithmetic primitives. No core-cost premise is used. -/
set_option maxHeartbeats 800000 in
theorem complete_compressed_execution (I BI H K : ℕ → ℕ) (c bc ae d G ep : ℕ)
    (hI : ParameterGrowth I) (hBI : ParameterGrowth BI)
    (hH : ParameterGrowth H) (hK : ParameterGrowth K) :
    ∃ e W : ℕ, ∀ {n : ℕ} (hn : 0 < n) (a v : Fin n → ℤ) (b rhs : ℤ)
      (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ v i)
      (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n),
      PreparationLocalBounds ft normalize G ep →
    ∀ s : WeightedRunPrimitives
      (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).1.normalization,
      WeightedRunBounds _ s I BI H K c bc ae d →
      s.arithmetic.base.L = 7*(n+1)^3 →
      (runPreparedWeighted (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize) s).1.Correct a v b rhs ∧
      (runPreparedWeighted (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize) s).2 ≤
        ((((Finset.univ.image v).filter (fun z => 0 < z)).card)+7)^
          (W*((((Finset.univ.image v).filter (fun z => 0 < z)).card)+1))*
          (n+rawIntegerPayload a v b rhs+2)^e := by
  obtain ⟨ec,Wc,hcore⟩ := weightedRun_sharp I BI H K c bc ae d hI hBI hH hK
  obtain ⟨e,W,henv⟩ := compressedEndBudget_sharp G ep Wc ec
  refine ⟨e,2*W,?_⟩
  intro n hn a v b rhs ha hb hab hc ft normalize hp s hs hL
  let prep := chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize
  have hcorrect := runPreparedWeighted_correct prep s
  have hc' := (hcore prep.1.normalization s hs).2
  have hn' : Fintype.card (Item prep.1.normalization.sizes) = n := by
    simpa using Fintype.card_congr prep.1.normalization.itemEquiv
  have hsize : s.arithmetic.base.L ≤ 18*(n+1)^4 := by
    rw [hL]; exact compressedPrepared_exponent n
  have hcc := compression_cost_substitution_two n s.arithmetic.base.L
    ((prep.1.normalization.classes+6)^(Wc*(prep.1.normalization.classes+1))) ec _ hsize hc'
  have hprep := chargedCompressionPreparation_cost hn a v b rhs ha hb hab hc ft normalize G ep hp
  have hsum : (runPreparedWeighted prep s).2 ≤
      compressedEndBudget prep.1.normalization.classes n (rawIntegerPayload a v b rhs) G ep Wc ec := by
    dsimp only [runPreparedWeighted,compressedEndBudget]
    exact Nat.add_le_add_right (Nat.add_le_add hprep hcc) 1
  have hh := hsum.trans (henv prep.1.normalization.classes n (rawIntegerPayload a v b rhs))
  have hq := compressedPrepared_parameter hn prep.1
  have ht := Nat.mul_le_mul_right ((n+rawIntegerPayload a v b rhs+2)^e)
    (sharp_parameter_transport _ _ W hq)
  exact ⟨hcorrect,hh.trans ht⟩

end MOR34
