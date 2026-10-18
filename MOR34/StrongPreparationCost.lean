import MOR34.CompleteCompressedExecution

namespace MOR34
variable {n : ℕ}

/-- The strongly polynomial arithmetic-time version of the established
Frank--Tardos contract. It is distinct from its bit-time contract. -/
structure PreparationStrongBounds (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n)
    (G e : ℕ) : Prop where
  compress : ∀ w, (ft.run w).2 ≤ G*(n+2)^e
  normalize : ∀ hn a v b rhs ha hb hab hc,
    (normalize.run hn a v b rhs ha hb hab hc).2 ≤ G*(n+rawIntegerPayload a v b rhs+2)^e

theorem chargedCompressionPreparation_strong_cost (hn : 0 < n) (a v : Fin n → ℤ) (b rhs : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ v i)
    (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n) (G e : ℕ)
    (h : PreparationStrongBounds ft normalize G e) :
    (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).2 ≤
      preparationBudget n 0 G e := by
  have h₁ := h.compress (augmentedWeights a b)
  have h₂ := h.compress (augmentedWeights v rhs)
  let p := (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).1
  have hp := compressedPrepared_size p
  have hcond := compression_hypotheses hn p.relation ha hb hab hc
  have h₃ := h.normalize hn p.weights p.coefficients p.capacity p.level
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have h₄ := h₃.trans (Nat.mul_le_mul_left G
    (pow_le_pow_left' (Nat.add_le_add_right (Nat.add_le_add_left hp n) 2) e))
  dsimp only [p,chargedCompressionPreparation] at h₄ ⊢
  unfold preparationBudget
  simp only [Nat.add_zero]
  omega

set_option maxHeartbeats 800000 in
/-- Magnitude-independent arithmetic-operation consequence. Compression itself
uses its established strongly polynomial contract; the compressed core and all
new application steps are the same retained execution as above. -/
theorem complete_strongly_polynomial_execution (I BI H K : ℕ → ℕ) (c bc ae d G ep : ℕ)
    (hI : ParameterGrowth I) (hBI : ParameterGrowth BI)
    (hH : ParameterGrowth H) (hK : ParameterGrowth K) :
    ∃ e W : ℕ, ∀ {n : ℕ} (hn : 0 < n) (a v : Fin n → ℤ) (b rhs : ℤ)
      (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ v i)
      (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n),
      PreparationStrongBounds ft normalize G ep →
    ∀ s : WeightedRunPrimitives
      (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).1.normalization,
      WeightedRunBounds _ s I BI H K c bc ae d →
      s.arithmetic.base.L = 7*(n+1)^3 →
      (runPreparedWeighted (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize) s).1.Correct a v b rhs ∧
      (runPreparedWeighted (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize) s).2 ≤
        ((((Finset.univ.image v).filter (fun z => 0 < z)).card)+7)^
          (W*((((Finset.univ.image v).filter (fun z => 0 < z)).card)+1))*
          (n+2)^e := by
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
  have hprep := chargedCompressionPreparation_strong_cost hn a v b rhs ha hb hab hc ft normalize G ep hp
  have hsum : (runPreparedWeighted prep s).2 ≤
      compressedEndBudget prep.1.normalization.classes n (0) G ep Wc ec := by
    dsimp only [runPreparedWeighted,compressedEndBudget]
    exact Nat.add_le_add_right (Nat.add_le_add hprep hcc) 1
  have hh := hsum.trans (henv prep.1.normalization.classes n (0))
  have hq := compressedPrepared_parameter hn prep.1
  have ht := Nat.mul_le_mul_right ((n+2)^e)
    (sharp_parameter_transport _ _ W hq)
  exact ⟨hcorrect,hh.trans ht⟩

end MOR34
