import MOR34.WeightedRunInterface
import MOR34.CompressionApplication

namespace MOR34
variable {n : ℕ}

/-- The established compression algorithm is used on one augmented vector at
a time. Its sign, size and time conclusions are separate local contracts. -/
structure CompressionPrimitive (n : ℕ) where
  run : (Option (Fin n) → ℤ) → (Option (Fin n) → ℤ) × ℕ
  signs : ∀ w, PreservesSmallSigns (n+1) w (run w).1
  magnitude : ∀ w i, ((run w).1 i).natAbs ≤ compressionRadius n

/-- Standard coefficient grouping and sorting. The output is the specific
normalization already proved correct, with a local preparation cost. -/
structure NormalizationPrimitive (n : ℕ) where
  run : (hn : 0 < n) → (a v : Fin n → ℤ) → (b rhs : ℤ) →
    (ha : ∀ i, 0 < a i) → (hb : 0 < b) → (hab : ∀ i, a i ≤ b) →
    (hc : ∀ i, 0 ≤ v i) → RawNormalization a v b rhs × ℕ
  value : ∀ hn a v b rhs ha hb hab hc,
    (run hn a v b rhs ha hb hab hc).1 = normalizeRawExecutable hn a v b rhs ha hb hab hc

structure CompressedPreparedInput (a v : Fin n → ℤ) (b rhs : ℤ) where
  weights : Fin n → ℤ
  coefficients : Fin n → ℤ
  capacity : ℤ
  level : ℤ
  relation : RawCompression a v weights coefficients b rhs capacity level
  normalization : RawNormalization weights coefficients capacity level
  weights_bound : ∀ i, (augmentedWeights weights capacity i).natAbs ≤ compressionRadius n
  coefficients_bound : ∀ i, (augmentedWeights coefficients level i).natAbs ≤ compressionRadius n

def chargedCompressionPreparation (hn : 0 < n) (a v : Fin n → ℤ) (b rhs : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ v i)
    (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n) :
    CompressedPreparedInput a v b rhs × ℕ := by
  let wa := ft.run (augmentedWeights a b)
  let wc := ft.run (augmentedWeights v rhs)
  let a' := fun i => wa.1 (some i)
  let c' := fun i => wc.1 (some i)
  let b' := wa.1 none
  let d' := wc.1 none
  have hea : augmentedWeights a' b' = wa.1 := by funext i; cases i <;> rfl
  have hec : augmentedWeights c' d' = wc.1 := by funext i; cases i <;> rfl
  have hrel : RawCompression a v a' c' b rhs b' d' := by
    constructor
    · rw [hea]; exact ft.signs _
    · rw [hec]; exact ft.signs _
  have hh := compression_hypotheses hn hrel ha hb hab hc
  let N := normalize.run hn a' c' b' d' hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  exact (⟨a',c',b',d',hrel,N.1,
    fun i => by rw [hea]; exact ft.magnitude _ i,
    fun i => by rw [hec]; exact ft.magnitude _ i⟩,wa.2+wc.2+N.2+2*n+4)

theorem compressedPrepared_size {a v : Fin n → ℤ} {b rhs : ℤ}
    (p : CompressedPreparedInput a v b rhs) :
    rawIntegerPayload p.weights p.coefficients p.capacity p.level ≤ 18*(n+1)^4 :=
  compressed_payload_bound _ _ _ _ p.weights_bound p.coefficients_bound

theorem compressedPrepared_parameter {a v : Fin n → ℤ} {b rhs : ℤ}
    (hn : 0 < n) (p : CompressedPreparedInput a v b rhs) :
    p.normalization.classes ≤ ((Finset.univ.image v).filter (fun z => 0 < z)).card+1 := by
  rw [compression_positive_parameter hn p.relation]
  exact rawNormalization_parameter p.normalization

/-- A suitable common magnitude and polynomial exponent are proved for the
actual grouped compressed model; they are not postulated for its rows. -/
theorem compressedPrepared_magnitudes {a v : Fin n → ℤ} {b rhs : ℤ}
    (p : CompressedPreparedInput a v b rhs) :
    (∀ i, |p.normalization.model.weight i| ≤ (compressionRadius n : ℤ)) ∧
    (∀ j, |p.normalization.model.coefficient j| ≤ (compressionRadius n : ℤ)) ∧
    |p.normalization.model.capacity| ≤ (compressionRadius n : ℤ) ∧
    |p.normalization.model.rhs| ≤ (compressionRadius n : ℤ) := by
  have absBound (z : ℤ) (h : z.natAbs ≤ compressionRadius n) : |z| ≤ (compressionRadius n : ℤ) := by
    simpa only [Int.natCast_natAbs] using (show (z.natAbs : ℤ) ≤ (compressionRadius n : ℤ) by exact_mod_cast h)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [p.normalization.weight_eq]
    exact absBound _ (p.weights_bound (some (p.normalization.itemEquiv i)))
  · intro j
    let i : Item p.normalization.sizes := ⟨j,⟨0,p.normalization.wellFormed.2.1 j⟩⟩
    rw [p.normalization.coefficient_eq i]
    exact absBound _ (p.coefficients_bound (some (p.normalization.itemEquiv i)))
  · rw [p.normalization.capacity_eq]
    exact absBound _ (p.weights_bound none)
  · rw [p.normalization.rhs_eq]
    exact absBound _ (p.coefficients_bound none)

/-- Only the two compression calls and one normalization call are assumed to
satisfy standard polynomial bounds. Their composition below is proved. -/
structure PreparationLocalBounds (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n)
    (G e : ℕ) : Prop where
  compress : ∀ w, (ft.run w).2 ≤ G*(n+(∑ i, signedIntegerBits (w i))+2)^e
  normalize : ∀ hn a v b rhs ha hb hab hc,
    (normalize.run hn a v b rhs ha hb hab hc).2 ≤ G*(n+rawIntegerPayload a v b rhs+2)^e

def preparationBudget (n L G e : ℕ) : ℕ :=
  2*G*(n+L+2)^e+G*(n+18*(n+1)^4+2)^e+2*n+4

theorem chargedCompressionPreparation_cost (hn : 0 < n) (a v : Fin n → ℤ) (b rhs : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ v i)
    (ft : CompressionPrimitive n) (normalize : NormalizationPrimitive n) (G e : ℕ)
    (h : PreparationLocalBounds ft normalize G e) :
    (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).2 ≤
      preparationBudget n (rawIntegerPayload a v b rhs) G e := by
  have hleft : (∑ i, signedIntegerBits (augmentedWeights a b i)) ≤ rawIntegerPayload a v b rhs := by
    unfold rawIntegerPayload; omega
  have hright : (∑ i, signedIntegerBits (augmentedWeights v rhs i)) ≤ rawIntegerPayload a v b rhs := by
    unfold rawIntegerPayload; omega
  have h₁ := (h.compress (augmentedWeights a b)).trans (Nat.mul_le_mul_left G
    (pow_le_pow_left' (Nat.add_le_add_right (Nat.add_le_add_left hleft n) 2) e))
  have h₂ := (h.compress (augmentedWeights v rhs)).trans (Nat.mul_le_mul_left G
    (pow_le_pow_left' (Nat.add_le_add_right (Nat.add_le_add_left hright n) 2) e))
  let p := (chargedCompressionPreparation hn a v b rhs ha hb hab hc ft normalize).1
  have hp := compressedPrepared_size p
  have hcond := compression_hypotheses hn p.relation ha hb hab hc
  have h₃ := h.normalize hn p.weights p.coefficients p.capacity p.level
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
  have h₄ := h₃.trans (Nat.mul_le_mul_left G
    (pow_le_pow_left' (Nat.add_le_add_right (Nat.add_le_add_left hp n) 2) e))
  dsimp only [p,chargedCompressionPreparation] at h₄ ⊢
  unfold preparationBudget
  omega

end MOR34
