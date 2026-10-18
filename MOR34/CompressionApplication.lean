import MOR34.CompressionSize

namespace MOR34

/-- The application accepts the sign and size conclusions of Frank--Tardos as
external hypotheses. Everything specific to the knapsack instance is proved here. -/
theorem external_compression_application {n : ℕ} (hn : 0 < n)
    (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (compress : (Option (Fin n) → ℤ) → (Option (Fin n) → ℤ))
    (hsign : ∀ w, PreservesSmallSigns (n+1) w (compress w))
    (hbound : ∀ w i, (compress w i).natAbs ≤ compressionRadius n) :
    ∃ (a' c' : Fin n → ℤ) (b' d' : ℤ),
      RawCompression a c a' c' b d b' d' ∧
      rawIntegerPayload a' c' b' d' ≤ 18*(n+1)^4 ∧
      ((Finset.univ.image c).filter (fun v => 0 < v)).card =
        ((Finset.univ.image c').filter (fun v => 0 < v)).card ∧
      (∀ out : RawOutput n, out.Correct a c b d ↔ out.Correct a' c' b' d') ∧
      ∃ N : RawNormalization a' c' b' d',
        N.classes ≤ ((Finset.univ.image c).filter (fun v => 0 < v)).card+1 ∧
        ∀ s : RowPrimitives N.model, (N.runExecutable s).Correct a c b d := by
  let wa := compress (augmentedWeights a b)
  let wc := compress (augmentedWeights c d)
  let a' := fun i => wa (some i)
  let c' := fun i => wc (some i)
  let b' := wa none
  let d' := wc none
  have hea : augmentedWeights a' b' = wa := by funext i; cases i <;> rfl
  have hec : augmentedWeights c' d' = wc := by funext i; cases i <;> rfl
  have hh : RawCompression a c a' c' b d b' d' := by
    constructor
    · rw [hea]; exact hsign _
    · rw [hec]; exact hsign _
  refine ⟨a',c',b',d',hh,?_,compression_positive_parameter hn hh,
    compression_output hh,compressed_original_output_contract hn hh ha hb hab hc⟩
  apply compressed_payload_bound
  · intro i; rw [hea]; exact hbound _ i
  · intro i; rw [hec]; exact hbound _ i

end MOR34
