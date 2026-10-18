import MOR34.ChargedRawExecution

namespace MOR34

/-- A finite prefix majorant transports a normalized parameter bound without
assuming that the dimension factor supplied by an external algorithm is monotone. -/
def parameterMajorant (F : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range (k+2), F j

theorem parameterMajorant_le (F : ℕ → ℕ) (q k : ℕ) (h : q ≤ k+1) :
    F q ≤ parameterMajorant F k := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (F j)) (Finset.mem_range.mpr (by omega))

def rawReferenceBudget (q n L N D I c J E C O BJ BE BI bc RC RE RJ : ℕ) : ℕ :=
  normalizedExecutionBudget q n L N D I c J E C O BJ BE BI bc+
    RC+RE+(n+1)*(RC+1)+RJ+3

theorem rawReferenceBudget_uniform (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    UniformPolynomial (fun q n L =>
      rawReferenceBudget q n L (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)) := by
  unfold rawReferenceBudget
  apply uniformPolynomial_add
  · apply uniformPolynomial_add
    · apply uniformPolynomial_add
      · apply uniformPolynomial_add
        · apply uniformPolynomial_add
          · exact normalizedExecutionBudget_uniform I BI K c bc d
          · uniform_polynomial
        · uniform_polynomial
      · uniform_polynomial
    · uniform_polynomial
  · uniform_polynomial

/-- This theorem includes restoration of the original point labels. It is
still a reference-operation result; integer bit pricing is a separate obligation. -/
theorem original_reference_application (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ, ∀ {n : ℕ} {a v : Fin n → ℤ} {b rhs : ℤ}
      (N : RawNormalization a v b rhs) (R : ℕ)
      (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
      (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives N.model solve),
      R ≤ n+1 → A.I = I N.classes → A.c = c →
    ∀ (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
      (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
      (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n)
      (C O BJ BE RC RE RJ : ℕ),
      PointOperationBounds ops C → BinaryRankBounds ranker rankOps BE (BI N.classes) bc →
      BinaryCollectionBounds setOps O BJ → RelabelLocalBounds N.itemEquiv point basis RC RE RJ →
      ExecutionLocalBounds N.model solve A C O BJ BE (K N.classes*(n+A.L+2)^d) →
      RC ≤ K N.classes*(n+A.L+2)^d → RE ≤ K N.classes*(n+A.L+2)^d →
      RJ ≤ K N.classes*(n+A.L+2)^d →
      (N.runCharged R solve hs A ops ranker rankOps setOps point basis).1.Correct a v b rhs ∧
      (N.runCharged R solve hs A ops ranker rankOps setOps point basis).2 ≤
        F (((Finset.univ.image v).filter (fun z => 0 < z)).card)*(n+A.L+2)^e := by
  obtain ⟨e,F,hF⟩ := rawReferenceBudget_uniform I BI K c bc d
  refine ⟨e,parameterMajorant F,?_⟩
  intro n a v b rhs N R solve hs A hR hI hc ops ranker rankOps setOps point basis
    C O BJ BE RC RE RJ ho hr hb hl hlocal hRC hRE hRJ
  refine ⟨chargedRawExecution_correct N R solve hs A ops ranker rankOps setOps point basis,?_⟩
  have hx := chargedRawExecution_cost N R solve hs A hR ops ranker rankOps setOps point basis
    C O BJ BE (BI N.classes) bc RC RE RJ ho hr hb hl
  rw [hI,hc] at hx
  have hn := normalizedExecutionBudget_mono N.classes n A.L A.N A.D (I N.classes) c
    A.J A.E C O BJ BE (BI N.classes) bc (K N.classes*(n+A.L+2)^d)
    hlocal.normalRead hlocal.decode hlocal.insertCount hlocal.emitCount
    hlocal.point hlocal.order hlocal.insertBinary hlocal.emitBinary
  have hm := Nat.mul_le_mul_left (n+1) (Nat.add_le_add_right hRC 1)
  have hraw := hF N.classes n A.L
  dsimp only [rawReferenceBudget] at hraw
  have hbound := parameterMajorant_le F N.classes
    (((Finset.univ.image v).filter (fun z => 0 < z)).card) (rawNormalization_parameter N)
  have hlast := Nat.mul_le_mul_right ((n+A.L+2)^e) hbound
  omega

/-- Two external compression calls and ordinary grouping/sorting preprocessing
are local phases outside the already bounded retained core. This lemma merely
combines those phase costs; it does not supply the core bound as an assumption
for the applications above. -/
theorem prepend_standard_preprocessing (cost prep F S e H d : ℕ)
    (hS : 1 ≤ S) (hcore : cost ≤ F*S^e) (hprep : prep ≤ H*S^d) :
    prep+cost+1 ≤ (H+F+1)*S^(d+e) := by
  have hp := hprep.trans (Nat.mul_le_mul_left H (pow_le_pow_right' hS (by omega : d ≤ d+e)))
  have hc := hcore.trans (Nat.mul_le_mul_left F (pow_le_pow_right' hS (by omega : e ≤ d+e)))
  have hone := Nat.one_le_pow (d+e) S hS
  nlinarith

end MOR34
