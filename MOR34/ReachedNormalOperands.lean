import MOR34.StandardFactorInstantiation

namespace MOR34
variable {q : ℕ}

/-- The operand invariant for the exact matrix emitted at a normal-generation
call, including rejected candidates and all determinant partial sums. -/
def PreparedNormalOperands (prep : CountMatrixPreparation q) (B : Finset (Counts q)) (n : ℕ) : Prop :=
  (∀ i j, |(prep.emit B).1 i j| ≤ ((n+1 : ℕ) : ℤ)) ∧
  (∀ {r : ℕ} (a : Fin r → Fin (orderedCounts B).length) (c : Fin r ↪ Fin (q+1))
      (i : Fin (orderedCounts B).length) (j : Fin (q+1)) (S : Finset (Fin (q+1))),
    signedIntegerBits (∑ l ∈ S, (prep.emit B).1 i l *
      concreteColumnNormal ((prep.emit B).1.submatrix a id) c j l) ≤ normalWorkBits q n) ∧
  (∀ {r : ℕ}, r+1 ≤ q+1 →
    ∀ (a : Fin (r+1) → Fin (orderedCounts B).length) (c : Fin (r+1) → Fin (q+1))
      (S : Finset (Fin (r+1))),
    signedIntegerBits (∑ j ∈ S, laplaceTerm ((prep.emit B).1.submatrix a c) j) ≤ normalWorkBits q n)

theorem preparedNormalOperands_of_bounded (prep : CountMatrixPreparation q)
    (B : Finset (Counts q)) (n : ℕ) (hB : ∀ z ∈ B, ∀ j, z j ≤ n+1) :
    PreparedNormalOperands prep B n := by
  refine ⟨?_,?_,?_⟩
  · rw [prep.value]
    exact orderedCountMatrix_bound B n hB
  · intro r a c i j S
    exact preparedNormalCheck_bits prep B n hB a c i j S
  · intro r hr a c S
    exact preparedNormalMinor_bits prep B n hB hr a c S

/-- Propagate the operand invariant through every actually reached basis state
of the same query callback used by the weighted cell execution. -/
theorem preparedNormalOperands_on_states (prep : CountMatrixPreparation q)
    (C : Set (Counts q)) (n : ℕ) (hC : ∀ z ∈ C, ∀ j, z j ≤ n+1)
    (solve : IntegerQuery q → Option (Counts q) × ℕ)
    (hor : LinearOracleSpec C (fun t => (solve t).1)) :
    SearchStates (linearSpanOracle (fun t => (solve t).1) computedCountForms)
      (fun B => PreparedNormalOperands prep B n) (q+1) ∅ := by
  have hf := linearSpanOracle_spec C (fun t => (solve t).1) hor computedCountForms computedCountForms_spec
  apply searchStates_of_containment C _ (fun B z hz => (hf.found B z hz).1)
  · intro B hB
    exact preparedNormalOperands_of_bounded prep B n (fun z hz => hC z (hB hz))
  · simp

variable {m : Fin q → ℕ}

theorem preparedWeightedCell_normal_states (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) :
    SearchStates (linearSpanOracle
      (fun t => (weightedDenseCellQuery A.arith P A.base.R A.base.D solve ε e mode t).1)
      computedCountForms)
      (fun B => PreparedNormalOperands A.prep B (Fintype.card (Item m))) (q+1) ∅ := by
  apply preparedNormalOperands_on_states A.prep (parityCellSet P ε e mode) (Fintype.card (Item m))
  · intro z hz j
    exact (hz.1.1 j).trans ((class_size_le_items j).trans (by omega))
  · simp only [weightedDenseCellQuery_value]
    exact rowCellOracle_spec P hWF _ (denseCountOracle_spec P A.base.R solve hs) ε e mode

end MOR34
