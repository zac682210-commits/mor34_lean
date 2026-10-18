import MOR34.DensePayloadTransfer

namespace MOR34

/-- A dense arithmetic input-size measure with explicit row/dimension headers.
It deliberately dominates a compact encoding; it is not a wire-format verifier. -/
def denseProblemSize {q : ℕ} (rows : List (DenseIntegerRow q)) : ℕ :=
  (rows.map DenseIntegerRow.payload).sum+rows.length+2*q+1

/-- The supplied established solver has a bound for each concrete input. It
assumes no correctness, phase count, or bound for the MOR34 algorithm. -/
def DenseSolverCostBound {q : ℕ}
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) (I c : ℕ) : Prop :=
  ∀ rows, (∀ row ∈ rows, row.WellSized) → (solve rows).2 ≤ I*(denseProblemSize rows)^c

theorem denseProblemSize_polynomial {q : ℕ} (rows : List (DenseIntegerRow q)) (n L : ℕ)
    (hq : q ≤ n) (hr : rows.length ≤ 6*(n+L+2))
    (hp : (rows.map DenseIntegerRow.payload).sum ≤ 168*(n+L+2)^4) :
    denseProblemSize rows ≤ 180*(n+L+2)^4 := by
  have ht : n+L+2 ≤ (n+L+2)^4 := le_self_pow₀ (by omega) (by decide)
  unfold denseProblemSize
  omega

variable {q : ℕ} {m : Fin q → ℕ}

theorem compiledForcedRequest_length (P : Model m) (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    (compiledForcedRequest P j u v R).1.length =
      Fintype.card (Item m)+2*q+(pairAllowed u v).card+6 := by
  simp only [compiledForcedRequest,retainedForcedSystem,chargedMap_value,List.length_map,
    forcedRowIndexList_length]

theorem compiledCountRequest_length (P : Model m) (ε : Parity q) (Q : List (IntegerQuery q)) (R : ℕ) :
    (compiledCountRequest P ε Q R).1.length = Fintype.card (Item m)+2*q+Q.length+3 := by
  simp only [compiledCountRequest,chargedMap_value,List.length_map,countRowIndexList_length]

theorem compiledViolationRequest_length (P : Model m) (R : ℕ) :
    (compiledViolationRequest P R).1.length = Fintype.card (Item m)+2*q+2 := by
  simp only [compiledViolationRequest,chargedMap_value,List.length_map,violationRowIndexList_length]

theorem actualForcedSolver_cost (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (j : Fin q) (u v : Fin (m j)) (R I c : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) :
    (solve (compiledForcedRequest P j u v R).1).2 ≤
      I*(180*(Fintype.card (Item m)+L+2)^4)^c := by
  have hq := coefficient_classes_le_items P hWF
  have hpair : (pairAllowed u v).card ≤ Fintype.card (Item m) :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans
      (class_size_le_items j)
  have hsize := denseProblemSize_polynomial (compiledForcedRequest P j u v R).1
    (Fintype.card (Item m)) L hq
    (by rw [compiledForcedRequest_length]; omega)
    (compiledForcedRequest_payload_polynomial P hWF M L hM hML hw hc hb hd j u v R)
  exact (hcost _ (compiledForcedRequest_sized P j u v R)).trans
    (Nat.mul_le_mul_left I (pow_le_pow_left' hsize c))

theorem actualViolationSolver_cost (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) (R I c : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) :
    (solve (compiledViolationRequest P R).1).2 ≤ I*(180*(Fintype.card (Item m)+L+2)^4)^c := by
  have hq := coefficient_classes_le_items P hWF
  have hsize := denseProblemSize_polynomial (compiledViolationRequest P R).1
    (Fintype.card (Item m)) L hq (by rw [compiledViolationRequest_length]; omega)
    (compiledViolationRequest_payload_polynomial P hWF M L hM hML hw hc hb hd R)
  exact (hcost _ (compiledViolationRequest_sized P R)).trans
    (Nat.mul_le_mul_left I (pow_le_pow_left' hsize c))

/-- The old actual-state payload invariant is transported to the integer array
used at the corresponding call, and then into the external solver's local cost. -/
theorem actualCellSolver_cost (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (e : ParityExtrema P ε) (mode : CellMode q) (L : ℕ) (B : Finset (Counts q))
    (hp : PolynomialCellSearchPayload P ε e mode L B)
    (t : IntegerQuery q) (ht : t ∈ outsideQueries (computedCountForms B)) (R I c : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) :
    (solve (compiledCountRequest P ε (t::cellQueries e.low e.high mode) R).1).2 ≤
      I*(180*(Fintype.card (Item m)+L+2)^4)^c := by
  obtain ⟨a,b,d,he,hbits⟩ := hp t ht
  have harr : (((compiledCountRequest P ε (t::cellQueries e.low e.high mode) R).1).map
      DenseIntegerRow.payload).sum ≤ 168*(Fintype.card (Item m)+L+2)^4 := by
    rw [compiledCountRequest_payload P ε _ R a b d he]
    exact hbits
  have hq := coefficient_classes_le_items P hWF
  have hsize := denseProblemSize_polynomial
    (compiledCountRequest P ε (t::cellQueries e.low e.high mode) R).1
    (Fintype.card (Item m)) L hq
    (by rw [compiledCountRequest_length,List.length_cons,cellQueries_length]; omega) harr
  exact (hcost _ (compiledCountRequest_sized P ε _ R)).trans
    (Nat.mul_le_mul_left I (pow_le_pow_left' hsize c))

end MOR34
