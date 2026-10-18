import MOR34.ExecutableNormalizedPipeline
import MOR34.BasisRankCalls
import MOR34.PolynomialPayload
import MOR34.NormalSearchCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

set_option maxHeartbeats 1000000 in
theorem computedReturnedBasis_rank_calls (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) (ranker : ExactIntegerRank m) :
    finiteBasisRankCalls (orderedBinarySets (computedReturnedSets P hWF solve hs edgeSolve he))
      (fun B => ranker.evaluate (binaryPointMatrix B)) (Fintype.card (Item m)+1) ∅ ≤
      2*(Fintype.card (Item m)+1)*((q+1)*6^q+2*Fintype.card (Item m)) := by
  have hlen : (orderedBinarySets (computedReturnedSets P hWF solve hs edgeSolve he)).length ≤
      (q+1)*6^q+2*Fintype.card (Item m) := by
    rw [orderedBinarySets_length, computedReturnedSets_eq]
    exact returnedSets_card P hWF (computedCellSelection P hWF solve hs) edgeSolve he
      (computedCellSelection_small P hWF solve hs)
  exact (finiteBasisRankCalls_le
    (orderedBinarySets (computedReturnedSets P hWF solve hs edgeSolve he))
    (fun B => ranker.evaluate (binaryPointMatrix B)) (Fintype.card (Item m)+1) ∅).trans
      (Nat.mul_le_mul_left _ hlen)

theorem binaryPointMatrix_entry_bits (B : Finset (Finset (Item m)))
    (t : B) (i : Option (Item m)) : signedIntegerBits (binaryPointMatrix B t i) ≤ 2 := by
  have hb : (binaryPointMatrix B t i).natAbs ≤ 2^0 := by
    cases i with
    | none => norm_num [binaryPointMatrix]
    | some j => simp only [binaryPointMatrix, indicator]; split_ifs <;> norm_num
  have hh := magnitudeBits_le_of_power_bound (binaryPointMatrix B t i) 0 hb
  unfold signedIntegerBits
  omega

def binaryMatrixPayload (B : Finset (Finset (Item m))) : ℕ :=
  ∑ t : B, ∑ i : Option (Item m), signedIntegerBits (binaryPointMatrix B t i)

theorem binaryMatrixPayload_bound (B : Finset (Finset (Item m))) :
    binaryMatrixPayload B ≤ 2*B.card*(Fintype.card (Item m)+1) := by
  calc
    _ ≤ ∑ _t : B, ∑ _i : Option (Item m), 2 :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun i _ => binaryPointMatrix_entry_bits B t i))
    _ = _ := by simp; ring

/-- Both rank inputs in every actual outside test have quadratic binary payload.
The statement covers even candidates that are rejected. -/
theorem binaryBasisSearch_rank_payload_states (L : List (Finset (Item m)))
    (rankEval : Finset (Finset (Item m)) → ℕ) :
    SearchStates (finiteSpanOracle L (rankOutside rankEval))
      (fun B => binaryMatrixPayload B ≤ 2*(Fintype.card (Item m)+2)^2 ∧
        ∀ t : Finset (Item m), binaryMatrixPayload (insert t B) ≤ 2*(Fintype.card (Item m)+2)^2)
      (Fintype.card (Item m)+1) ∅ := by
  apply searchStates_mono _ (fun B => B.card ≤ Fintype.card (Item m)+1) _ ?_ _ _
    (searchStates_card _ _ _ _ (by simp))
  intro B hB
  constructor
  · have hh := (binaryMatrixPayload_bound B).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hB))
    nlinarith
  · intro t
    have hi := Finset.card_insert_le t B
    have hb : (insert t B).card ≤ Fintype.card (Item m)+2 := by omega
    have hh := (binaryMatrixPayload_bound (insert t B)).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hb))
    nlinarith

end MOR34
