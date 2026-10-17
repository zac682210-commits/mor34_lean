import MOR34.BinaryPointBasis

namespace MOR34
section RankCalls
variable {α : Type*} [DecidableEq α]

/-- Two rank evaluations per candidate outside test, counted without caching. -/
def finiteBasisRankCalls (L : List α) (rankEval : Finset α → ℕ) : ℕ → Finset α → ℕ
  | 0, _ => 0
  | n + 1, B =>
    2 * firstWitnessCalls (fun a => if rankOutside rankEval B a then some a else none) L +
      match finiteSpanOracle L (rankOutside rankEval) B with
      | none => 0
      | some a => finiteBasisRankCalls L rankEval n (insert a B)

theorem finiteBasisRankCalls_le (L : List α) (rankEval : Finset α → ℕ) (n : ℕ) (B : Finset α) :
    finiteBasisRankCalls L rankEval n B ≤ 2 * n * L.length := by
  induction n generalizing B with
  | zero => simp [finiteBasisRankCalls]
  | succ n ih =>
    have hc := firstWitness_calls_le
      (fun a => if rankOutside rankEval B a then some a else none) L
    cases he : finiteSpanOracle L (rankOutside rankEval) B with
    | none => simp only [finiteBasisRankCalls, he]; nlinarith
    | some a =>
      simp only [finiteBasisRankCalls, he]
      have hh := ih (insert a B)
      nlinarith
end RankCalls

variable {q : ℕ} {m : Fin q → ℕ}

/-- The extraction phase has polynomially many exact rank calls in the returned family size. -/
theorem returned_basis_rank_calls (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve)
    (hsmall : ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1)
    (rankEval : Finset (Finset (Item m)) → ℕ) :
    finiteBasisRankCalls (returnedSets P hWF S solve hs).toList rankEval
      (Fintype.card (Item m) + 1) ∅ ≤
      2 * (Fintype.card (Item m) + 1) * ((q + 1) * 6 ^ q + 2 * Fintype.card (Item m)) := by
  have hh := finiteBasisRankCalls_le (returnedSets P hWF S solve hs).toList rankEval
    (Fintype.card (Item m) + 1) ∅
  rw [Finset.length_toList] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (returnedSets_card P hWF S solve hs hsmall))
end MOR34
