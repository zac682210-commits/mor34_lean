import MOR34.ChargedRankBasis

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Established dense-matrix emission and exact-rank primitives. Their costs
are local functions of this concrete matrix, not of the MOR34 execution. -/
structure BinaryRankOperations (ranker : ExactIntegerRank m) where
  emit : (B : Finset (Finset (Item m))) → Matrix B (Option (Item m)) ℤ × ℕ
  emit_value : ∀ B, (emit B).1 = binaryPointMatrix B
  rank : (B : Finset (Finset (Item m))) → Matrix B (Option (Item m)) ℤ → ℕ × ℕ
  rank_value : ∀ B M, (rank B M).1 = ranker.evaluate M

def chargedBinaryRank (ranker : ExactIntegerRank m) (ops : BinaryRankOperations ranker)
    (B : Finset (Finset (Item m))) : ℕ × ℕ :=
  let matrix := ops.emit B
  let out := ops.rank B matrix.1
  (out.1,matrix.2+out.2+1)

theorem chargedBinaryRank_value (ranker : ExactIntegerRank m) (ops : BinaryRankOperations ranker)
    (B : Finset (Finset (Item m))) :
    (chargedBinaryRank ranker ops B).1 = ranker.evaluate (binaryPointMatrix B) := by
  simp only [chargedBinaryRank,ops.rank_value,ops.emit_value]

structure BinaryRankBounds (ranker : ExactIntegerRank m) (ops : BinaryRankOperations ranker)
    (E I c : ℕ) : Prop where
  emit : ∀ B, (ops.emit B).2 ≤ E*(B.card+1)*(Fintype.card (Item m)+1)^2
  rank : ∀ B, (ops.rank B (binaryPointMatrix B)).2 ≤
    I*(binaryMatrixPayload B+B.card+Fintype.card (Item m)+1)^c

def binaryRankBudget (n E I c : ℕ) : ℕ := E*(n+3)*(n+1)^2+I*(4*(n+3)^2)^c+1

theorem chargedBinaryRank_cost (ranker : ExactIntegerRank m) (ops : BinaryRankOperations ranker)
    (E I c : ℕ) (hops : BinaryRankBounds ranker ops E I c)
    (B : Finset (Finset (Item m))) (hB : B.card ≤ Fintype.card (Item m)+2) :
    (chargedBinaryRank ranker ops B).2 ≤ binaryRankBudget (Fintype.card (Item m)) E I c := by
  let n := Fintype.card (Item m)
  have hp := binaryMatrixPayload_bound B
  have hsize : binaryMatrixPayload B+B.card+n+1 ≤ 4*(n+3)^2 := by
    have hh := Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_left 2 hB)
    nlinarith
  have hm := (hops.emit B).trans
    (Nat.mul_le_mul_right ((n+1)^2) (Nat.mul_le_mul_left E (Nat.add_le_add_right hB 1)))
  have hr := (hops.rank B).trans (Nat.mul_le_mul_left I (pow_le_pow_left' hsize c))
  simp only [chargedBinaryRank,ops.emit_value,binaryRankBudget]
  change _ ≤ E*(n+3)*(n+1)^2+I*(4*(n+3)^2)^c+1
  dsimp only [n] at *
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

/-- Standard ordering/deduplication and insertion on finite binary point sets.
No correctness or runtime of the basis search is assumed here. -/
structure BinaryCollectionOperations (m : Fin q → ℕ) where
  order : List (Finset (Item m)) → List (Finset (Item m)) × ℕ
  order_value : ∀ L, (order L).1 = orderedBinarySets L.toFinset
  put : Finset (Item m) → Finset (Finset (Item m)) → Finset (Finset (Item m)) × ℕ
  put_value : ∀ S B, (put S B).1 = insert S B

structure BinaryCollectionBounds (ops : BinaryCollectionOperations m) (O J : ℕ) : Prop where
  order : ∀ L, (ops.order L).2 ≤ O*(L.length+1)^2
  put : ∀ S B, B.card ≤ Fintype.card (Item m)+1 → (ops.put S B).2 ≤ J

def chargedFinalBasis (ranker : ExactIntegerRank m) (rankOps : BinaryRankOperations ranker)
    (setOps : BinaryCollectionOperations m) (L : List (Finset (Item m))) :
    Finset (Finset (Item m)) × ℕ :=
  let ordered := setOps.order L
  let out := chargedRankBasis ordered.1 (chargedBinaryRank ranker rankOps) setOps.put
    (Fintype.card (Item m)+1)
  (out.1,ordered.2+out.2+1)

theorem chargedFinalBasis_value (ranker : ExactIntegerRank m) (rankOps : BinaryRankOperations ranker)
    (setOps : BinaryCollectionOperations m) (L : List (Finset (Item m))) :
    (chargedFinalBasis ranker rankOps setOps L).1 =
      binaryBasisSearch (orderedBinarySets L.toFinset) (fun B => ranker.evaluate (binaryPointMatrix B)) := by
  rw [chargedFinalBasis,chargedRankBasis_value _ _ _ setOps.put_value]
  simp only [setOps.order_value,chargedBinaryRank_value,binaryBasisSearch]

def finalBasisBudget (n M O J E I c : ℕ) : ℕ :=
  O*(M+1)^2+(n+1)*(M*(2*binaryRankBudget n E I c+J+2)+J+2)+2

theorem chargedFinalBasis_cost (ranker : ExactIntegerRank m) (rankOps : BinaryRankOperations ranker)
    (setOps : BinaryCollectionOperations m) (M O J E I c : ℕ)
    (hr : BinaryRankBounds ranker rankOps E I c) (hc : BinaryCollectionBounds setOps O J)
    (L : List (Finset (Item m))) (hL : L.length ≤ M) :
    (chargedFinalBasis ranker rankOps setOps L).2 ≤
      finalBasisBudget (Fintype.card (Item m)) M O J E I c := by
  let n := Fintype.card (Item m)
  have hl : (setOps.order L).1.length ≤ M := by
    rw [setOps.order_value,orderedBinarySets_length]
    exact (List.toFinset_card_le L).trans hL
  have ho := (hc.order L).trans (Nat.mul_le_mul_left O (pow_le_pow_left' (Nat.add_le_add_right hL 1) 2))
  have hb := chargedRankBasis_cost (setOps.order L).1 (chargedBinaryRank ranker rankOps)
    setOps.put setOps.put_value (n+1) (binaryRankBudget n E I c) J
    (fun B hB => chargedBinaryRank_cost ranker rankOps E I c hr B hB) hc.put
  have hm := Nat.mul_le_mul_right (2*binaryRankBudget n E I c+J+2) hl
  have hm' := Nat.mul_le_mul_left (n+1) (Nat.add_le_add_right hm (J+2))
  dsimp only [chargedFinalBasis,finalBasisBudget]
  change _ ≤ O*(M+1)^2+(n+1)*(M*(2*binaryRankBudget n E I c+J+2)+J+2)+2
  dsimp only [n] at *
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

end MOR34
