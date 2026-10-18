import MOR34.RowLiteralBounds
import MOR34.ViolationConstructionCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem forcedSlopeConstruction_literals (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (M : ℕ) (hM : 1 ≤ M) (hm : m j ≤ M)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) :
    (forcedSlopeConstruction P j u v a).LiteralsBounded M := by
  have hr : ∀ i, (forcedResidualWeights P j u v i).natAbs ≤ M := fun i => hw _
  have hcard : (pairAllowed u v).card ≤ m j := by simpa using Finset.card_le_univ (pairAllowed u v)
  refine ⟨fun k => integerPick_magnitude j k _ M (hr a),
    fun k => integerPick_magnitude j k (-1) M (by simpa using hM),?_⟩
  change (((((a.val : ℤ).natAbs ≤ M) ∧ (1 : ℤ).natAbs ≤ M) ∧
    (forcedResidualWeights P j u v a).natAbs ≤ M) ∧
    (prefixConstruction (forcedResidualWeights P j u v) a.val).LiteralsBounded M) ∧
      (P.weight ⟨j,v⟩).natAbs ≤ M
  exact ⟨⟨⟨⟨by simp; omega,by simpa using hM⟩,hr a⟩,
    prefixConstruction_literals _ _ M hr⟩,hw _⟩

theorem forcedEmptyConstruction_literals (P : Model m) (j : Fin q) (u v : Fin (m j))
    (M : ℕ) (hM : 1 ≤ M) (hw : ∀ i, (P.weight i).natAbs ≤ M) :
    (forcedEmptyConstruction P j u v).LiteralsBounded M := by
  unfold forcedEmptyConstruction
  split_ifs
  · exact ⟨fun _ => Nat.zero_le _,
      fun k => integerPick_magnitude j k (-1) M (by simpa using hM),hw _⟩
  · exact atomicIntegerRow_literals _ _ _ M (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (Nat.zero_le _)

theorem forcedRowConstruction_literals (P : Model m) (j : Fin q) (u v : Fin (m j))
    (M : ℕ) (hM : 1 ≤ M) (hm : ∀ k, m k ≤ M)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (ha : ∀ k, (P.coefficient k).natAbs ≤ M)
    (hb : P.rhs.natAbs ≤ M) (hc : P.capacity.natAbs ≤ M)
    (k : ForcedRow m j u v) : (forcedRowConstruction P j u v k).LiteralsBounded M := by
  have hz : ∀ k : Fin q, ((0 : Fin q → ℤ) k).natAbs ≤ M := fun _ => Nat.zero_le _
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  · exact atomicIntegerRow_literals _ _ _ M
      (fun i => integerPick_magnitude k i (-1) M (by simpa using hM)) hz (Nat.zero_le _)
  · exact atomicIntegerRow_literals _ _ _ M
      (fun i => integerPick_magnitude k i 1 M (by simpa using hM)) hz (by simpa using hm k)
  · simp only [forcedRowConstruction]
    split_ifs
    · exact atomicIntegerRow_literals _ _ _ M ha hz hb
    · exact ⟨ha,hz,hb⟩
  · simp only [forcedRowConstruction]
    split_ifs
    · exact atomicIntegerRow_literals _ _ _ M
        (fun i => integerPick_magnitude j i (-1) M (by simpa using hM)) hz (by simpa using hM)
    · exact ⟨fun i => integerPick_magnitude j i 1 M (by simpa using hM),hz,
        ⟨by simpa using hm j,by simpa using hM⟩⟩
  · simp only [forcedRowConstruction,forcedOrdinaryConstruction]
    split_ifs
    · exact atomicIntegerRow_literals _ _ _ M hz hz (Nat.zero_le _)
    · exact prefixRowConstruction_literals P k a M hM (hm k) hw
  · exact forcedSlopeConstruction_literals P j u v a M hM (hm j) hw
  · exact forcedEmptyConstruction_literals P j u v M hM hw
  · exact atomicIntegerRow_literals _ _ _ M hz (fun _ => by simpa using hM) hc

theorem violationRowConstruction_literals (P : Model m) (M : ℕ) (hM : 1 ≤ M)
    (hm : ∀ k, m k ≤ M) (hw : ∀ i, (P.weight i).natAbs ≤ M)
    (ha : ∀ k, (P.coefficient k).natAbs ≤ M) (hb : P.rhs.natAbs ≤ M)
    (hc : P.capacity.natAbs ≤ M) (k : ViolationRow m) :
    (violationRowConstruction P k).LiteralsBounded M := by
  cases k with
  | inl k =>
      exact countRowConstruction_literals P _ _ M hM hm hw ha hb hc
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) _
  | inr u => exact ⟨ha,fun _ => Nat.zero_le _,⟨hb,by simpa using hM⟩⟩

/-- Parity-row arithmetic contains only original dense entries and the constants
0, 1, 2; intermediate sums are handled by the generic subterm envelope. -/
theorem construction_fold_literals (es : List IntegerConstruction) (M : ℕ)
    (h : ∀ e ∈ es, e.LiteralsBounded M) :
    (es.foldr IntegerConstruction.add (.atom 0)).LiteralsBounded M := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih => exact ⟨h e (by simp),ih (fun t ht => h t (by simp [ht]))⟩

theorem parityRowConstruction_literals (a b : Fin q → ℤ) (d : ℤ) (ε : Parity q)
    (M : ℕ) (hM : 2 ≤ M) (ha : ∀ j, (a j).natAbs ≤ M)
    (hb : ∀ j, (b j).natAbs ≤ M) (hd : d.natAbs ≤ M) :
    (parityRowConstruction a b d ε).LiteralsBounded M := by
  refine ⟨fun j => ⟨ha j,by simpa using hM⟩,hb,hd,?_⟩
  apply construction_fold_literals
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  exact ⟨ha j, by
    change (ε j).val ≤ M
    have hj := (ε j).isLt
    omega⟩

end MOR34
