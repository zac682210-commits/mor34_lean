import MOR34.ForcedLinearEncoding

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def forcedOrdinaryRow (P : Model m) (j k : Fin q) (a : Fin (m k)) : CountInequality q :=
  if k = j then integerRow 0 0 0 else
    integerRow (integerPick k (P.weight ⟨k, a⟩)) (integerPick k (-1))
      (P.weight ⟨k, a⟩ * (a.val : ℤ) - prefixCost (fun t => P.weight ⟨k, t⟩) a.val)

theorem forcedOrdinaryRow_iff (P : Model m) (j k : Fin q) (a : Fin (m k))
    (z y : Fin q → ℤ) :
    (forcedOrdinaryRow P j k a).Holds z y ↔
      (k ≠ j → prefixLine (fun t => P.weight ⟨k, t⟩) a (z k) ≤ y k) := by
  by_cases hk : k = j
  · simp [forcedOrdinaryRow, hk, integerRow_iff]
  · simp only [forcedOrdinaryRow, hk, ite_false, integerRow_iff,
      integerPick_sum, neg_one_mul, not_false_eq_true, true_implies]
    unfold prefixLine
    constructor <;> intro h <;> nlinarith

abbrev ForcedRow (m : Fin q → ℕ) (j : Fin q) (u v : Fin (m j)) :=
  ((Fin q ⊕ Fin q) ⊕ (Fin 2 ⊕ Fin 2)) ⊕
    (Item m ⊕ (Fin (pairAllowed u v).card ⊕ (Unit ⊕ Unit)))

/-- Redundant zero ordinary rows keep a uniform finite index type. -/
def forcedRow (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    ForcedRow m j u v → CountInequality q
  | Sum.inl (Sum.inl (Sum.inl k)) => integerRow (integerPick k (-1)) 0 0
  | Sum.inl (Sum.inl (Sum.inr k)) => integerRow (integerPick k 1) 0 (m k)
  | Sum.inl (Sum.inr (Sum.inl b)) =>
      if b = 0 then integerRow P.coefficient 0 P.rhs
      else integerRow (fun k => -P.coefficient k) 0 (-P.rhs)
  | Sum.inl (Sum.inr (Sum.inr b)) =>
      if b = 0 then integerRow (integerPick j (-1)) 0 (-1)
      else integerRow (integerPick j 1) 0 ((m j : ℤ) - 1)
  | Sum.inr (Sum.inl ⟨k, a⟩) => forcedOrdinaryRow P j k a
  | Sum.inr (Sum.inr (Sum.inl a)) => forcedSlopeRow P j u v a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => forcedEmptyRow P j u v
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => integerRow 0 (fun _ => 1) P.capacity

theorem forcedRows_iff (P : Model m) (j : Fin q) (u v : Fin (m j)) (z y : Fin q → ℤ) :
    (∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y) ↔
      IntegerCountBounds (m := m) z ∧ 1 ≤ z j ∧ z j ≤ (m j : ℤ) - 1 ∧
      (∑ k, P.coefficient k * z k) = P.rhs ∧ IntegerForcedEpigraph P j u v z y := by
  simp only [Sum.forall, forcedRow, Fin.forall_fin_two, ↓reduceIte, zero_ne_one,
    one_ne_zero, integerRow_iff, integerPick_sum, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, neg_one_mul, one_mul,
    neg_mul, Finset.sum_neg_distrib, Sigma.forall, forcedOrdinaryRow_iff,
    forcedSlopeRow_iff, Unit.forall, forcedEmptyRow_iff]
  constructor
  · rintro ⟨⟨⟨hl, hu⟩, ⟨he, hf⟩⟩, ⟨ho, hs, hzero, hc⟩⟩
    refine ⟨(fun k => ⟨by have h := hl k; omega, hu k⟩), ?_, hf.2, ?_,
      hzero, hs, (fun k hk a => ho k a hk), hc⟩
    · omega
    · omega
  · rintro ⟨hb, hl, hu, he, hzero, hs, ho, hc⟩
    refine ⟨⟨⟨(fun k => ?_), (fun k => (hb k).2)⟩, ⟨?_, ?_⟩⟩,
      ⟨(fun k a hk => ho k hk a), hs, hzero, hc⟩⟩
    · have h := (hb k).1; omega
    · constructor <;> omega
    · constructor <;> omega

/-- Exact equivalence of explicit integer rows with the original exchange predicate. -/
theorem exchange_iff_forced_rows (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) :
    Exchange P j u v ↔ u < v ∧ ∃ z y : Fin q → ℤ,
      ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y := by
  rw [exchange_iff_forced_epigraph P hWF j u v]
  constructor
  · rintro ⟨huv, z, hb, hl, hu, he, y, hy⟩
    refine ⟨huv, encodeCounts z, y, (forcedRows_iff P j u v _ _).mpr
      ⟨(integerCountBounds_encode z).mpr hb, ?_, ?_, ?_,
        (integerForcedEpigraph_encode P j u v z hl y).mpr hy⟩⟩
    · dsimp [encodeCounts]; omega
    · have hm := v.isLt
      dsimp [encodeCounts]; omega
    · simpa only [encodeCounts, mul_comm] using he
  · rintro ⟨huv, z, y, hh⟩
    obtain ⟨hb, hl, hu, he, hy⟩ := (forcedRows_iff P j u v z y).mp hh
    have hbound := decodeCounts_bounded z hb
    have hid := encode_decodeCounts z hb
    have hj := congrFun hid j
    have hl' : 1 ≤ decodeCounts z j := by change (decodeCounts z j : ℤ) = z j at hj; omega
    have hu' : decodeCounts z j ≤ m j - 1 := by
      change (decodeCounts z j : ℤ) = z j at hj
      omega
    refine ⟨huv, decodeCounts z, hbound, hl', hu', ?_, y, ?_⟩
    · have he' : (∑ k, P.coefficient k * encodeCounts (decodeCounts z) k) = P.rhs := by
        rw [hid]; exact he
      simpa only [encodeCounts, mul_comm] using he'
    · apply (integerForcedEpigraph_encode P j u v _ hl' y).mp
      rw [hid]
      exact hy

/-- The uniform row family is linear-size; it retains harmless zero rows. -/
theorem forcedRow_card (j : Fin q) (u v : Fin (m j)) :
    Fintype.card (ForcedRow m j u v) =
      Fintype.card (Item m) + 2 * q + (pairAllowed u v).card + 6 := by
  simp [ForcedRow]; omega

end MOR34
