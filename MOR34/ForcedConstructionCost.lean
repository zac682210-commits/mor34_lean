import MOR34.CountConstructionCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def forcedSlopeConstruction (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) : ConstructedIntegerRow q :=
  ⟨fun k => .atom (integerPick j (forcedResidualWeights P j u v a) k),
    fun k => .atom (integerPick j (-1) k),
    .add (.add
      (.mul (.add (.atom a.val) (.atom 1)) (.atom (forcedResidualWeights P j u v a)))
      (.neg (prefixConstruction (forcedResidualWeights P j u v) a.val)))
      (.neg (.atom (P.weight ⟨j,v⟩)))⟩

theorem forcedSlopeConstruction_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) :
    (forcedSlopeConstruction P j u v a).value = forcedSlopeRow P j u v a := by
  simp only [ConstructedIntegerRow.value, forcedSlopeConstruction, IntegerConstruction.value,
    prefixConstruction_value, forcedSlopeRow, sub_eq_add_neg]

theorem forcedSlopeConstruction_work (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) :
    (forcedSlopeConstruction P j u v a).work ≤ 2*q+2*m j+11 := by
  have hh := prefixConstruction_work (forcedResidualWeights P j u v) a.val
  have hc : (pairAllowed u v).card ≤ m j := by simpa using Finset.card_le_univ (pairAllowed u v)
  simp only [ConstructedIntegerRow.work, forcedSlopeConstruction, IntegerConstruction.work,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]
  omega

def forcedEmptyConstruction (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    ConstructedIntegerRow q :=
  if (pairAllowed u v).card = 0 then
    ⟨fun _ => .atom 0, fun k => .atom (integerPick j (-1) k), .neg (.atom (P.weight ⟨j,v⟩))⟩
  else atomicIntegerRow 0 0 0

theorem forcedEmptyConstruction_value (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    (forcedEmptyConstruction P j u v).value = forcedEmptyRow P j u v := by
  unfold forcedEmptyConstruction forcedEmptyRow
  split_ifs <;> rfl

theorem forcedEmptyConstruction_work (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    (forcedEmptyConstruction P j u v).work ≤ 2*q+2 := by
  unfold forcedEmptyConstruction
  split_ifs
  · simp [ConstructedIntegerRow.work, IntegerConstruction.work] <;> omega
  · rw [atomicIntegerRow_work]; omega

def forcedOrdinaryConstruction (P : Model m) (j k : Fin q) (a : Fin (m k)) :
    ConstructedIntegerRow q :=
  if k = j then atomicIntegerRow 0 0 0 else prefixRowConstruction P k a

theorem forcedOrdinaryConstruction_value (P : Model m) (j k : Fin q) (a : Fin (m k)) :
    (forcedOrdinaryConstruction P j k a).value = forcedOrdinaryRow P j k a := by
  unfold forcedOrdinaryConstruction forcedOrdinaryRow
  split_ifs
  · rfl
  · exact prefixRowConstruction_value P k a

def forcedRowConstruction (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    ForcedRow m j u v → ConstructedIntegerRow q
  | .inl (.inl (.inl k)) => atomicIntegerRow (integerPick k (-1)) 0 0
  | .inl (.inl (.inr k)) => atomicIntegerRow (integerPick k 1) 0 (m k)
  | .inl (.inr (.inl b)) => if b = 0 then atomicIntegerRow P.coefficient 0 P.rhs
      else ⟨fun k => .neg (.atom (P.coefficient k)), fun _ => .atom 0, .neg (.atom P.rhs)⟩
  | .inl (.inr (.inr b)) => if b = 0 then atomicIntegerRow (integerPick j (-1)) 0 (-1)
      else ⟨fun k => .atom (integerPick j 1 k), fun _ => .atom 0,
        .add (.atom (m j)) (.neg (.atom 1))⟩
  | .inr (.inl ⟨k,a⟩) => forcedOrdinaryConstruction P j k a
  | .inr (.inr (.inl a)) => forcedSlopeConstruction P j u v a
  | .inr (.inr (.inr (.inl _))) => forcedEmptyConstruction P j u v
  | .inr (.inr (.inr (.inr _))) => atomicIntegerRow 0 (fun _ => 1) P.capacity

theorem forcedRowConstruction_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (k : ForcedRow m j u v) : (forcedRowConstruction P j u v k).value = forcedRow P j u v k := by
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  · rfl
  · rfl
  · simp only [forcedRowConstruction, forcedRow]
    split_ifs <;> rfl
  · simp only [forcedRowConstruction, forcedRow]
    split_ifs <;> simp only [ConstructedIntegerRow.value, IntegerConstruction.value,
      atomicIntegerRow_value, sub_eq_add_neg]
  · exact forcedOrdinaryConstruction_value P j k a
  · exact forcedSlopeConstruction_value P j u v a
  · exact forcedEmptyConstruction_value P j u v
  · rfl

theorem forcedRowConstruction_work (P : Model m) (j : Fin q) (u v : Fin (m j))
    (n : ℕ) (hm : ∀ k, m k ≤ n) (k : ForcedRow m j u v) :
    (forcedRowConstruction P j u v k).work ≤ 4*q+2*n+12 := by
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  · simp only [forcedRowConstruction, atomicIntegerRow_work]; omega
  · simp only [forcedRowConstruction, atomicIntegerRow_work]; omega
  · simp only [forcedRowConstruction]
    split_ifs <;> simp [atomicIntegerRow_work, ConstructedIntegerRow.work,
      IntegerConstruction.work] <;> omega
  · simp only [forcedRowConstruction]
    split_ifs <;> simp [atomicIntegerRow_work, ConstructedIntegerRow.work,
      IntegerConstruction.work] <;> omega
  · simp only [forcedRowConstruction, forcedOrdinaryConstruction]
    split_ifs
    · rw [atomicIntegerRow_work]; omega
    · exact (prefixRowConstruction_work P k a).trans (by have hh := hm k; omega)
  · exact (forcedSlopeConstruction_work P j u v a).trans (by have hh := hm j; omega)
  · exact (forcedEmptyConstruction_work P j u v).trans (by omega)
  · simp only [forcedRowConstruction, atomicIntegerRow_work]; omega

theorem forcedConstructionWork_polynomial (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (L : ℕ) :
    (∑ k : ForcedRow m j u v, (forcedRowConstruction P j u v k).work) ≤
      144*(Fintype.card (Item m)+L+2)^2 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  have hp : (pairAllowed u v).card ≤ n :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans (hm j)
  calc
    _ ≤ ∑ _k : ForcedRow m j u v, (4*q+2*n+12) :=
      Finset.sum_le_sum (fun k _ => forcedRowConstruction_work P j u v n hm k)
    _ = (n+2*q+(pairAllowed u v).card+6)*(4*q+2*n+12) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, forcedRow_card] <;> rfl
    _ ≤ (6*(n+L+2))*(24*(n+L+2)) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

end MOR34
