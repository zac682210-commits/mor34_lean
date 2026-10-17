import MOR34.LinearEncoding
import MOR34.ExchangeEncoding

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Integer input data for a rational row; the two variable blocks remain integer. -/
def integerRow (a b : Fin q → ℤ) (c : ℤ) : CountInequality q :=
  ⟨fun k => a k, fun k => b k, c⟩

theorem integerRow_iff (a b : Fin q → ℤ) (c : ℤ) (z y : Fin q → ℤ) :
    (integerRow a b c).Holds z y ↔ (∑ k, a k * z k) + (∑ k, b k * y k) ≤ c := by
  unfold integerRow CountInequality.Holds
  constructor <;> intro h <;> exact_mod_cast h

def integerPick (j : Fin q) (c : ℤ) : Fin q → ℤ := fun k => if k = j then c else 0

theorem integerPick_sum (j : Fin q) (c : ℤ) (z : Fin q → ℤ) :
    (∑ k, integerPick j c k * z k) = c * z j := by simp [integerPick, ite_mul]

def forcedResidualWeights (P : Model m) (j : Fin q) (u v : Fin (m j)) :
    Fin (pairAllowed u v).card → ℤ :=
  fun i => P.weight ⟨j, (pairAllowed u v).orderEmbOfFin rfl i⟩

def forcedSlopeRow (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) : CountInequality q :=
  integerRow (integerPick j (forcedResidualWeights P j u v a)) (integerPick j (-1))
    (((a.val : ℤ) + 1) * forcedResidualWeights P j u v a -
      prefixCost (forcedResidualWeights P j u v) a.val - P.weight ⟨j, v⟩)

theorem forcedSlopeRow_iff (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (z y : Fin q → ℤ) :
    (forcedSlopeRow P j u v a).Holds z y ↔
      P.weight ⟨j, v⟩ + prefixLine (forcedResidualWeights P j u v) a (z j - 1) ≤ y j := by
  rw [forcedSlopeRow, integerRow_iff, integerPick_sum, integerPick_sum]
  unfold prefixLine
  constructor <;> intro h <;> nlinarith

/-- This row is active exactly when deleting the pair leaves no residual item. -/
def forcedEmptyRow (P : Model m) (j : Fin q) (u v : Fin (m j)) : CountInequality q :=
  if (pairAllowed u v).card = 0 then
    integerRow 0 (integerPick j (-1)) (-P.weight ⟨j, v⟩)
  else integerRow 0 0 0

theorem forcedEmptyRow_iff (P : Model m) (j : Fin q) (u v : Fin (m j))
    (z y : Fin q → ℤ) :
    (forcedEmptyRow P j u v).Holds z y ↔
      ((pairAllowed u v).card = 0 → P.weight ⟨j, v⟩ ≤ y j) := by
  by_cases he : (pairAllowed u v).card = 0
  · simp [forcedEmptyRow, he, integerRow_iff, integerPick_sum]
  · simp [forcedEmptyRow, he, integerRow_iff]

/-- The truncation cast is justified by the required positive forced count. -/
theorem forcedSlopeRow_counts (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (z : Counts q) (hl : 1 ≤ z j) (y : Fin q → ℤ) :
    (forcedSlopeRow P j u v a).Holds (encodeCounts z) y ↔
      P.weight ⟨j, v⟩ + prefixLine (forcedResidualWeights P j u v) a ((z j - 1 : ℕ) : ℤ) ≤ y j := by
  have he : ((z j - 1 : ℕ) : ℤ) = (z j : ℤ) - 1 := by omega
  rw [forcedSlopeRow_iff, he]
  rfl

/-- Exact integer-count version of the already verified global forced epigraph. -/
def IntegerForcedEpigraph (P : Model m) (j : Fin q) (u v : Fin (m j))
    (z y : Fin q → ℤ) : Prop :=
  ((pairAllowed u v).card = 0 → P.weight ⟨j, v⟩ ≤ y j) ∧
  (∀ a : Fin (pairAllowed u v).card,
    P.weight ⟨j, v⟩ + prefixLine (forcedResidualWeights P j u v) a (z j - 1) ≤ y j) ∧
  (∀ k, k ≠ j → ∀ a : Fin (m k),
    prefixLine (fun i => P.weight ⟨k, i⟩) a (z k) ≤ y k) ∧
  (∑ k, y k) ≤ P.capacity

theorem integerForcedEpigraph_encode (P : Model m) (j : Fin q) (u v : Fin (m j))
    (z : Counts q) (hl : 1 ≤ z j) (y : Fin q → ℤ) :
    IntegerForcedEpigraph P j u v (encodeCounts z) y ↔ ForcedEpigraph P j u v z y := by
  have he : ((z j - 1 : ℕ) : ℤ) = (z j : ℤ) - 1 := by omega
  simp only [IntegerForcedEpigraph, ForcedEpigraph, forcedResidualWeights, encodeCounts, he,
    and_assoc]

end MOR34
