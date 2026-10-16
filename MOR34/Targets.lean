import MOR34.Model

/-!
OPEN TARGETS, not theorems. Each declaration below is a definition of a proposition.
No proof term for any of these propositions is supplied in this checkpoint.
-/

namespace MOR34

/-- First finite-set target: force two elements into each equal half. -/
def BalancedSplitGoal : Prop :=
  ∀ (α : Type) [DecidableEq α] (D P N : Finset α) (k : ℕ),
    P ⊆ D → N ⊆ D → Disjoint P N → P.card = 2 → N.card = 2 →
    D.card = 2 * k → 2 ≤ k →
    ∃ U V : Finset α, U ∪ V = D ∧ Disjoint U V ∧
      U.card = k ∧ V.card = k ∧ P ⊆ U ∧ N ⊆ V

variable {q : ℕ} {m : Fin q → ℕ}

/-- Combinatorial part of paper Lemma 4, for one fixed interior cut. -/
def PairingAtCutGoal : Prop :=
  ∀ (z w : Counts q), BoundedCounts (m := m) z → BoundedCounts (m := m) w →
    SameParity z w → ∀ (j : Fin q) (r : ℕ),
    z j + 2 ≤ r → r + 2 ≤ w j →
    ∃ U V : Finset (Item m),
      Repartitions (prefix z) (prefix w) U V ∧ BalancedCounts z w U V ∧
      Crosses j r U ∧ Crosses j r V

/-- Target corresponding to the adjacent-cut conclusion of paper Lemma 4. -/
def InteriorExchangeGoal (P : Model m) : Prop :=
  WellFormed P → ∀ (z w : Counts q),
    BoundedCounts (m := m) z → BoundedCounts (m := m) w →
    Tight P (prefix z) → Tight P (prefix w) → SameParity z w →
    ∀ (j : Fin q) (r : ℕ), z j + 2 ≤ r → r + 2 ≤ w j →
      AdjacentExchangeCut P j r

end MOR34
