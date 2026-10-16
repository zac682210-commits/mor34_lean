import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic

/-!
Draft definitions for MOR34. NOT compiler-checked in this checkpoint.
Indices within a class are zero-based. A cut r separates indices < r from >= r.
No theorem about facet recognition or running time is claimed here.
-/

namespace MOR34

abbrev Item {q : ℕ} (m : Fin q → ℕ) := (j : Fin q) × Fin (m j)
abbrev Counts (q : ℕ) := Fin q → ℕ

variable {q : ℕ} {m : Fin q → ℕ}

/-- Raw grouped data; mathematical hypotheses are recorded by `WellFormed`. -/
structure Model (m : Fin q → ℕ) where
  weight : Item m → ℤ
  coefficient : Fin q → ℤ
  capacity : ℤ
  rhs : ℤ

def WellFormed (P : Model m) : Prop :=
  0 < q ∧ (∀ j, 0 < m j) ∧
  (∀ i, 0 < P.weight i) ∧ 0 < P.capacity ∧
  (∀ i, P.weight i ≤ P.capacity) ∧
  (∀ j, 0 ≤ P.coefficient j) ∧ Function.Injective P.coefficient ∧
  (∀ j (u v : Fin (m j)), u ≤ v → P.weight ⟨j, u⟩ ≤ P.weight ⟨j, v⟩)

def weightSum (P : Model m) (S : Finset (Item m)) : ℤ :=
  ∑ i ∈ S, P.weight i

def candidateValue (P : Model m) (S : Finset (Item m)) : ℤ :=
  ∑ i ∈ S, P.coefficient i.1

def Feasible (P : Model m) (S : Finset (Item m)) : Prop :=
  weightSum P S ≤ P.capacity

/-- A feasible equality level. Validity of the inequality is a separate condition. -/
def Tight (P : Model m) (S : Finset (Item m)) : Prop :=
  Feasible P S ∧ candidateValue P S = P.rhs

def Valid (P : Model m) : Prop :=
  ∀ S : Finset (Item m), Feasible P S → candidateValue P S ≤ P.rhs

def counts (S : Finset (Item m)) (j : Fin q) : ℕ :=
  (S.filter fun i => i.1 = j).card

def BoundedCounts (z : Counts q) : Prop := ∀ j, z j ≤ m j

def prefixSet (z : Counts q) : Finset (Item m) :=
  Finset.univ.filter fun i => i.2.val < z i.1

def SameParity (z w : Counts q) : Prop := ∀ j, z j % 2 = w j % 2

def indicator {α : Type*} [DecidableEq α] (S : Finset α) (i : α) : ℤ :=
  if i ∈ S then 1 else 0

def Repartitions (S T U V : Finset (Item m)) : Prop :=
  ∀ i, indicator U i + indicator V i = indicator S i + indicator T i

/-- Equal half-counts, expressed without natural-number division. -/
def BalancedCounts (z w : Counts q) (U V : Finset (Item m)) : Prop :=
  ∀ j, counts U j = counts V j ∧ counts U j + counts V j = z j + w j

def Crosses (j : Fin q) (r : ℕ) (S : Finset (Item m)) : Prop :=
  ∃ u v : Fin (m j), u.val < r ∧ r ≤ v.val ∧
    (⟨j, u⟩ : Item m) ∉ S ∧ (⟨j, v⟩ : Item m) ∈ S

def Exchange (P : Model m) (j : Fin q) (u v : Fin (m j)) : Prop :=
  u < v ∧ ∃ S : Finset (Item m), Tight P S ∧
    (⟨j, u⟩ : Item m) ∉ S ∧ (⟨j, v⟩ : Item m) ∈ S

def AdjacentExchangeCut (P : Model m) (j : Fin q) (r : ℕ) : Prop :=
  ∃ u v : Fin (m j), u.val + 1 = r ∧ v.val = r ∧ Exchange P j u v

end MOR34
