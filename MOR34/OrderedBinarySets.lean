import MOR34.OrderedCounts
import MOR34.BinaryPointBasis

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- A finite nested bit list, in the original class/item coordinate order. -/
def binarySetKey (S : Finset (Item m)) : List (List ℕ) :=
  List.ofFn (fun j : Fin q => List.ofFn (fun u : Fin (m j) => if (⟨j,u⟩ : Item m) ∈ S then 1 else 0))

theorem binarySetKey_injective : Function.Injective (binarySetKey (m := m)) := by
  intro S T h
  apply Finset.ext
  rintro ⟨j,u⟩
  have hj := congrFun (List.ofFn_injective h) j
  have hu := congrFun (List.ofFn_injective hj) u
  by_cases hs : (⟨j,u⟩ : Item m) ∈ S <;>
    by_cases ht : (⟨j,u⟩ : Item m) ∈ T <;> simp [hs, ht] at hu ⊢

def binarySetLE (S T : Finset (Item m)) : Prop := binarySetKey S ≤ binarySetKey T

instance : DecidableRel (binarySetLE (m := m)) := fun S T =>
  inferInstanceAs (Decidable (binarySetKey S ≤ binarySetKey T))
instance : IsTrans (Finset (Item m)) binarySetLE where
  trans _ _ _ hab hbc := le_trans hab hbc
instance : IsAntisymm (Finset (Item m)) binarySetLE where
  antisymm _ _ hab hba := binarySetKey_injective (le_antisymm hab hba)
instance : IsTotal (Finset (Item m)) binarySetLE where
  total S T := le_total (binarySetKey S) (binarySetKey T)

def orderedBinarySets (B : Finset (Finset (Item m))) : List (Finset (Item m)) := B.sort binarySetLE

theorem orderedBinarySets_mem (B : Finset (Finset (Item m))) (S : Finset (Item m)) :
    S ∈ orderedBinarySets B ↔ S ∈ B := Finset.mem_sort binarySetLE

theorem orderedBinarySets_length (B : Finset (Finset (Item m))) :
    (orderedBinarySets B).length = B.card := by simp [orderedBinarySets]

end MOR34
