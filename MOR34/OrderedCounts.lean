import MOR34.BoundedCountForms
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

namespace MOR34
variable {q : ℕ}

/-- An explicit lexicographic relation avoids changing the usual pointwise order. -/
def countLexLE (x y : Counts q) : Prop := List.ofFn x ≤ List.ofFn y

instance : DecidableRel (countLexLE (q := q)) := fun x y =>
  inferInstanceAs (Decidable (List.ofFn x ≤ List.ofFn y))

instance : IsTrans (Counts q) countLexLE where
  trans _ _ _ hab hbc := le_trans hab hbc

instance : IsAntisymm (Counts q) countLexLE where
  antisymm _ _ hab hba := List.ofFn_injective (le_antisymm hab hba)

instance : IsTotal (Counts q) countLexLE where
  total a b := le_total (List.ofFn a) (List.ofFn b)

/-- Computable lexicographic enumeration of the selected finite set. -/
def orderedCounts (B : Finset (Counts q)) : List (Counts q) := B.sort countLexLE

theorem orderedCounts_mem (B : Finset (Counts q)) (z : Counts q) : z ∈ orderedCounts B ↔ z ∈ B :=
  Finset.mem_sort countLexLE

theorem orderedCounts_length (B : Finset (Counts q)) : (orderedCounts B).length = B.card := by
  simp [orderedCounts]

def finAugmentedCount (z : Counts q) : Fin (q+1) → ℤ := Fin.cases 1 (fun j => z j)

def orderedCountMatrix (B : Finset (Counts q)) :
    Matrix (Fin (orderedCounts B).length) (Fin (q+1)) ℤ :=
  fun i => finAugmentedCount ((orderedCounts B).get i)

def finCountEquiv (q : ℕ) : (Fin (q+1) → ℚ) ≃ₗ[ℚ] ℚ × (Fin q → ℚ) where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finAugmentedCount_cast (z : Counts q) :
    finCountEquiv q (fun k => (finAugmentedCount z k : ℚ)) = rationalCountPoint z := by
  rfl

theorem orderedCountMatrix_span (B : Finset (Counts q)) (z : Counts q) :
    (fun k => (finAugmentedCount z k : ℚ)) ∈
      Submodule.span ℚ (Set.range ((orderedCountMatrix B).map (Int.castRingHom ℚ)).row) ↔
    rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B := by
  let e := finCountEquiv q
  have hm : (Submodule.span ℚ (Set.range ((orderedCountMatrix B).map (Int.castRingHom ℚ)).row)).map
      e.toLinearMap = selectedSpan (K := ℚ) rationalCountPoint B := by
    rw [Submodule.map_span, selectedSpan]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨(orderedCounts B).get i, (orderedCounts_mem B _).mp (List.get_mem _ _),
        (finAugmentedCount_cast _).symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((orderedCounts_mem B t).mpr ht)
      refine ⟨_, ⟨i, rfl⟩, ?_⟩
      change finCountEquiv q (fun k => (finAugmentedCount ((orderedCounts B).get i) k : ℚ)) = _
      rw [finAugmentedCount_cast, hi]
  constructor
  · intro hz
    rw [← hm]
    exact ⟨_, hz, finAugmentedCount_cast z⟩
  · intro hz
    rw [← hm] at hz
    obtain ⟨x, hx, he⟩ := hz
    have heq : x = fun k => (finAugmentedCount z k : ℚ) :=
      e.injective (he.trans (finAugmentedCount_cast z).symm)
    rwa [← heq]

end MOR34
