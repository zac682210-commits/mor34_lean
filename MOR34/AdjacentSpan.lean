import MOR34.TightDimension

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def adjacentDirectionSpan (P : Model m) : Submodule ℝ (Item m → ℝ) :=
  Submodule.span ℝ {x | ∃ (j : Fin q) (u v : Fin (m j)),
    u.val + 1 = v.val ∧ Exchange P j u v ∧
      x = unitVector (⟨j, u⟩ : Item m) - unitVector (⟨j, v⟩ : Item m)}

theorem adjacent_path_difference_mem (P : Model m) (j : Fin q) {a b : Fin (m j)}
    (h : Relation.ReflTransGen (fun u v : Fin (m j) =>
      u.val + 1 = v.val ∧ Exchange P j u v) a b) :
    unitVector (⟨j, a⟩ : Item m) - unitVector (⟨j, b⟩ : Item m) ∈
      adjacentDirectionSpan P := by
  induction h with
  | refl => simp only [sub_self]; exact Submodule.zero_mem _
  | @tail b c hab hbc ih =>
    have he : unitVector (⟨j, b⟩ : Item m) - unitVector (⟨j, c⟩ : Item m) ∈
        adjacentDirectionSpan P := Submodule.subset_span ⟨j, b, c, hbc.1, hbc.2, rfl⟩
    have hs := Submodule.add_mem (adjacentDirectionSpan P) ih he
    convert hs using 1 <;> abel

theorem adjacentDirectionSpan_eq_exchange (P : Model m) (hWF : WellFormed P) :
    adjacentDirectionSpan P = exchangeDirectionSpan P := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, u, v, _, he, rfl⟩
    exact Submodule.subset_span ⟨j, u, v, he, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨j, a, b, he, rfl⟩
    apply adjacent_path_difference_mem P j
    apply adjacent_chain a b (le_of_lt he.1)
    intro u v hau huv hvb
    refine ⟨huv, intervalExchange P hWF j a b u v he hau ?_ hvb⟩
    change u.val < v.val
    omega

theorem adjacentDirectionSpan_eq_ker (P : Model m) (hWF : WellFormed P) :
    adjacentDirectionSpan P = LinearMap.ker (componentCountMap P) := by
  rw [adjacentDirectionSpan_eq_exchange P hWF, exchangeDirectionSpan_eq_ker]

end MOR34
