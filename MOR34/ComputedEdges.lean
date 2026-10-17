import MOR34.ForcedSolver
import MOR34.RetainedMatrix

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

abbrev AdjacentPair (m : Fin q → ℕ) :=
  {t : (j : Fin q) × (Fin (m j) × Fin (m j)) // t.2.1.val + 1 = t.2.2.val}

instance adjacentPairFintype (m : Fin q → ℕ) : Fintype (AdjacentPair m) := inferInstance

def computedEdges
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    Finset (AdjacentPair m) :=
  Finset.univ.filter (fun e => exchangeDecision solve e.val.1 e.val.2.1 e.val.2.2 = true)

theorem computedEdges_mem (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : AdjacentPair m) :
    e ∈ computedEdges solve ↔ Exchange P e.val.1 e.val.2.1 e.val.2.2 := by
  simp only [computedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exchangeDecision_iff P hWF solve hs _ _ _

/-- Only adjacent pairs are queried; there are at most n of them. -/
theorem adjacentPair_card (m : Fin q → ℕ) :
    Fintype.card (AdjacentPair m) ≤ Fintype.card (Item m) := by
  let f : AdjacentPair m → Item m := fun e => ⟨e.val.1, e.val.2.1⟩
  apply Fintype.card_le_of_injective f
  rintro ⟨⟨j, u, v⟩, h⟩ ⟨⟨k, w, t⟩, h'⟩ he
  change (⟨j, u⟩ : Item m) = ⟨k, w⟩ at he
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
  cases he
  have hv : v = t := Fin.ext (by omega)
  subst t
  rfl

theorem computedEdges_card
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    (computedEdges solve).card ≤ Fintype.card (Item m) := by
  have hh : (computedEdges solve).card ≤ Fintype.card (AdjacentPair m) := Finset.card_le_univ _
  exact le_trans hh (adjacentPair_card m)

/-- The filtered finite list has exactly the direction span used in the structural theorem. -/
theorem computedEdges_span (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    Submodule.span ℝ {x | ∃ e ∈ computedEdges solve,
      x = unitVector (⟨e.val.1, e.val.2.1⟩ : Item m) -
        unitVector (⟨e.val.1, e.val.2.2⟩ : Item m)} = adjacentDirectionSpan P := by
  unfold adjacentDirectionSpan
  congr 1
  ext x
  constructor
  · rintro ⟨e, he, hx⟩
    exact ⟨e.val.1, e.val.2.1, e.val.2.2, e.property,
      (computedEdges_mem P hWF solve hs e).mp he, hx⟩
  · rintro ⟨j, u, v, ha, he, hx⟩
    let e : AdjacentPair m := ⟨⟨j, u, v⟩, ha⟩
    exact ⟨e, (computedEdges_mem P hWF solve hs e).mpr he, hx⟩

end MOR34
