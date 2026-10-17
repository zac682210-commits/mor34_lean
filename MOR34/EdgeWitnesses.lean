import MOR34.ComputedMatrix

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem computed_edge_has_witness (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : computedEdges solve) :
    ∃ S, exchangeWitness solve e.val.val.1 e.val.val.2.1 e.val.val.2.2 = some S := by
  cases he : exchangeWitness solve e.val.val.1 e.val.val.2.1 e.val.val.2.2 with
  | some S => exact ⟨S, rfl⟩
  | none =>
    have hn := (exchangeWitness_none_iff P hWF solve hs _ _ _).mp he
    exact False.elim (hn ((computedEdges_mem P hWF solve hs e.val).mp e.property))

/-- Extract the actual solver result, not an unrelated existential exchange witness. -/
def computedEdgeWitness (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : computedEdges solve) : Finset (Item m) :=
  (exchangeWitness solve e.val.val.1 e.val.val.2.1 e.val.val.2.2).get
    (Option.isSome_iff_exists.mpr (computed_edge_has_witness P hWF solve hs e))

theorem computedEdgeWitness_result (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : computedEdges solve) :
    exchangeWitness solve e.val.val.1 e.val.val.2.1 e.val.val.2.2 =
      some (computedEdgeWitness P hWF solve hs e) := (Option.some_get _).symm

def computedEdgeSwap (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : computedEdges solve) : Finset (Item m) :=
  insert (⟨e.val.val.1, e.val.val.2.1⟩ : Item m)
    ((computedEdgeWitness P hWF solve hs e).erase ⟨e.val.val.1, e.val.val.2.2⟩)

/-- Each computed direction has two returned original tight binary points. -/
theorem computedEdgeWitness_pair (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (e : computedEdges solve) :
    Tight P (computedEdgeWitness P hWF solve hs e) ∧
      Tight P (computedEdgeSwap P hWF solve hs e) ∧
      pointVector (computedEdgeSwap P hWF solve hs e) -
        pointVector (computedEdgeWitness P hWF solve hs e) =
          unitVector (⟨e.val.val.1, e.val.val.2.1⟩ : Item m) -
            unitVector (⟨e.val.val.1, e.val.val.2.2⟩ : Item m) := by
  obtain ⟨huv, ht, hu, hv⟩ := exchangeWitness_some P hWF solve hs _ _ _ _
    (computedEdgeWitness_result P hWF solve hs e)
  refine ⟨ht, ?_, pointVector_swap_difference _ _ _ hu hv⟩
  exact tight_swap P ht hu hv (hWF.2.2.2.2.2.2.2 _ _ _ (le_of_lt huv)) rfl

end MOR34
