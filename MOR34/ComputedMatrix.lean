import MOR34.ComputedEdges

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def computedEdgeEquiv (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) : (computedEdges solve) ≃ AdjacentEdge P where
  toFun e := ⟨e.val.val, e.val.property, (computedEdges_mem P hWF solve hs e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, e.property.1⟩,
    (computedEdges_mem P hWF solve hs ⟨e.val, e.property.1⟩).mpr e.property.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

abbrev ComputedRowIndex (P : Model m) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :=
  (selectionFinset P S) ⊕ (computedEdges solve)

/-- Matrix data use the actual filtered finite edge list. -/
noncomputable def computedMatrix (P : Model m) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) :
    Matrix (ComputedRowIndex P S solve) (Option (Item m)) ℤ
  | Sum.inl z, none => 1
  | Sum.inl z, some i => indicator (prefixSet z.val) i
  | Sum.inr e, none => 0
  | Sum.inr e, some i =>
      (if i = (⟨e.val.val.1, e.val.val.2.1⟩ : Item m) then 1 else 0) -
      (if i = (⟨e.val.val.1, e.val.val.2.2⟩ : Item m) then 1 else 0)

noncomputable def computedRowEquiv (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) : ComputedRowIndex P S solve ≃ RetainedRowIndex P S :=
  Equiv.sumCongr (Equiv.refl _) (computedEdgeEquiv P hWF solve hs)

theorem computedMatrix_eq_submatrix (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) :
    computedMatrix P S solve = (retainedMatrix P S).submatrix (computedRowEquiv P hWF S solve hs) id := by
  ext r k
  cases r <;> cases k <;> rfl

theorem computed_matrix_rank (P : Model m) (hWF : WellFormed P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (hT : (tightPointSet P).Nonempty) :
    ((computedMatrix P S solve).map (Int.castRingHom ℚ)).rank =
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  classical
  rw [computedMatrix_eq_submatrix P hWF S solve hs]
  change (((retainedMatrix P S).map (Int.castRingHom ℚ)).submatrix
    (computedRowEquiv P hWF S solve hs) (Equiv.refl (Option (Item m)))).rank = _
  rw [Matrix.rank_submatrix]
  exact retained_matrix_rational_rank P hWF S hT

theorem computedRowIndex_card (P : Model m) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hsmall : ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) :
    Fintype.card (ComputedRowIndex P S solve) ≤ Fintype.card (Item m) + (q + 1) * 6 ^ q := by
  classical
  have hb := selectionFinset_card P S hsmall
  have he := computedEdges_card solve
  simp only [ComputedRowIndex, Fintype.card_sum, Fintype.card_coe]
  omega

end MOR34
