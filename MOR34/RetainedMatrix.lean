import MOR34.StructuralTheorem

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

abbrev AdjacentEdge (P : Model m) :=
  {t : (j : Fin q) × (Fin (m j) × Fin (m j)) //
    t.2.1.val + 1 = t.2.2.val ∧ Exchange P t.1 t.2.1 t.2.2}

noncomputable instance adjacentEdgeFintype (P : Model m) : Fintype (AdjacentEdge P) := by
  classical
  infer_instance

abbrev RetainedRowIndex (P : Model m) (S : CellBasisSelection P) :=
  (selectionFinset P S) ⊕ AdjacentEdge P

noncomputable def retainedRowReal (P : Model m) (S : CellBasisSelection P) :
    RetainedRowIndex P S → ℝ × (Item m → ℝ)
  | Sum.inl z => pointAugment (pointVector (prefixSet z.val))
  | Sum.inr e => zeroAugment (unitVector (⟨e.val.1, e.val.2.1⟩ : Item m) -
      unitVector (⟨e.val.1, e.val.2.2⟩ : Item m))

noncomputable def retainedRowInt (P : Model m) (S : CellBasisSelection P) :
    RetainedRowIndex P S → ℤ × (Item m → ℤ)
  | Sum.inl z => (1, indicator (prefixSet z.val))
  | Sum.inr e => (0, fun i =>
      (if i = (⟨e.val.1, e.val.2.1⟩ : Item m) then 1 else 0) -
      (if i = (⟨e.val.1, e.val.2.2⟩ : Item m) then 1 else 0))

noncomputable def retainedMatrix (P : Model m) (S : CellBasisSelection P) :
    Matrix (RetainedRowIndex P S) (Option (Item m)) ℤ :=
  fun r k => match k with
    | none => (retainedRowInt P S r).1
    | some i => (retainedRowInt P S r).2 i

theorem retained_row_cast (P : Model m) (S : CellBasisSelection P) (r : RetainedRowIndex P S) :
    (LinearEquiv.piOptionEquivProd ℝ : (Option (Item m) → ℝ) ≃ₗ[ℝ] ℝ × (Item m → ℝ))
      (fun k => (retainedMatrix P S r k : ℝ)) = retainedRowReal P S r := by
  cases r <;> ext i <;>
    simp [retainedMatrix, retainedRowInt, retainedRowReal, LinearEquiv.piOptionEquivProd,
      Equiv.piOptionEquivProd, pointAugment, zeroAugment, pointVector, indicator, unitVector]

theorem retained_row_span (P : Model m) (S : CellBasisSelection P) :
    Submodule.span ℝ (Set.range (retainedRowReal P S)) =
      augmentedSpan (selectedPoints P S) ⊔ (adjacentDirectionSpan P).map zeroAugment := by
  classical
  rw [adjacentDirectionSpan, Submodule.map_span, augmentedSpan, ← Submodule.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    cases r with
    | inl z =>
      apply Or.inl
      refine ⟨pointVector (prefixSet z.val), ⟨z.val, ?_, rfl⟩, rfl⟩
      rw [← selectionFinset_coe]
      exact z.property
    | inr e =>
      exact Or.inr ⟨_, ⟨e.val.1, e.val.2.1, e.val.2.2, e.property.1, e.property.2, rfl⟩, rfl⟩
  · rintro (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | ⟨_, ⟨j, u, v, huv, he, rfl⟩, rfl⟩)
    · have hz' : z ∈ selectionFinset P S := by
        change z ∈ (↑(selectionFinset P S) : Set (Counts q))
        rw [selectionFinset_coe]
        exact hz
      exact ⟨Sum.inl ⟨z, hz'⟩, rfl⟩
    · exact ⟨Sum.inr ⟨⟨j, u, v⟩, huv, he⟩, rfl⟩

theorem retained_matrix_real_rank (P : Model m) (S : CellBasisSelection P) :
    ((retainedMatrix P S).map (Int.castRingHom ℝ)).rank =
      Module.finrank ℝ ((augmentedSpan (selectedPoints P S) ⊔
        (adjacentDirectionSpan P).map zeroAugment : Submodule ℝ (ℝ × (Item m → ℝ)))) := by
  classical
  let e : (Option (Item m) → ℝ) ≃ₗ[ℝ] ℝ × (Item m → ℝ) := LinearEquiv.piOptionEquivProd ℝ
  rw [Matrix.rank_eq_finrank_span_row]
  have hm : (Submodule.span ℝ (Set.range ((retainedMatrix P S).map (Int.castRingHom ℝ)))).map
      e.toLinearMap = Submodule.span ℝ (Set.range (retainedRowReal P S)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, (retained_row_cast P S r).symm⟩
    · rintro ⟨r, rfl⟩
      exact ⟨_, ⟨r, rfl⟩, retained_row_cast P S r⟩
  rw [← retained_row_span, ← hm]
  exact (e.finrank_map_eq _).symm

/-- A concrete finite integer row matrix has the required rational rank. -/
theorem retained_matrix_rational_rank (P : Model m) (hWF : WellFormed P)
    (S : CellBasisSelection P) (hT : (tightPointSet P).Nonempty) :
    ((retainedMatrix P S).map (Int.castRingHom ℚ)).rank =
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  rw [← integer_matrix_rank, retained_matrix_real_rank]
  exact selected_dimension P hWF S hT

theorem adjacentEdge_card (P : Model m) :
    Fintype.card (AdjacentEdge P) ≤ Fintype.card (Item m) := by
  classical
  let f : AdjacentEdge P → Item m := fun e => ⟨e.val.1, e.val.2.1⟩
  apply Fintype.card_le_of_injective f
  rintro ⟨⟨j, u, v⟩, h⟩ ⟨⟨k, w, t⟩, h'⟩ he
  change (⟨j, u⟩ : Item m) = ⟨k, w⟩ at he
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp he
  cases he
  have h1 : u.val + 1 = v.val := h.1
  have h2 : u.val + 1 = t.val := h'.1
  have hv : v = t := Fin.ext (by omega)
  subst t
  rfl

theorem retainedRowIndex_card (P : Model m) (S : CellBasisSelection P)
    (hsmall : ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) :
    Fintype.card (RetainedRowIndex P S) ≤ Fintype.card (Item m) + (q + 1) * 6 ^ q := by
  classical
  have hb := selectionFinset_card P S hsmall
  have he := adjacentEdge_card P
  simp only [RetainedRowIndex, Fintype.card_sum, Fintype.card_coe]
  omega

/-- Bounded finite integer matrix certificate for the nonempty tight-face dimension. -/
theorem small_retained_matrix (P : Model m) (hWF : WellFormed P)
    (hT : (tightPointSet P).Nonempty) :
    ∃ S : CellBasisSelection P,
      Fintype.card (RetainedRowIndex P S) ≤ Fintype.card (Item m) + (q + 1) * 6 ^ q ∧
      ((retainedMatrix P S).map (Int.castRingHom ℚ)).rank =
        Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 := by
  obtain ⟨S, hs⟩ := small_cellBasisSelection_exists P
  exact ⟨S, retainedRowIndex_card P S hs, retained_matrix_rational_rank P hWF S hT⟩

end MOR34
