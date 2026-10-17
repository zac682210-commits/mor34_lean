import MOR34.GroupedSorting

namespace MOR34

/-- Every raw instance under the paper's positivity hypotheses admits the normalized
model through an item bijection. This theorem asserts no preprocessing runtime. -/
theorem normalized_model_exists (n : ℕ) (hn : 0 < n)
    (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b)
    (hc : ∀ i, 0 ≤ c i) :
    ∃ q : ℕ, ∃ m : Fin q → ℕ, ∃ P : Model m, ∃ e : Item m ≃ Fin n,
      WellFormed P ∧ P.capacity = b ∧ P.rhs = d ∧
      (∀ i, P.weight i = a (e i)) ∧ (∀ i, P.coefficient i.1 = c (e i)) := by
  classical
  let C := Finset.univ.image c
  let q := Fintype.card C
  let ce : Fin q ≃ C := (Fintype.equivFin C).symm
  let fiber := fun j : C => {i : Fin n // c i = j.val}
  let m := fun j : Fin q => Fintype.card (fiber (ce j))
  let fe := fun j : Fin q => (Fintype.equivFin (fiber (ce j))).symm
  let e : Item m ≃ Fin n := (Equiv.sigmaCongr ce fe).trans
    (Equiv.sigmaSubtypeFiberEquiv c (fun v => v ∈ C)
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hec (i : Item m) : c (e i) = (ce i.1).val := (fe i.1 i.2).property
  let P : Model m := ⟨fun i => a (e i), fun j => (ce j).val, b, d⟩
  have hq : 0 < q := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨c ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩⟩
  have hm (j : Fin q) : 0 < m j := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ce j).property
    exact ⟨⟨i, hi⟩⟩
  have hcoef (j : Fin q) : 0 ≤ (ce j).val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ce j).property
    rw [← hi]
    exact hc i
  have hi : Function.Injective (fun j : Fin q => (ce j).val) :=
    Subtype.val_injective.comp ce.injective
  have hP : GroupedConditions P :=
    ⟨hq, hm, fun i => ha (e i), hb, fun i => hab (e i), hcoef, hi⟩
  refine ⟨q, m, sortGrouped P, (sortItems P).trans e,
    sortGrouped_wellFormed P hP, rfl, rfl, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    exact (hec (sortItems P i)).symm

end MOR34
