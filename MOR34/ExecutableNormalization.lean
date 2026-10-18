import MOR34.ExecutableRawPipeline

namespace MOR34
variable {n : ℕ}

/-- Enumerate integer coefficient values and their item fibers by their natural orders,
then sort each fiber by weight. All data are computed; hypotheses are used only in proofs. -/
def normalizeRawExecutable (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b)
    (hc : ∀ i, 0 ≤ c i) : RawNormalization a c b d := by
  let C := Finset.univ.image c
  let q := C.card
  let ce : Fin q ≃ C := (Finset.orderIsoOfFin C rfl).toEquiv
  let fiber := fun j : C => {i : Fin n // c i = j.val}
  let fiberSet := fun j : C => Finset.univ.filter (fun i : Fin n => c i = j.val)
  let m := fun j : Fin q => (fiberSet (ce j)).card
  let fse : (j : C) → (fiberSet j) ≃ fiber j := fun j => {
    toFun := fun i => ⟨i.val, (Finset.mem_filter.mp i.property).2⟩
    invFun := fun i => ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property⟩⟩
    left_inv := fun i => rfl
    right_inv := fun i => rfl
  }
  let fe := fun j : Fin q => ((fiberSet (ce j)).orderIsoOfFin rfl).toEquiv.trans (fse (ce j))
  let e : Item m ≃ Fin n := (Equiv.sigmaCongr ce fe).trans
    (Equiv.sigmaSubtypeFiberEquiv c (fun v => v ∈ C)
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hec (i : Item m) : c (e i) = (ce i.1).val := (fe i.1 i.2).property
  let P : Model m := ⟨fun i => a (e i), fun j => (ce j).val, b, d⟩
  have hq : 0 < q := by
    apply Finset.card_pos.mpr
    exact ⟨c ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  have hm (j : Fin q) : 0 < m j := by
    apply Finset.card_pos.mpr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ce j).property
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
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

/-- End-to-end output correctness from raw integer data with the computed normalization. -/
theorem executable_original_input_output_contract (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (s : RowPrimitives (normalizeRawExecutable hn a c b d ha hb hab hc).model) :
    ((normalizeRawExecutable hn a c b d ha hb hab hc).runExecutable s).Correct a c b d :=
  executableRawPipeline_correct _ s

theorem executable_normalization_parameter (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i) :
    (normalizeRawExecutable hn a c b d ha hb hab hc).classes ≤
      ((Finset.univ.image c).filter (fun v => 0 < v)).card + 1 :=
  rawNormalization_parameter _

end MOR34
