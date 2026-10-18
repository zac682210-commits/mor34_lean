import MOR34.WeightedRequestPolynomial

namespace MOR34

theorem chargedMap_cost_additive {α β γ : Type*} (f : α → β × ℕ) (g : α → γ × ℕ)
    (L : List α) (W : ℕ) (h : ∀ x ∈ L, (f x).2 ≤ (g x).2+W) :
    (chargedMap f L).2 ≤ (chargedMap g L).2+L.length*W := by
  induction L with
  | nil => simp [chargedMap]
  | cons x L ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [chargedMap,List.length_cons]
    nlinarith

variable {q : ℕ} {m : Fin q → ℕ}

theorem weightedRetainedRow_cost_additive (A : IntegerArithmeticCharge)
    (row : ConstructedIntegerRow q × ℕ) (W : ℕ)
    (h : (weightedEvaluateRow A row.1).2 ≤ W) :
    (weightedCompileRetainedRow A row).2 ≤ (compileRetainedRow row).2+W := by
  simp only [weightedCompileRetainedRow,compileRetainedRow]
  omega

/-- The extra bit cost is charged to the rows actually enumerated by the
violation request. Its index construction and original reads are retained. -/
theorem weightedViolationRequest_cost (A : IntegerArithmeticCharge) (P : Model m)
    (R W : ℕ) (h : ∀ k, (weightedEvaluateRow A (violationRowConstruction P k)).2 ≤ W) :
    (weightedCompiledViolationRequest A P R).2 ≤
      (compiledViolationRequest P R).2+(Fintype.card (Item m)+2*q+2)*W := by
  have hh := chargedMap_cost_additive
    (fun k => weightedCompileRetainedRow A (builtViolationRow P R k))
    (fun k => compileRetainedRow (builtViolationRow P R k)) (violationRowIndexList m) W
    (fun k _ => weightedRetainedRow_cost_additive A _ W (by rw [builtViolationRow_value]; exact h k))
  rw [violationRowIndexList_length] at hh
  dsimp only [weightedCompiledViolationRequest,compiledViolationRequest]
  omega

/-- The forced request keeps the same one-time residual table. Only evaluation
of its retained rows is repriced, so no repeated residual construction is hidden. -/
theorem weightedForcedRequest_cost (A : IntegerArithmeticCharge) (P : Model m)
    (j : Fin q) (u v : Fin (m j)) (R W : ℕ)
    (h : ∀ k, (weightedEvaluateRow A (forcedRowConstruction P j u v k)).2 ≤ W) :
    (weightedCompiledForcedRequest A P j u v R).2 ≤
      (compiledForcedRequest P j u v R).2+(forcedRowIndexList j u v).length*W := by
  have hh := chargedMap_cost_additive
    (fun k => weightedCompileRetainedRow A (retainedForcedRow P j u v
      (chargedResidualWeights P j u v R).1 (P.weight ⟨j,v⟩,R) R k))
    (fun k => compileRetainedRow (retainedForcedRow P j u v
      (chargedResidualWeights P j u v R).1 (P.weight ⟨j,v⟩,R) R k)) (forcedRowIndexList j u v) W
    (fun k _ => weightedRetainedRow_cost_additive A _ W (by
      rw [retainedForcedRow_value P j u v _ _ R rfl rfl]; exact h k))
  dsimp only [weightedCompiledForcedRequest,compiledForcedRequest,retainedForcedSystem]
  omega

theorem weightedRemainingRequests_polynomial (P : Model m) (hWF : WellFormed P)
    (R M L H a : ℕ) (hR : R ≤ Fintype.card (Item m)+1)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (hc : ∀ i, (P.coefficient i).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (170*(Fintype.card (Item m)+L+2)^3)
      (H*(170*(Fintype.card (Item m)+L+2)^3)^a)) :
    (weightedCompiledViolationRequest A P R).2 ≤
      2048*(Fintype.card (Item m)+1)^4+
      (Fintype.card (Item m)+2*q+2)*(12*H*170^a+5)*(Fintype.card (Item m)+L+2)^(3*a+1) ∧
    ∀ j u v, (weightedCompiledForcedRequest A P j u v R).2 ≤
      521*(Fintype.card (Item m)+1)^3+
      (forcedRowIndexList j u v).length*(12*H*170^a+5)*(Fintype.card (Item m)+L+2)^(3*a+1) := by
  have hq := coefficient_classes_le_items P hWF
  have hm := fun j => class_size_le_items (m := m) j
  constructor
  · have hh := weightedViolationRequest_cost A P R _ (fun k =>
      weightedViolationRow_polynomial P _ L M H a hq hm hM hML hw hc hr hcap A hA k)
    have hb := compiledViolationRequest_cost P hWF R (by nlinarith)
    exact hh.trans (by nlinarith only [hb])
  · intro j u v
    have hh := weightedForcedRequest_cost A P j u v R _ (fun k =>
      weightedForcedRow_polynomial P j u v _ L M H a hq hm hM hML hw hc hr hcap A hA k)
    have hb := compiledForcedRequest_cost P hWF j u v R hR
    exact hh.trans (by nlinarith only [hb])

end MOR34
