import MOR34.RawOutput

namespace MOR34
variable {n : ℕ}

/-- A normalized model together with its exact relation to the supplied raw input. -/
structure RawNormalization (a c : Fin n → ℤ) (b d : ℤ) where
  classes : ℕ
  sizes : Fin classes → ℕ
  model : Model sizes
  itemEquiv : Item sizes ≃ Fin n
  wellFormed : WellFormed model
  capacity_eq : model.capacity = b
  rhs_eq : model.rhs = d
  weight_eq : ∀ i, model.weight i = a (itemEquiv i)
  coefficient_eq : ∀ i, model.coefficient i.1 = c (itemEquiv i)

theorem rawNormalization_exists (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i) :
    Nonempty (RawNormalization a c b d) := by
  obtain ⟨q, m, P, e, hwf, hcap, hrhs, hw, hcoef⟩ := normalized_model_exists n hn a c b d ha hb hab hc
  exact ⟨⟨q, m, P, e, hwf, hcap, hrhs, hw, hcoef⟩⟩

/-- Classical normalization: no sorting implementation or runtime is asserted. -/
noncomputable def normalizeRaw (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i) :
    RawNormalization a c b d := Classical.choice (rawNormalization_exists hn a c b d ha hb hab hc)

/-- Primitive contracts only: these do not assume any face, dimension or basis conclusion. -/
structure RowPrimitives {q : ℕ} {m : Fin q → ℕ} (P : Model m) where
  solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)
  solve_spec : ParityRowSolverSpec P solve
  edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)
  edge_spec : ForcedRowSolverSpec P edgeSolve
  violate : Option (IntegerRowSolution q)
  violate_spec : ViolationSolverSpec P violate
  ranker : ExactIntegerRank m

noncomputable def RawNormalization.run {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) : RawOutput n :=
  rawPipeline N.model N.wellFormed N.itemEquiv s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.ranker

theorem rawNormalization_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.run s).Correct a c b d := by
  have h := rawPipeline_correct N.model N.wellFormed N.itemEquiv a c N.weight_eq N.coefficient_eq
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.violate_spec s.ranker
  simpa only [N.capacity_eq, N.rhs_eq] using h

theorem rawNormalization_parameter {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) :
    N.classes ≤ ((Finset.univ.image c).filter (fun v => 0 < v)).card + 1 :=
  raw_parameter_bound N.model N.wellFormed N.itemEquiv c N.coefficient_eq

theorem rawNormalization_facet {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) :
    (N.run s).decision.isFacet = true ↔ RawDefinesFacet a c b d :=
  raw_correct_output_facet _ _ _ _ _ (rawNormalization_correct N s).1

theorem rawNormalization_dimension {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (s : RowPrimitives N.model) (hv : RawValid a c b d) :
    (N.run s).decision.dimension = some (rawSignedDimension a c b d) := by
  have hv' : RawValid a c N.model.capacity N.model.rhs := by
    simpa only [N.capacity_eq, N.rhs_eq] using hv
  have h := rawPipeline_dimension N.model N.wellFormed N.itemEquiv a c N.weight_eq N.coefficient_eq hv'
    s.solve s.solve_spec s.edgeSolve s.edge_spec s.violate s.violate_spec s.ranker
  simpa only [N.capacity_eq, N.rhs_eq] using h

/-- Raw data, paper hypotheses, and exact primitive solvers suffice for the output contract.
The primitive type refers to the normalized model, not to the desired final result. -/
theorem original_input_output_contract (hn : 0 < n) (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i)
    (s : RowPrimitives (normalizeRaw hn a c b d ha hb hab hc).model) :
    ((normalizeRaw hn a c b d ha hb hab hc).run s).Correct a c b d :=
  rawNormalization_correct _ s

end MOR34
