import MOR34.SupportingHull
import MOR34.FeasibleDimension
import MOR34.ComputedMatrix

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

noncomputable def candidateLinear (P : Model m) : (Item m → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (P.coefficient i.1 : ℝ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm, mul_assoc]

theorem candidateLinear_point (P : Model m) (t : Finset (Item m)) :
    candidateLinear P (pointVector t) = (candidateValue P t : ℝ) := by
  classical
  simp [candidateLinear, pointVector, candidateValue, mul_ite]

/-- Equality level in the actual convex hull, rather than just its binary generators. -/
def candidateFace (P : Model m) : Set (Item m → ℝ) :=
  {x ∈ knapsackPolytope P | candidateLinear P x = (P.rhs : ℝ)}

theorem valid_linear_bound (P : Model m) (hv : Valid P) :
    ∀ x ∈ feasiblePointSet P, candidateLinear P x ≤ (P.rhs : ℝ) := by
  rintro x ⟨t, ht, rfl⟩
  rw [candidateLinear_point]
  exact_mod_cast hv t ht

theorem valid_polytope_bound (P : Model m) (hv : Valid P) :
    ∀ x ∈ knapsackPolytope P, candidateLinear P x ≤ (P.rhs : ℝ) :=
  linear_bound_convexHull _ _ _ (valid_linear_bound P hv)

theorem tightPointSet_level (P : Model m) :
    {x ∈ feasiblePointSet P | candidateLinear P x = (P.rhs : ℝ)} = tightPointSet P := by
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, he⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    rw [candidateLinear_point] at he
    exact_mod_cast he
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht.1, rfl⟩, by rw [candidateLinear_point, ht.2]⟩

theorem candidateFace_eq_hull (P : Model m) (hv : Valid P) :
    candidateFace P = convexHull ℝ (tightPointSet P) := by
  rw [candidateFace, knapsackPolytope,
    supporting_hull_eq _ _ _ (valid_linear_bound P hv), tightPointSet_level]

theorem candidateFace_convex (P : Model m) (hv : Valid P) : Convex ℝ (candidateFace P) := by
  rw [candidateFace_eq_hull P hv]
  exact convex_convexHull _ _

theorem candidateFace_extreme (P : Model m) (hv : Valid P) :
    IsExtreme ℝ (knapsackPolytope P) (candidateFace P) :=
  supporting_level_extreme _ _ _ (valid_polytope_bound P hv)

theorem candidateFace_nonempty_iff (P : Model m) (hv : Valid P) :
    (candidateFace P).Nonempty ↔ (tightPointSet P).Nonempty := by
  rw [candidateFace_eq_hull P hv, convexHull_nonempty_iff]

theorem candidateFace_affineSpan (P : Model m) (hv : Valid P) :
    affineSpan ℝ (candidateFace P) = affineSpan ℝ (tightPointSet P) := by
  rw [candidateFace_eq_hull P hv, affineSpan_convexHull]

theorem candidateFace_vectorSpan (P : Model m) (hv : Valid P) :
    vectorSpan ℝ (candidateFace P) = vectorSpan ℝ (tightPointSet P) := by
  simpa only [direction_affineSpan] using congrArg AffineSubspace.direction
    (candidateFace_affineSpan P hv)

/-- Facet convention: nonempty convex extreme subset of affine codimension one.
The ambient set in applications is the full-dimensional knapsack polytope. -/
def IsCodimensionOneFace {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A F : Set V) : Prop :=
  F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ A F ∧
    Module.finrank ℝ (vectorSpan ℝ F) + 1 = Module.finrank ℝ (vectorSpan ℝ A)

theorem candidate_facet_iff_dimension (P : Model m) (hWF : WellFormed P) (hv : Valid P) :
    IsCodimensionOneFace (knapsackPolytope P) (candidateFace P) ↔
      (tightPointSet P).Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) + 1 = Fintype.card (Item m) := by
  rw [IsCodimensionOneFace, candidateFace_nonempty_iff P hv,
    candidateFace_vectorSpan P hv, knapsackPolytope_finrank P hWF]
  constructor
  · intro h; exact ⟨h.1, h.2.2.2⟩
  · intro h
    exact ⟨h.1, candidateFace_convex P hv, candidateFace_extreme P hv, h.2⟩

/-- The geometric face is a facet exactly at the computed rational rank n.
Empty equality levels are separately excluded. -/
theorem candidate_facet_iff_computed_rank (P : Model m) (hWF : WellFormed P)
    (hv : Valid P) (S : CellBasisSelection P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (hT : (tightPointSet P).Nonempty) :
    IsCodimensionOneFace (knapsackPolytope P) (candidateFace P) ↔
      ((computedMatrix P S solve).map (Int.castRingHom ℚ)).rank = Fintype.card (Item m) := by
  rw [candidate_facet_iff_dimension P hWF hv, computed_matrix_rank P hWF S solve hs hT]
  exact and_iff_right hT
end MOR34
