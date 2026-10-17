import MOR34.AugmentedDimension
import MOR34.TightDimension
import Mathlib.Analysis.Convex.Hull

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The actual feasible binary points; no convex-hull or facet predicate is introduced here. -/
def feasiblePointSet (P : Model m) : Set (Item m → ℝ) :=
  {x | ∃ S : Finset (Item m), Feasible P S ∧ x = pointVector S}

theorem feasiblePointSet_zero (P : Model m) (hWF : WellFormed P) :
    (0 : Item m → ℝ) ∈ feasiblePointSet P := by
  refine ⟨∅, ?_, ?_⟩
  · simpa [Feasible, weightSum] using le_of_lt hWF.2.2.2.1
  · ext i; simp [pointVector]

theorem feasiblePointSet_unit (P : Model m) (hWF : WellFormed P) (i : Item m) :
    unitVector i ∈ feasiblePointSet P := by
  refine ⟨{i}, ?_, ?_⟩
  · simpa [Feasible, weightSum] using hWF.2.2.2.2.1 i
  · ext k; simp [pointVector, unitVector]

/-- Feasible singletons and the empty set already span all ambient directions. -/
theorem feasiblePointSet_vectorSpan (P : Model m) (hWF : WellFormed P) :
    vectorSpan ℝ (feasiblePointSet P) = ⊤ := by
  apply top_unique
  intro x _
  have hu (i : Item m) : unitVector i ∈ vectorSpan ℝ (feasiblePointSet P) := by
    have hh := vsub_mem_vectorSpan ℝ (feasiblePointSet_unit P hWF i)
      (feasiblePointSet_zero P hWF)
    simpa using hh
  rw [← unitVector_expansion x]
  exact (vectorSpan ℝ (feasiblePointSet P)).sum_mem
    (fun i _ => (vectorSpan ℝ (feasiblePointSet P)).smul_mem (x i) (hu i))

theorem feasiblePointSet_affineSpan (P : Model m) (hWF : WellFormed P) :
    affineSpan ℝ (feasiblePointSet P) = ⊤ := by
  exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
    ℝ (Item m → ℝ) (Item m → ℝ) ⟨0, feasiblePointSet_zero P hWF⟩).mpr
      (feasiblePointSet_vectorSpan P hWF)

theorem feasiblePointSet_finrank (P : Model m) (hWF : WellFormed P) :
    Module.finrank ℝ (vectorSpan ℝ (feasiblePointSet P)) = Fintype.card (Item m) := by
  rw [feasiblePointSet_vectorSpan P hWF, finrank_top]
  simp

/-- The original binary knapsack polytope, as the convex hull of feasible points. -/
def knapsackPolytope (P : Model m) : Set (Item m → ℝ) := convexHull ℝ (feasiblePointSet P)

theorem knapsackPolytope_affineSpan (P : Model m) (hWF : WellFormed P) :
    affineSpan ℝ (knapsackPolytope P) = ⊤ := by
  rw [knapsackPolytope, affineSpan_convexHull, feasiblePointSet_affineSpan P hWF]

theorem knapsackPolytope_finrank (P : Model m) (hWF : WellFormed P) :
    Module.finrank ℝ (vectorSpan ℝ (knapsackPolytope P)) = Fintype.card (Item m) := by
  have hh := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top
    ℝ (Item m → ℝ) (Item m → ℝ) (knapsackPolytope_affineSpan P hWF)
  rw [hh, finrank_top]
  simp

end MOR34
