import MOR34.RawTransport
import MOR34.TightDimension
import MOR34.SignedDimension
import MOR34.BoundedNormalizedPipeline

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

def rawPointVector (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else 0

def rawTightPointSet (a c : Fin n → ℤ) (b d : ℤ) : Set (Fin n → ℝ) :=
  {x | ∃ S, RawTight a c b d S ∧ x = rawPointVector S}

noncomputable def relabelLinear (e : Item m ≃ Fin n) : (Item m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x (e.symm i)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relabel_pointVector (e : Item m ≃ Fin n) (S : Finset (Item m)) :
    relabelLinear e (pointVector S) = rawPointVector (S.map e.toEmbedding) := by
  classical
  funext i
  simp [relabelLinear, pointVector, rawPointVector]

theorem relabel_tightPointSet (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    rawTightPointSet a c P.capacity P.rhs = relabelLinear e '' tightPointSet P := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, rfl⟩
    let T := S.map e.symm.toEmbedding
    have he : T.map e.toEmbedding = S := by ext i; simp [T]
    have ht : Tight P T := (relabel_tight P e a c ha hc T).mpr (he.symm ▸ hS)
    refine ⟨pointVector T, ⟨T, ht, rfl⟩, ?_⟩
    rw [relabel_pointVector, he]
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S.map e.toEmbedding, (relabel_tight P e a c ha hc S).mp hS,
      relabel_pointVector e S⟩

/-- Affine directions, hence nonempty affine dimensions, are invariant under normalization. -/
theorem relabel_tight_finrank (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    Module.finrank ℝ (vectorSpan ℝ (rawTightPointSet a c P.capacity P.rhs)) =
      Module.finrank ℝ (vectorSpan ℝ (tightPointSet P)) := by
  rw [relabel_tightPointSet P e a c ha hc]
  have he := (relabelLinear e).toAffineEquiv.toAffineMap.vectorSpan_image_eq_submodule_map
    (s := tightPointSet P)
  simp only [AffineEquiv.coe_toAffineMap, LinearEquiv.coe_toAffineEquiv] at he
  rw [← he]
  exact LinearEquiv.finrank_map_eq (relabelLinear e) _

noncomputable def rawSignedDimension (a c : Fin n → ℤ) (b d : ℤ) : ℤ := by
  classical
  exact if (rawTightPointSet a c b d).Nonempty then
    (Module.finrank ℝ (vectorSpan ℝ (rawTightPointSet a c b d)) : ℤ) else -1

theorem relabel_tight_nonempty (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    (rawTightPointSet a c P.capacity P.rhs).Nonempty ↔ (tightPointSet P).Nonempty := by
  rw [relabel_tightPointSet P e a c ha hc, Set.image_nonempty]

/-- Empty faces retain dimension -1 after returning to the original item coordinates. -/
theorem relabel_signed_dimension (P : Model m) (hv : Valid P)
    (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    rawSignedDimension a c P.capacity P.rhs = candidateFaceDimension P := by
  classical
  have hn := candidateFace_nonempty_iff P hv
  have hr := relabel_tight_nonempty P e a c ha hc
  by_cases ht : (tightPointSet P).Nonempty
  · have hf := hn.mpr ht
    have hg := hr.mpr ht
    simp only [rawSignedDimension, candidateFaceDimension, if_pos hf, if_pos hg]
    rw [relabel_tight_finrank P e a c ha hc, candidateFace_vectorSpan P hv]
  · have hf : ¬ (candidateFace P).Nonempty := fun h => ht (hn.mp h)
    have hg : ¬ (rawTightPointSet a c P.capacity P.rhs).Nonempty := fun h => ht (hr.mp h)
    simp only [rawSignedDimension, candidateFaceDimension, if_neg hf, if_neg hg]

/-- The computed signed dimension is now expressed using original binary tight points. -/
theorem boundedPipeline_raw_dimension (P : Model m) (hWF : WellFormed P) (hv : Valid P)
    (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve)
    (violate : Option (IntegerRowSolution q)) (hviol : ViolationSolverSpec P violate)
    (ranker : ExactIntegerRank m) :
    (boundedPipeline P hWF solve hs edgeSolve he violate ranker).decision.dimension =
      some (rawSignedDimension a c P.capacity P.rhs) := by
  rw [relabel_signed_dimension P hv e a c ha hc]
  exact boundedPipeline_dimension P hWF hv solve hs edgeSolve he violate hviol ranker

end MOR34
