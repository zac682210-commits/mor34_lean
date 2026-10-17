import MOR34.RawTransport
import MOR34.TightDimension

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

def rawPointVector (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else 0

def rawTightPointSet (a c : Fin n → ℤ) (b d : ℤ) : Set (Fin n → ℝ) :=
  {x | ∃ S, RawTight a c b d S ∧ x = rawPointVector S}

def relabelLinear (e : Item m ≃ Fin n) : (Item m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
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
  rw [← he]
  exact LinearEquiv.finrank_map_eq (relabelLinear e) _

end MOR34
