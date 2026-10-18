import MOR34.RawFacet

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

def relabelBasis (e : Item m ≃ Fin n) (B : Finset (Finset (Item m))) : Finset (Finset (Fin n)) :=
  B.map e.finsetCongr.toEmbedding

theorem relabelBasis_card (e : Item m ≃ Fin n) (B : Finset (Finset (Item m))) :
    (relabelBasis e B).card = B.card := Finset.card_map _

def relabelBasisEquiv (e : Item m ≃ Fin n) (B : Finset (Finset (Item m))) : B ≃ relabelBasis e B where
  toFun S := ⟨e.finsetCongr S.val, Finset.mem_map.mpr ⟨S.val, S.property, rfl⟩⟩
  invFun T := ⟨e.finsetCongr.symm T.val, Finset.mem_map_equiv.mp T.property⟩
  left_inv S := by apply Subtype.ext; exact e.finsetCongr.symm_apply_apply S.val
  right_inv T := by apply Subtype.ext; exact e.finsetCongr.apply_symm_apply T.val

theorem relabelBasis_points (e : Item m ≃ Fin n) (B : Finset (Finset (Item m))) :
    rawPointVector '' (relabelBasis e B : Set (Finset (Fin n))) =
      relabelLinear e '' (pointVector '' (B : Set (Finset (Item m)))) := by
  classical
  ext x
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    exact ⟨pointVector S, ⟨S, hS, rfl⟩, relabel_pointVector e S⟩
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S.map e.toEmbedding, Finset.mem_map.mpr ⟨S, hS, rfl⟩,
      (relabel_pointVector e S).symm⟩

theorem relabelBasis_independent (e : Item m ≃ Fin n) (B : Finset (Finset (Item m)))
    (hB : AffineIndependent ℝ (fun S : B => pointVector S.val)) :
    AffineIndependent ℝ (fun T : relabelBasis e B => rawPointVector T.val) := by
  have hh := hB.map' (relabelLinear e).toAffineEquiv.toAffineMap (relabelLinear e).injective
  apply (affineIndependent_equiv (k := ℝ) (relabelBasisEquiv e B)).mp
  convert hh using 1
  funext S
  exact (relabel_pointVector e S.val).symm

theorem relabelBasis_tight (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (B : Finset (Finset (Item m))) (hB : ∀ S ∈ B, Tight P S) :
    ∀ T ∈ relabelBasis e B, RawTight a c P.capacity P.rhs T := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
  exact (relabel_tight P e a c ha hc S).mp (hB S hS)

theorem relabelBasis_affineSpan (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i))
    (B : Finset (Finset (Item m)))
    (hB : affineSpan ℝ (pointVector '' (B : Set (Finset (Item m)))) = affineSpan ℝ (tightPointSet P)) :
    affineSpan ℝ (rawPointVector '' (relabelBasis e B : Set (Finset (Fin n)))) =
      affineSpan ℝ (rawTightPointSet a c P.capacity P.rhs) := by
  rw [relabelBasis_points, relabel_tightPointSet P e a c ha hc]
  have hh := congrArg (fun A : AffineSubspace ℝ (Item m → ℝ) =>
    A.map (relabelLinear e).toAffineEquiv.toAffineMap) hB
  simpa only [AffineSubspace.map_span, AffineEquiv.coe_toAffineMap,
    LinearEquiv.coe_toAffineEquiv] using hh

end MOR34
