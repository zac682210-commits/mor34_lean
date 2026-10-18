import MOR34.RawGeometry

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

def rawFeasiblePointSet (a : Fin n → ℤ) (b : ℤ) : Set (Fin n → ℝ) :=
  {x | ∃ S, RawFeasible a b S ∧ x = rawPointVector S}

def rawKnapsackPolytope (a : Fin n → ℤ) (b : ℤ) : Set (Fin n → ℝ) :=
  convexHull ℝ (rawFeasiblePointSet a b)

noncomputable def rawCandidateLinear (c : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (c i : ℝ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.mul_sum, mul_left_comm, mul_assoc]

def rawCandidateFace (a c : Fin n → ℤ) (b d : ℤ) : Set (Fin n → ℝ) :=
  {x ∈ rawKnapsackPolytope a b | rawCandidateLinear c x = (d : ℝ)}

def RawDefinesFacet (a c : Fin n → ℤ) (b d : ℤ) : Prop :=
  RawValid a c b d ∧ IsCodimensionOneFace (rawKnapsackPolytope a b) (rawCandidateFace a c b d)

theorem rawCandidateLinear_point (c : Fin n → ℤ) (S : Finset (Fin n)) :
    rawCandidateLinear c (rawPointVector S) = ((∑ i ∈ S, c i : ℤ) : ℝ) := by
  classical
  simp [rawCandidateLinear, rawPointVector, mul_ite]

theorem raw_valid_linear_bound (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    ∀ x ∈ rawFeasiblePointSet a b, rawCandidateLinear c x ≤ (d : ℝ) := by
  rintro x ⟨S, hS, rfl⟩
  rw [rawCandidateLinear_point]
  exact_mod_cast hv S hS

theorem rawTightPointSet_level (a c : Fin n → ℤ) (b d : ℤ) :
    {x ∈ rawFeasiblePointSet a b | rawCandidateLinear c x = (d : ℝ)} = rawTightPointSet a c b d := by
  ext x
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, he⟩
    refine ⟨S, ⟨hS, ?_⟩, rfl⟩
    rw [rawCandidateLinear_point] at he
    exact_mod_cast he
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS.1, rfl⟩, by rw [rawCandidateLinear_point, hS.2]⟩

theorem rawCandidateFace_eq_hull (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    rawCandidateFace a c b d = convexHull ℝ (rawTightPointSet a c b d) := by
  rw [rawCandidateFace, rawKnapsackPolytope,
    supporting_hull_eq _ _ _ (raw_valid_linear_bound a c b d hv), rawTightPointSet_level]

theorem rawCandidateFace_convex (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    Convex ℝ (rawCandidateFace a c b d) := by
  rw [rawCandidateFace_eq_hull a c b d hv]
  exact convex_convexHull _ _

theorem rawCandidateFace_extreme (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    IsExtreme ℝ (rawKnapsackPolytope a b) (rawCandidateFace a c b d) :=
  supporting_level_extreme _ _ _ (linear_bound_convexHull _ _ _ (raw_valid_linear_bound a c b d hv))

theorem rawCandidateFace_nonempty (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    (rawCandidateFace a c b d).Nonempty ↔ (rawTightPointSet a c b d).Nonempty := by
  rw [rawCandidateFace_eq_hull a c b d hv, convexHull_nonempty_iff]

theorem rawCandidateFace_vectorSpan (a c : Fin n → ℤ) (b d : ℤ) (hv : RawValid a c b d) :
    vectorSpan ℝ (rawCandidateFace a c b d) = vectorSpan ℝ (rawTightPointSet a c b d) := by
  have hh : affineSpan ℝ (rawCandidateFace a c b d) = affineSpan ℝ (rawTightPointSet a c b d) := by
    rw [rawCandidateFace_eq_hull a c b d hv, affineSpan_convexHull]
  simpa only [direction_affineSpan] using congrArg AffineSubspace.direction hh

theorem relabel_feasiblePointSet (P : Model m) (e : Item m ≃ Fin n) (a : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) :
    rawFeasiblePointSet a P.capacity = relabelLinear e '' feasiblePointSet P := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, rfl⟩
    let T := S.map e.symm.toEmbedding
    have he : T.map e.toEmbedding = S := by ext i; simp [T]
    have ht : Feasible P T := (relabel_feasible P e a ha T).mpr (he.symm ▸ hS)
    refine ⟨pointVector T, ⟨T, ht, rfl⟩, ?_⟩
    rw [relabel_pointVector, he]
  · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S.map e.toEmbedding, (relabel_feasible P e a ha S).mp hS, relabel_pointVector e S⟩

theorem relabel_knapsackPolytope (P : Model m) (e : Item m ≃ Fin n) (a : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) :
    rawKnapsackPolytope a P.capacity = relabelLinear e '' knapsackPolytope P := by
  rw [rawKnapsackPolytope, relabel_feasiblePointSet P e a ha, knapsackPolytope]
  exact ((relabelLinear e).toLinearMap.image_convexHull _).symm

theorem relabel_candidateFace (P : Model m) (hv : Valid P) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    rawCandidateFace a c P.capacity P.rhs = relabelLinear e '' candidateFace P := by
  rw [rawCandidateFace_eq_hull _ _ _ _ ((relabel_valid P e a c ha hc).mp hv),
    relabel_tightPointSet P e a c ha hc, candidateFace_eq_hull P hv]
  exact ((relabelLinear e).toLinearMap.image_convexHull _).symm

theorem relabel_polytope_finrank (P : Model m) (e : Item m ≃ Fin n) (a : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) :
    Module.finrank ℝ (vectorSpan ℝ (rawKnapsackPolytope a P.capacity)) =
      Module.finrank ℝ (vectorSpan ℝ (knapsackPolytope P)) := by
  rw [relabel_knapsackPolytope P e a ha]
  have he := (relabelLinear e).toAffineEquiv.toAffineMap.vectorSpan_image_eq_submodule_map
    (s := knapsackPolytope P)
  simp only [AffineEquiv.coe_toAffineMap, LinearEquiv.coe_toAffineEquiv] at he
  rw [← he]
  exact LinearEquiv.finrank_map_eq (relabelLinear e) _

theorem relabel_face_finrank (P : Model m) (hv : Valid P) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    Module.finrank ℝ (vectorSpan ℝ (rawCandidateFace a c P.capacity P.rhs)) =
      Module.finrank ℝ (vectorSpan ℝ (candidateFace P)) := by
  rw [rawCandidateFace_vectorSpan _ _ _ _ ((relabel_valid P e a c ha hc).mp hv),
    candidateFace_vectorSpan P hv, relabel_tight_finrank P e a c ha hc]

theorem relabel_geometric_facet (P : Model m) (hv : Valid P) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    IsCodimensionOneFace (rawKnapsackPolytope a P.capacity) (rawCandidateFace a c P.capacity P.rhs) ↔
      IsCodimensionOneFace (knapsackPolytope P) (candidateFace P) := by
  have hr := (relabel_valid P e a c ha hc).mp hv
  have hn : (rawCandidateFace a c P.capacity P.rhs).Nonempty ↔ (candidateFace P).Nonempty := by
    rw [relabel_candidateFace P hv e a c ha hc, Set.image_nonempty]
  simp only [IsCodimensionOneFace, hn, relabel_face_finrank P hv e a c ha hc,
    relabel_polytope_finrank P e a ha, rawCandidateFace_convex _ _ _ _ hr,
    rawCandidateFace_extreme _ _ _ _ hr, candidateFace_convex P hv, candidateFace_extreme P hv,
    true_and]

theorem relabel_definesFacet (P : Model m) (e : Item m ≃ Fin n) (a c : Fin n → ℤ)
    (ha : ∀ i, P.weight i = a (e i)) (hc : ∀ i, P.coefficient i.1 = c (e i)) :
    RawDefinesFacet a c P.capacity P.rhs ↔ DefinesFacet P := by
  constructor
  · rintro ⟨hv, hf⟩
    have h := (relabel_valid P e a c ha hc).mpr hv
    exact ⟨h, (relabel_geometric_facet P h e a c ha hc).mp hf⟩
  · rintro ⟨hv, hf⟩
    exact ⟨(relabel_valid P e a c ha hc).mp hv,
      (relabel_geometric_facet P hv e a c ha hc).mpr hf⟩

end MOR34
