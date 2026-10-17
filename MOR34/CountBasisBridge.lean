import MOR34.IntegerNormals
import MOR34.AugmentedDimension

namespace MOR34

/-- The first coordinate recovers the affine constraint on a linear combination. -/
theorem affineSpan_of_augment_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {T : Set V} {x : V} (hx : pointAugment x ∈ augmentedSpan T) : x ∈ affineSpan ℝ T := by
  by_cases hT : T.Nonempty
  · obtain ⟨a, ha⟩ := hT
    rw [augmentedSpan_anchor ha] at hx
    obtain ⟨u, hu, v, hv, he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d, hd, hde⟩ := hv
    have hc1 : c = 1 := by
      have hh := congrArg Prod.fst he
      rw [← hc, ← hde] at hh
      simpa [pointAugment, zeroAugment] using hh
    have hdx : d + a = x := by
      have hh := congrArg Prod.snd he
      rw [← hc, ← hde, hc1] at hh
      simpa [pointAugment, zeroAugment, add_comm] using hh
    have hh := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan (mem_affineSpan ℝ ha) hd
    simpa only [vadd_eq_add, hdx] using hh
  · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    rw [he] at hx
    have hz : pointAugment x = 0 := by simpa [augmentedSpan] using hx
    have h1 := congrArg Prod.fst hz
    simp [pointAugment] at h1

def rationalAugmentCast {q : ℕ} (x : ℚ × (Fin q → ℚ)) : ℝ × (Fin q → ℝ) :=
  (x.1, fun j => (x.2 j : ℝ))

theorem rational_selectedSpan_to_real {q : ℕ} (B : Finset (Counts q))
    {x : ℚ × (Fin q → ℚ)} (hx : x ∈ selectedSpan (K := ℚ) rationalCountPoint B) :
    rationalAugmentCast x ∈ augmentedSpan (countReal '' (B : Set (Counts q))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have hh : rationalAugmentCast (rationalCountPoint z) = pointAugment (countReal z) := by
      ext <;> simp [rationalAugmentCast, rationalCountPoint, pointAugment, countReal]
    rw [hh]
    exact Submodule.subset_span ⟨countReal z, ⟨z, hz, rfl⟩, rfl⟩
  | zero =>
    have he : rationalAugmentCast (0 : ℚ × (Fin q → ℚ)) = 0 := by
      ext <;> simp [rationalAugmentCast]
    rw [he]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have he : rationalAugmentCast (x + y) = rationalAugmentCast x + rationalAugmentCast y := by
      ext <;> simp [rationalAugmentCast]
    rw [he]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    have he : rationalAugmentCast (c • x) = (c : ℝ) • rationalAugmentCast x := by
      ext <;> simp [rationalAugmentCast, smul_eq_mul]
    rw [he]
    exact Submodule.smul_mem _ _ ih

theorem countReal_affineSpan_of_rational_span {q : ℕ} (B : Finset (Counts q)) (z : Counts q)
    (hz : rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B) :
    countReal z ∈ affineSpan ℝ (countReal '' (B : Set (Counts q))) := by
  apply affineSpan_of_augment_mem
  have hh := rational_selectedSpan_to_real B hz
  convert hh using 1 <;>
    ext <;> simp [rationalAugmentCast, rationalCountPoint, pointAugment, countReal]

/-- The query-bounded count procedure supplies the real affine-spanning contract used by the cells. -/
theorem real_count_basis_from_linear_oracle {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve) :
    ∃ forms : Finset (Counts q) → List (IntegerForm q),
    let B := basisSearch (linearSpanOracle solve forms) (q + 1) ∅
    (B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      (∀ z ∈ C, countReal z ∈ affineSpan ℝ (countReal '' (B : Set (Counts q)))) ∧
      linearBasisCalls solve forms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  obtain ⟨forms, hb, hsize, hspan, hcalls⟩ := count_basis_from_linear_oracle C solve hs
  refine ⟨forms, hb, hsize, ?_, hcalls⟩
  intro z hz
  exact countReal_affineSpan_of_rational_span _ z (hspan z hz)

end MOR34
