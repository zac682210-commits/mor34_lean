import MOR34.BoundedMatrixNormals
import MOR34.IntegerNormals

namespace MOR34
variable {q : ℕ}

def augmentedCountRow (z : Counts q) : Option (Fin q) → ℤ
  | none => 1
  | some j => z j

def countMatrix (B : Finset (Counts q)) : Matrix B (Option (Fin q)) ℤ :=
  fun z => augmentedCountRow z.val

theorem augmentedCountRow_cast (z : Counts q) :
    (LinearEquiv.piOptionEquivProd ℚ : (Option (Fin q) → ℚ) ≃ₗ[ℚ] ℚ × (Fin q → ℚ))
      (fun k => (augmentedCountRow z k : ℚ)) = rationalCountPoint z := by
  ext <;> simp [augmentedCountRow, rationalCountPoint,
    LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

theorem countMatrix_span_iff (B : Finset (Counts q)) (z : Counts q) :
    (fun k => (augmentedCountRow z k : ℚ)) ∈
      Submodule.span ℚ (Set.range ((countMatrix B).map (Int.castRingHom ℚ)).row) ↔
    rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B := by
  classical
  let e : (Option (Fin q) → ℚ) ≃ₗ[ℚ] ℚ × (Fin q → ℚ) := LinearEquiv.piOptionEquivProd ℚ
  have hm : (Submodule.span ℚ (Set.range ((countMatrix B).map (Int.castRingHom ℚ)).row)).map
      e.toLinearMap = selectedSpan (K := ℚ) rationalCountPoint B := by
    rw [Submodule.map_span, selectedSpan]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.val, t.property, (augmentedCountRow_cast t.val).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, augmentedCountRow_cast t⟩
  constructor
  · intro hz
    rw [← hm]
    exact ⟨_, hz, augmentedCountRow_cast z⟩
  · intro hz
    rw [← hm] at hz
    obtain ⟨x, hx, he⟩ := hz
    have heq : x = fun k => (augmentedCountRow z k : ℚ) :=
      e.injective (he.trans (augmentedCountRow_cast z).symm)
    rwa [← heq]

def vectorIntegerForm (v : Option (Fin q) → ℤ) : IntegerForm q :=
  ⟨fun j => v (some j), v none⟩

theorem vectorIntegerForm_pairing (v : Option (Fin q) → ℤ) (z : Counts q) :
    ((vectorIntegerForm v).eval z : ℚ) =
      ∑ k, (augmentedCountRow z k : ℚ) * (v k : ℚ) := by
  simp [vectorIntegerForm, IntegerForm.eval, Fintype.sum_option, augmentedCountRow,
    Int.cast_sum, mul_comm]

def normalCoefficientBound (q N : ℕ) : ℤ :=
  2 * ((q + 1).factorial : ℤ) * (N : ℤ) ^ (q + 1)

def FormsBounded (forms : List (IntegerForm q)) (N : ℕ) : Prop :=
  ∀ f ∈ forms, |f.constant| ≤ normalCoefficientBound q N ∧
    ∀ j, |f.coefficient j| ≤ normalCoefficientBound q N

/-- Bounded equations for arbitrary finite count selections; independence is not assumed. -/
theorem bounded_count_forms_exist (B : Finset (Counts q)) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ N) :
    ∃ forms : List (IntegerForm q), FormsDescribe B forms ∧
      forms.length = q + 1 ∧ FormsBounded forms N := by
  classical
  have hM : ∀ (z : B) k, |countMatrix B z k| ≤ (N : ℤ) := by
    intro z k
    cases k with
    | none => simpa [countMatrix, augmentedCountRow] using (show (1 : ℤ) ≤ N by exact_mod_cast hN)
    | some j =>
      have hz : (z.val j : ℤ) ≤ N := by exact_mod_cast hB z.val z.property j
      simpa [countMatrix, augmentedCountRow] using hz
  obtain ⟨v, hv, hb⟩ := bounded_matrix_normals (countMatrix B) N hN hM
  let forms := (Finset.univ.toList : List (Option (Fin q))).map (fun j => vectorIntegerForm (v j))
  refine ⟨forms, ?_, ?_, ?_⟩
  · intro z
    rw [← countMatrix_span_iff, hv]
    constructor
    · intro hz f hf
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      have hh := hz j
      rw [← vectorIntegerForm_pairing] at hh
      exact_mod_cast hh
    · intro hz j
      have hj : vectorIntegerForm (v j) ∈ forms :=
        List.mem_map.mpr ⟨j, by simp, rfl⟩
      rw [← vectorIntegerForm_pairing, hz _ hj]
      simp
  · simp [forms]
  · intro f hf
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
    constructor
    · simpa [vectorIntegerForm, normalCoefficientBound, Nat.add_comm] using hb j none
    · intro k
      simpa [vectorIntegerForm, normalCoefficientBound, Nat.add_comm] using hb j (some k)

end MOR34
