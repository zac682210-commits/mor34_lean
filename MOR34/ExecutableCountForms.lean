import MOR34.ExecutableMatrixNormals
import MOR34.OrderedCounts

namespace MOR34
variable {q : ℕ}

def finVectorIntegerForm (v : Fin (q+1) → ℤ) : IntegerForm q :=
  ⟨fun j => v j.succ, v 0⟩

theorem finVectorIntegerForm_pairing (v : Fin (q+1) → ℤ) (z : Counts q) :
    ((finVectorIntegerForm v).eval z : ℚ) =
      ∑ k, (finAugmentedCount z k : ℚ) * (v k : ℚ) := by
  simp [finVectorIntegerForm, IntegerForm.eval, Fin.sum_univ_succ, finAugmentedCount,
    Int.cast_sum, mul_comm]

/-- No choice in the generated data: sorted counts, finite candidate search, finite determinants. -/
def computedCountForms (B : Finset (Counts q)) : List (IntegerForm q) :=
  List.ofFn (fun j : Fin (q+1) => finVectorIntegerForm (computedMatrixNormals (orderedCountMatrix B) j))

theorem computedCountForms_spec (B : Finset (Counts q)) : FormsDescribe B (computedCountForms B) := by
  intro z
  rw [← orderedCountMatrix_span, (computedMatrixNormals_spec (orderedCountMatrix B)).1]
  constructor
  · intro hz f hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    have hh := hz j
    rw [← finVectorIntegerForm_pairing] at hh
    exact_mod_cast hh
  · intro hz j
    have hj : finVectorIntegerForm (computedMatrixNormals (orderedCountMatrix B) j) ∈ computedCountForms B :=
      List.mem_ofFn.mpr ⟨j, rfl⟩
    rw [← finVectorIntegerForm_pairing, hz _ hj]
    simp

theorem computedCountForms_length (B : Finset (Counts q)) : (computedCountForms B).length = q+1 := by
  simp [computedCountForms]

theorem computedCountForms_bound (B : Finset (Counts q)) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ N) : FormsBounded (computedCountForms B) N := by
  have hM : ∀ i j, |orderedCountMatrix B i j| ≤ (N : ℤ) := by
    intro i j
    have hi : (orderedCounts B).get i ∈ B := (orderedCounts_mem B _).mp (List.get_mem _ _)
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [orderedCountMatrix, finAugmentedCount] using (show (1 : ℤ) ≤ N by exact_mod_cast hN)
    · have hh : (((orderedCounts B).get i k : ℕ) : ℤ) ≤ N := by exact_mod_cast hB _ hi k
      simpa [orderedCountMatrix, finAugmentedCount] using hh
  have hb := (computedMatrixNormals_spec (orderedCountMatrix B)).2 N hN hM
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact ⟨hb j 0, fun k => hb j k.succ⟩

end MOR34
