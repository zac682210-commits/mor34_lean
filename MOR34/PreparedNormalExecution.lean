import MOR34.WeightedCellUniform
import MOR34.NormalBitCost

namespace MOR34
variable {q : ℕ}

/-- Standard sorting and dense-matrix emission, on the small retained count
set. Its output is the precise matrix consumed by the normal search. -/
structure CountMatrixPreparation (q : ℕ) where
  emit : (B : Finset (Counts q)) →
    Matrix (Fin (orderedCounts B).length) (Fin (q+1)) ℤ × ℕ
  value : ∀ B, (emit B).1 = orderedCountMatrix B

/-- Uniform local instruction price for the actual early-stopping normal
trace. This is a reference charge, with integer arithmetic and bounded table
access supplied by standard local algorithms, not a backend runtime claim. -/
def preparedCountForms (prep : CountMatrixPreparation q) (unit : ℕ)
    (B : Finset (Counts q)) : List (IntegerForm q) × ℕ :=
  let matrix := prep.emit B
  let out := matrixNormalSearchBuilt matrix.1
  let normals := out.1.get (by
    rw [matrixNormalSearchBuilt_value,prep.value]
    exact matrixNormalSearch_isSome _)
  (List.ofFn (fun j : Fin (q+1) => finVectorIntegerForm (normals j)),
    matrix.2+out.2*unit+((q+1)*(q+2)+1)*unit)

theorem preparedCountForms_value (prep : CountMatrixPreparation q) (unit : ℕ)
    (B : Finset (Counts q)) : (preparedCountForms prep unit B).1 = computedCountForms B := by
  have hg (x y : Option (Fin (q+1) → Fin (q+1) → ℤ))
      (hx : x.isSome) (hy : y.isSome) (h : x = y) : x.get hx = y.get hy := by
    cases h
    rfl
  have he : (matrixNormalSearchBuilt (prep.emit B).1).1 = matrixNormalSearch (orderedCountMatrix B) := by
    rw [prep.value,matrixNormalSearchBuilt_value]
  have hx : (matrixNormalSearchBuilt (prep.emit B).1).1.isSome := by
    rw [he]
    exact matrixNormalSearch_isSome _
  exact congrArg (fun v => List.ofFn (fun j : Fin (q+1) => finVectorIntegerForm (v j)))
    (hg _ _ hx (matrixNormalSearch_isSome _) he)

theorem preparedCountForms_cost (prep : CountMatrixPreparation q) (unit E : ℕ)
    (B : Finset (Counts q)) (hB : B.card ≤ q+1) (he : (prep.emit B).2 ≤ E) :
    (preparedCountForms prep unit B).2 ≤ E+builtCountFormBudget q*unit := by
  have hh := builtCountForms_cost B hB
  have hm := Nat.mul_le_mul_right unit hh
  dsimp only [builtCountForms] at hm
  dsimp only [preparedCountForms]
  rw [prep.value]
  nlinarith only [he,hm]

theorem orderedCountMatrix_bound (B : Finset (Counts q)) (n : ℕ)
    (hB : ∀ z ∈ B, ∀ j, z j ≤ n+1) :
    ∀ i j, |orderedCountMatrix B i j| ≤ ((n+1 : ℕ) : ℤ) := by
  intro i j
  have hi : (orderedCounts B).get i ∈ B := (orderedCounts_mem B _).mp (List.get_mem _ _)
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [orderedCountMatrix,finAugmentedCount]
  · have hh : (((orderedCounts B).get i k : ℕ) : ℤ) ≤ n+1 := by exact_mod_cast hB _ hi k
    simpa [orderedCountMatrix,finAugmentedCount] using hh

/-- The candidate-check operand envelope is attached to the exact emitted
matrix; it includes partial sums for candidates subsequently rejected. -/
theorem preparedNormalCheck_bits (prep : CountMatrixPreparation q)
    (B : Finset (Counts q)) (n : ℕ) (hB : ∀ z ∈ B, ∀ j, z j ≤ n+1)
    {r : ℕ} (a : Fin r → Fin (orderedCounts B).length) (c : Fin r ↪ Fin (q+1))
    (i : Fin (orderedCounts B).length) (j : Fin (q+1)) (S : Finset (Fin (q+1))) :
    signedIntegerBits (∑ l ∈ S, (prep.emit B).1 i l *
      concreteColumnNormal ((prep.emit B).1.submatrix a id) c j l) ≤ normalWorkBits q n := by
  rw [prep.value]
  exact normalCheck_signed_bits _ a c n (orderedCountMatrix_bound B n hB) i j S

/-- Every determinant minor uses only entries of the emitted matrix. Arbitrary
row/column index maps cover the recursively selected submatrices and replaced
columns used by Cramer's rule. -/
theorem preparedNormalMinor_bits (prep : CountMatrixPreparation q)
    (B : Finset (Counts q)) (n : ℕ) (hB : ∀ z ∈ B, ∀ j, z j ≤ n+1)
    {r : ℕ} (hr : r+1 ≤ q+1)
    (a : Fin (r+1) → Fin (orderedCounts B).length) (c : Fin (r+1) → Fin (q+1))
    (S : Finset (Fin (r+1))) :
    signedIntegerBits (∑ j ∈ S, laplaceTerm ((prep.emit B).1.submatrix a c) j) ≤
      normalWorkBits q n := by
  rw [prep.value]
  exact determinant_signed_bits _ q n hr (fun i j => orderedCountMatrix_bound B n hB _ _) S

/-- Local preparation and instruction prices give a uniform polynomial bound
for this actual normal-generation invocation. -/
theorem preparedCountForms_polynomial (K H : ℕ → ℕ) (d a : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ, ∀ q n L (prep : CountMatrixPreparation q) unit E B,
      B.card ≤ q+1 → (prep.emit B).2 ≤ E → E ≤ K q*(n+L+2)^d →
      unit ≤ H q*(n+L+2)^a →
      (preparedCountForms prep unit B).2 ≤ F q*(n+L+2)^e := by
  have hpoly : UniformPolynomial (fun q n L =>
      K q*(n+L+2)^d+builtCountFormBudget q*(H q*(n+L+2)^a)) := by
    uniform_polynomial
  obtain ⟨e,F,hF⟩ := hpoly
  refine ⟨e,F,?_⟩
  intro q n L prep unit E B hB he hE hu
  have hh := preparedCountForms_cost prep unit E B hB he
  have hm := Nat.mul_le_mul_left (builtCountFormBudget q) hu
  have hf := hF q n L
  dsimp only at hf
  omega

end MOR34
