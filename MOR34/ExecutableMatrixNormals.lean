import MOR34.ConcreteColumnNormals
import MOR34.NormalCandidate

namespace MOR34

structure NormalSearchKey (s d : ℕ) where
  rank : Fin (d+1)
  rows : Fin rank.val → Fin s
  cols : Fin rank.val → Fin d

def normalSearchKeys (s d : ℕ) : List (NormalSearchKey s d) :=
  (List.finRange (d+1)).flatMap fun r =>
    (allFinFunctions r.val s).flatMap fun a =>
      (allFinFunctions r.val d).map fun c => ⟨r, a, c⟩

theorem mem_normalSearchKeys {s d : ℕ} (k : NormalSearchKey s d) : k ∈ normalSearchKeys s d := by
  rcases k with ⟨r, a, c⟩
  apply List.mem_flatMap.mpr
  refine ⟨r, List.mem_finRange r, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨a, mem_allFinFunctions _ _ a, ?_⟩
  exact List.mem_map.mpr ⟨c, mem_allFinFunctions _ _ c, rfl⟩

def tryNormalKey {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (k : NormalSearchKey s d) : Option (Fin d → Fin d → ℤ) :=
  if hi : Function.Injective k.cols then
    let c : Fin k.rank.val ↪ Fin d := ⟨k.cols, hi⟩
    let R := M.submatrix k.rows id
    if laplaceDet k.rank.val (R.submatrix id c) ≠ 0 then
      let v := concreteColumnNormal R c
      if ∀ i j, ∑ l, M i l * v j l = 0 then some v else none
    else none
  else none

def MatrixNormalsDescribe {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (v : Fin d → Fin d → ℤ) : Prop :=
  ∀ y : Fin d → ℚ, y ∈ Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).row) ↔
    ∀ j, ∑ k, y k * (v j k : ℚ) = 0

theorem tryNormalKey_spec {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (k : NormalSearchKey s d) (v : Fin d → Fin d → ℤ) (hv : tryNormalKey M k = some v) :
    MatrixNormalsDescribe M v ∧
      ∀ N : ℕ, 1 ≤ N → (∀ i j, |M i j| ≤ (N : ℤ)) →
        ∀ j l, |v j l| ≤ 2*(d.factorial : ℤ)*(N : ℤ)^d := by
  by_cases hi : Function.Injective k.cols
  · let c : Fin k.rank.val ↪ Fin d := ⟨k.cols, hi⟩
    let R := M.submatrix k.rows id
    by_cases hd : laplaceDet k.rank.val (R.submatrix id c) ≠ 0
    · by_cases hc : ∀ i j, ∑ l, M i l * concreteColumnNormal R c j l = 0
      · have he : concreteColumnNormal R c = v := by
          simpa only [tryNormalKey, dif_pos hi, c, R, if_pos hd, if_pos hc, Option.some.injEq] using hv
        rw [← he, concreteColumnNormal_eq]
        have hd' : (R.submatrix id c).det ≠ 0 := by simpa only [laplaceDet_correct] using hd
        have hc' : ∀ i j, ∑ l, M i l * columnNormal R c j l = 0 := by
          simpa only [concreteColumnNormal_eq] using hc
        constructor
        · exact checked_candidate_describes M k.rows c hd' hc'
        · intro N hN hM
          simpa only [Fintype.card_fin] using columnNormal_uniform_bound R c N hN (fun i j => hM (k.rows i) j)
      · simp only [tryNormalKey, dif_pos hi, c, R, if_pos hd, if_neg hc] at hv
        cases hv
    · simp only [tryNormalKey, dif_pos hi, c, R, if_neg hd] at hv
      cases hv
  · simp [tryNormalKey, hi] at hv

def matrixNormalSearch {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    Option (Fin d → Fin d → ℤ) := firstWitness (tryNormalKey M) (normalSearchKeys s d)

theorem matrixNormalSearch_exists {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    ∃ v, matrixNormalSearch M = some v := by
  obtain ⟨r, hr, a, c, hd, hc⟩ := normal_candidate_exists M
  let k : NormalSearchKey s d := ⟨⟨r, by omega⟩, a, c⟩
  have hk : tryNormalKey M k = some (concreteColumnNormal (M.submatrix a id) c) := by
    have hd' : laplaceDet r ((M.submatrix a id).submatrix id c) ≠ 0 := by
      simpa only [laplaceDet_correct] using hd
    have hc' : ∀ i j, ∑ l, M i l * concreteColumnNormal (M.submatrix a id) c j l = 0 := by
      simpa only [concreteColumnNormal_eq] using hc
    simpa only [tryNormalKey, k, dif_pos c.injective, if_pos hd', if_pos hc']
  cases he : matrixNormalSearch M with
  | some v => exact ⟨v, rfl⟩
  | none =>
    have hh := firstWitness_none (tryNormalKey M) (normalSearchKeys s d) he k (mem_normalSearchKeys k)
    rw [hk] at hh
    contradiction

theorem matrixNormalSearch_isSome {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    (matrixNormalSearch M).isSome := by
  obtain ⟨v, hv⟩ := matrixNormalSearch_exists M
  simp [hv]

/-- The returned entries are obtained by finite search; existence is used only as a proof. -/
def computedMatrixNormals {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) : Fin d → Fin d → ℤ :=
  (matrixNormalSearch M).get (matrixNormalSearch_isSome M)

theorem computedMatrixNormals_spec {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    MatrixNormalsDescribe M (computedMatrixNormals M) ∧
      ∀ N : ℕ, 1 ≤ N → (∀ i j, |M i j| ≤ (N : ℤ)) →
        ∀ j l, |computedMatrixNormals M j l| ≤ 2*(d.factorial : ℤ)*(N : ℤ)^d := by
  have he : matrixNormalSearch M = some (computedMatrixNormals M) := (Option.some_get _).symm
  obtain ⟨k, _, hk⟩ := firstWitness_some (tryNormalKey M) (normalSearchKeys s d) _ he
  exact tryNormalKey_spec M k _ hk

end MOR34
