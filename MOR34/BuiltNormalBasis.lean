import MOR34.NormalEnumerationAggregation

namespace MOR34

/-- The normal search result is retained and converted to the count forms.
The final charge is the dense (q+1)-by-(q+1) form materialization. -/
def builtCountForms {q : ℕ} (B : Finset (Counts q)) : List (IntegerForm q) × ℕ :=
  let out := matrixNormalSearchBuilt (orderedCountMatrix B)
  let normals := out.1.get (by rw [matrixNormalSearchBuilt_value]; exact matrixNormalSearch_isSome _)
  (List.ofFn (fun j : Fin (q+1) => finVectorIntegerForm (normals j)),
    out.2+(q+1)*(q+2)+1)

theorem builtCountForms_value {q : ℕ} (B : Finset (Counts q)) :
    (builtCountForms B).1 = computedCountForms B := by
  have hg {α : Type*} (a b : Option α) (ha : a.isSome) (hb : b.isSome) (he : a=b) :
      a.get ha = b.get hb := by cases he; rfl
  have hsome : (matrixNormalSearchBuilt (orderedCountMatrix B)).1.isSome := by
    rw [matrixNormalSearchBuilt_value]; exact matrixNormalSearch_isSome _
  have he := hg _ _ hsome (matrixNormalSearch_isSome (orderedCountMatrix B))
    (matrixNormalSearchBuilt_value (orderedCountMatrix B))
  exact congrArg (fun v => List.ofFn (fun j : Fin (q+1) => finVectorIntegerForm (v j))) he

def builtCountFormBudget (q : ℕ) : ℕ :=
  normalKeyBuildBudget (q+1)+((q+2)*(q+1)^(2*(q+1)))*normalKeyBudget (q+1)+(q+1)*(q+2)+1

theorem builtCountForms_cost {q : ℕ} (B : Finset (Counts q)) (hB : B.card ≤ q+1) :
    (builtCountForms B).2 ≤ builtCountFormBudget q := by
  have hs : (orderedCounts B).length ≤ q+1 := by simpa only [orderedCounts_length] using hB
  have hh := matrixNormalSearchBuilt_cost (orderedCountMatrix B) (by omega) hs
  dsimp only [builtCountForms, builtCountFormBudget]
  exact Nat.add_le_add_right (Nat.add_le_add_right hh _) 1

/-- Basis search consumes the forms returned by the charged constructor exactly
once at each state. Solver, row emission, and set-insertion charges are separate;
this trace claims only construction of normals and their dense form records. -/
def builtNormalBasisSearch {q : ℕ} (solve : IntegerQuery q → Option (Counts q)) :
    ℕ → Finset (Counts q) → Finset (Counts q) × ℕ
  | 0,B => (B,0)
  | r+1,B =>
      let forms := builtCountForms B
      match firstWitness solve (outsideQueries forms.1) with
      | none => (B,forms.2)
      | some z => let out := builtNormalBasisSearch solve r (insert z B)
                  (out.1,forms.2+out.2)

theorem builtNormalBasisSearch_value {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (fuel : ℕ) (B : Finset (Counts q)) :
    (builtNormalBasisSearch solve fuel B).1 =
      basisSearch (linearSpanOracle solve computedCountForms) fuel B := by
  induction fuel generalizing B with
  | zero => rfl
  | succ r ih =>
      simp only [builtNormalBasisSearch, builtCountForms_value, basisSearch, linearSpanOracle]
      cases firstWitness solve (outsideQueries (computedCountForms B)) <;> simp [ih]

theorem builtNormalBasisSearch_cost {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (fuel : ℕ) (B : Finset (Counts q)) (hB : B.card+fuel ≤ q+1) :
    (builtNormalBasisSearch solve fuel B).2 ≤ fuel*builtCountFormBudget q := by
  induction fuel generalizing B with
  | zero => simp [builtNormalBasisSearch]
  | succ r ih =>
      have hf := builtCountForms_cost B (by omega : B.card ≤ q+1)
      simp only [builtNormalBasisSearch, builtCountForms_value]
      cases he : firstWitness solve (outsideQueries (computedCountForms B)) with
      | none => dsimp only; nlinarith
      | some z =>
          have hn : (insert z B).card+r ≤ q+1 := by
            have hh := Finset.card_insert_le z B
            omega
          have hh := ih (insert z B) hn
          dsimp only
          nlinarith

end MOR34
