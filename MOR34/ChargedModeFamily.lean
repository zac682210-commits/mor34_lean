import MOR34.ChargedExtremaTable

namespace MOR34

/-- Visit each mode once and retain its emitted point list. Serialization is a
standard finite-collection primitive, with its local contract stated below. -/
def chargedModeFamily {q : ℕ}
    (cell : CellMode q → Finset (Counts q) × ℕ)
    (serialize : Finset (Counts q) → List (Counts q) × ℕ) : List (Counts q) × ℕ :=
  let modes := chargedFinFunctions q 3
  let out := chargedFlatMap (fun mode =>
    let b := cell mode
    let values := serialize b.1
    (values.1,b.2+values.2+1)) modes.1
  (out.1,modes.2+out.2+1)

theorem chargedModeFamily_value {q : ℕ}
    (cell : CellMode q → Finset (Counts q) × ℕ)
    (serialize : Finset (Counts q) → List (Counts q) × ℕ)
    (hs : ∀ B, (serialize B).1.toFinset = B) :
    (chargedModeFamily cell serialize).1.toFinset =
      Finset.univ.biUnion (fun mode => (cell mode).1) := by
  classical
  ext z
  simp only [chargedModeFamily,chargedFlatMap_value,chargedFinFunctions_value,
    List.mem_toFinset,List.mem_flatMap,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨mode,_,hz⟩
    refine ⟨mode, ?_⟩
    have hh := List.mem_toFinset.mpr hz
    simpa only [hs] using hh
  · rintro ⟨mode,hz⟩
    exact ⟨mode,mem_allFinFunctions q 3 mode,
      List.mem_toFinset.mp (by simpa only [hs] using hz)⟩

theorem chargedModeFamily_cost {q : ℕ}
    (cell : CellMode q → Finset (Counts q) × ℕ)
    (serialize : Finset (Counts q) → List (Counts q) × ℕ) (C E M : ℕ)
    (hc : ∀ mode, (cell mode).2 ≤ C)
    (he : ∀ mode, (serialize (cell mode).1).2 ≤ E)
    (hm : ∀ mode, (serialize (cell mode).1).1.length ≤ M) :
    (chargedModeFamily cell serialize).2 ≤
      functionEnumerationBudget q 3+3^q*(C+E+M+2)+1 := by
  have hh := chargedFlatMap_cost (fun mode =>
      let b := cell mode
      let values := serialize b.1
      (values.1,b.2+values.2+1)) (chargedFinFunctions q 3).1 (C+E+1) M
      (fun mode _ => by dsimp; have h1 := hc mode; have h2 := he mode; omega)
      (fun mode _ => hm mode)
  rw [chargedFinFunctions_value,allFinFunctions_length] at hh
  have hf := chargedFinFunctions_cost q 3
  dsimp only [chargedModeFamily]
  nlinarith

theorem chargedModeFamily_length {q : ℕ}
    (cell : CellMode q → Finset (Counts q) × ℕ)
    (serialize : Finset (Counts q) → List (Counts q) × ℕ) (M : ℕ)
    (hm : ∀ mode, (serialize (cell mode).1).1.length ≤ M) :
    (chargedModeFamily cell serialize).1.length ≤ 3^q*M := by
  have aux : ∀ L : List (CellMode q),
      (L.flatMap (fun mode => (serialize (cell mode).1).1)).length ≤ L.length*M := by
    intro L
    induction L with
    | nil => simp
    | cons mode L ih =>
        have hh := hm mode
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        nlinarith
  simpa only [chargedModeFamily,chargedFlatMap_value,chargedFinFunctions_value,
    allFinFunctions_length] using aux (allFinFunctions q 3)

end MOR34
