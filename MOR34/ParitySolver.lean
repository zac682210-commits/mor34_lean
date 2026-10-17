import MOR34.CellQueries
import MOR34.ParityLinearEncoding

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def queryCoefficients (L : List (IntegerQuery q)) (i : Fin L.length) : Fin q → ℚ :=
  fun j => ((L.get i).coefficient j : ℚ)

def queryBounds (L : List (IntegerQuery q)) (i : Fin L.length) : ℚ := (L.get i).bound

theorem queryRestrictions_iff (L : List (IntegerQuery q)) (z : Counts q) :
    RationalRestrictions (queryCoefficients L) (queryBounds L) (encodeCounts z) ↔ QueryAll L z := by
  have hi (i : Fin L.length) :
      (∑ j, queryCoefficients L i j * (encodeCounts z j : ℚ)) ≤ queryBounds L i ↔
      (L.get i).Holds z := by
    unfold queryCoefficients queryBounds encodeCounts IntegerQuery.Holds
    constructor <;> intro h <;> exact_mod_cast h
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact (hi i).mp (h i)
  · intro h i
    exact (hi i).mpr (h _ (List.get_mem L i))

abbrev IntegerRowSolution (q : ℕ) := (Fin q → ℤ) × (Fin q → ℤ)

def ParityRows (P : Model m) (ε : Parity q) (L : List (IntegerQuery q))
    (s : IntegerRowSolution q) : Prop :=
  ∀ k : CountRow m L.length,
    ((countRow P (queryCoefficients L) (queryBounds L) k).withParity ε).Holds s.1 s.2

/-- Exact input/output contract for the explicit 2q-variable integer row system. -/
structure ParityRowSolverSpec (P : Model m)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : Prop where
  found : ∀ ε L s, solve ε L = some s → ParityRows P ε L s
  done : ∀ ε L, solve ε L = none → ∀ s, ¬ ParityRows P ε L s

def decodedParitySolution (ε : Parity q) (s : IntegerRowSolution q) : Counts q :=
  decodeCounts (paritySubstitution ε s.1)

theorem parityRows_decode (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (L : List (IntegerQuery q)) (s : IntegerRowSolution q) (h : ParityRows P ε L s) :
    TightParity P ε (decodedParitySolution ε s) ∧ QueryAll L (decodedParitySolution ε s) := by
  have hh : CountEpigraph P (paritySubstitution ε s.1) s.2 ∧
      RationalRestrictions (queryCoefficients L) (queryBounds L) (paritySubstitution ε s.1) := by
    simpa only [ParityRows, row_parity_iff, countRows_iff] using h
  have hb := decodeCounts_bounded _ hh.1.1
  have he := encode_decodeCounts _ hh.1.1
  have ht : Tight P (prefixSet (decodedParitySolution ε s)) := by
    apply (tight_prefix_epigraph P hWF _ hb).mpr
    exact ⟨s.2, he.symm ▸ hh.1⟩
  refine ⟨⟨hb, ht, (count_parity_substitution _ ε).mpr ⟨s.1, he⟩⟩, ?_⟩
  apply (queryRestrictions_iff L _).mp
  exact he.symm ▸ hh.2

theorem parityRows_exists_iff (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (L : List (IntegerQuery q)) :
    (∃ s, ParityRows P ε L s) ↔ ∃ z, TightParity P ε z ∧ QueryAll L z := by
  have he := exact_parity_linear_count_encoding P hWF (queryCoefficients L) (queryBounds L) ε
  simp only [queryRestrictions_iff] at he
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨decodedParitySolution ε s, parityRows_decode P hWF ε L s hs⟩
  · rintro ⟨z, hz, hq⟩
    obtain ⟨v, y, hh⟩ := he.mp ⟨z, hz.1, hz.2.1, hz.2.2, hq⟩
    exact ⟨(v, y), hh⟩

def parityListSolver (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (ε : Parity q) (L : List (IntegerQuery q)) : Option (Counts q) :=
  (solve ε L).map (decodedParitySolution ε)

theorem parityListSolver_spec (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (ε : Parity q) :
    QueryListOracleSpec {z | TightParity P ε z} (parityListSolver solve ε) := by
  constructor
  · intro L z hz
    cases he : solve ε L with
    | none => simp [parityListSolver, he] at hz
    | some s =>
      have hh : decodedParitySolution ε s = z := by simpa [parityListSolver, he] using hz
      subst z
      exact parityRows_decode P hWF ε L s (hs.found ε L s he)
  · intro L h z hz hq
    have he : solve ε L = none := by
      cases he : solve ε L with
      | none => rfl
      | some s => simp [parityListSolver, he] at h
    obtain ⟨s, hh⟩ := (parityRows_exists_iff P hWF ε L).mpr ⟨z, hz, hq⟩
    exact hs.done ε L he s hh

end MOR34
