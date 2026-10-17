import MOR34.ViolationEncoding
import MOR34.ParitySolver

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

structure ViolationSolverSpec (P : Model m) (solve : Option (IntegerRowSolution q)) : Prop where
  found : ∀ s, solve = some s → ∀ k : ViolationRow m, (violationRow P k).Holds s.1 s.2
  done : solve = none → ∀ z y : Fin q → ℤ, ¬ ∀ k : ViolationRow m, (violationRow P k).Holds z y

theorem violationRows_witness (P : Model m) (hWF : WellFormed P)
    (z y : Fin q → ℤ) (h : ∀ k : ViolationRow m, (violationRow P k).Holds z y) :
    Feasible P (prefixSet (decodeCounts z)) ∧
      P.rhs < candidateValue P (prefixSet (decodeCounts z)) := by
  obtain ⟨he, hv⟩ := (violationRows_iff P z y).mp h
  obtain ⟨hb, hf⟩ := feasibleEpigraph_decode P hWF z y he
  have hid := encode_decodeCounts z he.1
  have hv' : P.rhs + 1 ≤ ∑ j, P.coefficient j * (decodeCounts z j : ℤ) := by
    change P.rhs + 1 ≤ ∑ j, P.coefficient j * encodeCounts (decodeCounts z) j
    rw [hid]
    exact hv
  refine ⟨hf, ?_⟩
  rw [candidateValue_counts, counts_prefixSet _ hb]
  simp only [mul_comm] at hv'
  omega

theorem violationSolver_none_iff (P : Model m) (hWF : WellFormed P)
    (solve : Option (IntegerRowSolution q)) (hs : ViolationSolverSpec P solve) :
    solve = none ↔ Valid P := by
  constructor
  · intro hn
    by_contra hv
    obtain ⟨z, y, hh⟩ := (invalid_iff_violation_rows P hWF).mp hv
    exact hs.done hn z y hh
  · intro hv
    cases he : solve with
    | none => rfl
    | some s =>
      have hh := violationRows_witness P hWF s.1 s.2 (hs.found s he)
      exact False.elim (not_lt_of_ge (hv _ hh.1) hh.2)

noncomputable def parityList (q : ℕ) : List (Parity q) := Finset.univ.toList

theorem parityList_mem (ε : Parity q) : ε ∈ parityList q := by simp [parityList]

theorem parityList_length (q : ℕ) : (parityList q).length = 2 ^ q := by
  simp [parityList, Parity]

noncomputable def supportSearch
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : Option (Counts q) :=
  firstWitness (fun ε => parityListSolver solve ε []) (parityList q)

theorem supportSearch_some (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (z : Counts q) (hz : supportSearch solve = some z) :
    BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
  obtain ⟨ε, _, he⟩ := firstWitness_some _ _ z hz
  have hh := (parityListSolver_spec P hWF solve hs ε).found [] z he
  exact ⟨hh.1.1, hh.1.2.1⟩

theorem supportSearch_none_iff (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    supportSearch solve = none ↔ ¬ ∃ S : Finset (Item m), Tight P S := by
  constructor
  · intro hn ht
    obtain ⟨z, hb, hz⟩ := (support_iff_tight_prefix P hWF).mp ht
    obtain ⟨ε, he⟩ := tight_has_parity P hb hz
    have hh := firstWitness_none _ _ hn ε (parityList_mem ε)
    exact (parityListSolver_spec P hWF solve hs ε).done [] hh z he (by simp [QueryAll])
  · intro hn
    cases he : supportSearch solve with
    | none => rfl
    | some z => exact False.elim (hn ⟨prefixSet z, (supportSearch_some P hWF solve hs z he).2⟩)

theorem supportSearch_calls_le
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) :
    firstWitnessCalls (fun ε => parityListSolver solve ε []) (parityList q) ≤ 2 ^ q := by
  simpa only [parityList_length] using
    firstWitness_calls_le (fun ε => parityListSolver solve ε []) (parityList q)

inductive RecognitionBranch (m : Fin q → ℕ) where
  | invalid (witness : Finset (Item m))
  | empty
  | supported (profile : Counts q)

noncomputable def recognitionBranch (violate : Option (IntegerRowSolution q))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : RecognitionBranch m :=
  match violate with
  | some s => .invalid (prefixSet (decodeCounts s.1))
  | none => match supportSearch solve with
    | none => .empty
    | some z => .supported z

def RecognitionBranch.Correct (P : Model m) : RecognitionBranch m → Prop
  | .invalid S => Feasible P S ∧ P.rhs < candidateValue P S
  | .empty => Valid P ∧ ¬ ∃ S : Finset (Item m), Tight P S
  | .supported z => Valid P ∧ BoundedCounts (m := m) z ∧ Tight P (prefixSet z)

theorem recognitionBranch_correct (P : Model m) (hWF : WellFormed P)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    (recognitionBranch (m := m) violate solve).Correct P := by
  cases he : violate with
  | some s =>
    simpa [recognitionBranch, he, RecognitionBranch.Correct] using
      violationRows_witness P hWF s.1 s.2 (hv.found s he)
  | none =>
    have hvalid := (violationSolver_none_iff P hWF violate hv).mp he
    cases ht : supportSearch solve with
    | none =>
      simpa [recognitionBranch, he, ht, RecognitionBranch.Correct] using
        And.intro hvalid ((supportSearch_none_iff P hWF solve hs).mp ht)
    | some z =>
      simpa [recognitionBranch, he, ht, RecognitionBranch.Correct] using
        And.intro hvalid (supportSearch_some P hWF solve hs z ht)

end MOR34
