import MOR34.RecognitionBranches
import MOR34.PivotSearch

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def executableParityList (q : ℕ) : List (Parity q) := allFinFunctions q 2

theorem executableParityList_mem (ε : Parity q) : ε ∈ executableParityList q := mem_allFinFunctions q 2 ε

theorem executableParityList_length (q : ℕ) : (executableParityList q).length = 2 ^ q := by
  simp [executableParityList, allFinFunctions_length]

def executableSupportSearch
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : Option (Counts q) :=
  firstWitness (fun ε => parityListSolver solve ε []) (executableParityList q)

theorem executableSupportSearch_some (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (z : Counts q) (hz : executableSupportSearch solve = some z) :
    BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
  obtain ⟨ε, _, he⟩ := firstWitness_some _ _ z hz
  have hh := (parityListSolver_spec P hWF solve hs ε).found [] z he
  exact ⟨hh.1.1, hh.1.2.1⟩

theorem executableSupportSearch_none_iff (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    executableSupportSearch solve = none ↔ ¬ ∃ S : Finset (Item m), Tight P S := by
  constructor
  · intro hn ht
    obtain ⟨z, hb, hz⟩ := (support_iff_tight_prefix P hWF).mp ht
    obtain ⟨ε, he⟩ := tight_has_parity P hb hz
    have hh := firstWitness_none _ _ hn ε (executableParityList_mem ε)
    exact (parityListSolver_spec P hWF solve hs ε).done [] hh z he (by simp [QueryAll])
  · intro hn
    cases he : executableSupportSearch solve with
    | none => rfl
    | some z => exact False.elim (hn ⟨prefixSet z, (executableSupportSearch_some P hWF solve hs z he).2⟩)

theorem executableSupportSearch_calls_le
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) :
    firstWitnessCalls (fun ε => parityListSolver solve ε []) (executableParityList q) ≤ 2 ^ q := by
  simpa only [executableParityList_length] using
    firstWitness_calls_le (fun ε => parityListSolver solve ε []) (executableParityList q)

def executableRecognitionBranch (violate : Option (IntegerRowSolution q))
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q)) : RecognitionBranch m :=
  match violate with
  | some s => .invalid (prefixSet (decodeCounts s.1))
  | none => match executableSupportSearch solve with
    | none => .empty
    | some z => .supported z

theorem executableRecognitionBranch_correct (P : Model m) (hWF : WellFormed P)
    (violate : Option (IntegerRowSolution q)) (hv : ViolationSolverSpec P violate)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    (executableRecognitionBranch (m := m) violate solve).Correct P := by
  cases he : violate with
  | some s =>
    simpa [executableRecognitionBranch, he, RecognitionBranch.Correct] using
      violationRows_witness P hWF s.1 s.2 (hv.found s he)
  | none =>
    have hvalid := (violationSolver_none_iff P hWF violate hv).mp he
    cases ht : executableSupportSearch solve with
    | none =>
      simpa [executableRecognitionBranch, he, ht, RecognitionBranch.Correct] using
        And.intro hvalid ((executableSupportSearch_none_iff P hWF solve hs).mp ht)
    | some z =>
      simpa [executableRecognitionBranch, he, ht, RecognitionBranch.Correct] using
        And.intro hvalid (executableSupportSearch_some P hWF solve hs z ht)

end MOR34
