import MOR34.Model
import Mathlib.Tactic

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def positiveClassIndices (P : Model m) : Finset (Fin q) :=
  Finset.univ.filter (fun j => 0 < P.coefficient j)

/-- Distinct positive coefficient values occurring on actual items. -/
def positiveCandidateValues (P : Model m) : Finset ℤ :=
  (Finset.univ.image (fun i : Item m => P.coefficient i.1)).filter (fun c => 0 < c)

theorem positiveCandidateValues_image (P : Model m) (hWF : WellFormed P) :
    positiveCandidateValues P = (positiveClassIndices P).image P.coefficient := by
  classical
  ext c
  simp only [positiveCandidateValues, positiveClassIndices, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hc⟩
    exact ⟨i.1, hc, rfl⟩
  · rintro ⟨j, hc, rfl⟩
    exact ⟨⟨⟨j, ⟨0, hWF.2.1 j⟩⟩, rfl⟩, hc⟩

theorem positiveCandidateValues_card (P : Model m) (hWF : WellFormed P) :
    (positiveCandidateValues P).card = (positiveClassIndices P).card := by
  rw [positiveCandidateValues_image P hWF]
  exact Finset.card_image_of_injective _ hWF.2.2.2.2.2.2.1

/-- Injectivity permits at most one zero-coefficient class. -/
theorem zeroClass_card_le_one (P : Model m) (hWF : WellFormed P) :
    (Finset.univ.filter (fun j => P.coefficient j = 0)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hWF.2.2.2.2.2.2.1
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

/-- The normalized model's q is at most K+1 for its actual distinct positive values. -/
theorem coefficient_class_parameter_bound (P : Model m) (hWF : WellFormed P) :
    q ≤ (positiveCandidateValues P).card + 1 := by
  have hz := zeroClass_card_le_one P hWF
  have hc : (positiveClassIndices P).card +
      (Finset.univ.filter (fun j => P.coefficient j = 0)).card = q := by
    have hn : Finset.univ.filter (fun j => ¬ 0 < P.coefficient j) =
        Finset.univ.filter (fun j => P.coefficient j = 0) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hh := hWF.2.2.2.2.2.1 j
      omega
    have hh := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.univ) (fun j : Fin q => 0 < P.coefficient j)
    simpa [positiveClassIndices, hn] using hh
  rw [positiveCandidateValues_card P hWF]
  omega

/-- Nonempty classes also give q<=n. -/
theorem coefficient_classes_le_items (P : Model m) (hWF : WellFormed P) :
    q ≤ Fintype.card (Item m) := by
  let f : Fin q → Item m := fun j => ⟨j, ⟨0, hWF.2.1 j⟩⟩
  have hi : Function.Injective f := by
    intro i j h
    exact congrArg Sigma.fst h
  simpa using Fintype.card_le_of_injective f hi
end MOR34
