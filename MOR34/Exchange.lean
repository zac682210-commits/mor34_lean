import MOR34.PaperInterface
import Mathlib.Tactic

namespace MOR34

theorem tight_swap {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    {S : Finset (Item m)} {u v : Item m}
    (hS : Tight P S) (hu : u ∉ S) (hv : v ∈ S)
    (hw : P.weight u ≤ P.weight v) (hc : P.coefficient u.1 = P.coefficient v.1) :
    Tight P (insert u (S.erase v)) := by
  have he : insert v (S.erase v) = S := Finset.insert_erase hv
  have hsW : weightSum P S = P.weight v + weightSum P (S.erase v) := by
    calc
      weightSum P S = weightSum P (insert v (S.erase v)) := congrArg (weightSum P) he.symm
      _ = _ := by simp [weightSum]
  have hsC : candidateValue P S = P.coefficient v.1 + candidateValue P (S.erase v) := by
    calc
      candidateValue P S = candidateValue P (insert v (S.erase v)) := congrArg (candidateValue P) he.symm
      _ = _ := by simp [candidateValue]
  have hnW : weightSum P (insert u (S.erase v)) =
      P.weight u + weightSum P (S.erase v) := by simp [weightSum, hu]
  have hnC : candidateValue P (insert u (S.erase v)) =
      P.coefficient u.1 + candidateValue P (S.erase v) := by simp [candidateValue, hu]
  rcases hS with ⟨hfeas, ht⟩
  change weightSum P S ≤ P.capacity at hfeas
  constructor
  · change weightSum P (insert u (S.erase v)) ≤ P.capacity
    omega
  · rw [hnC, hc, ← hsC, ht]

theorem intervalExchange {q : ℕ} {m : Fin q → ℕ} (P : Model m) :
    PaperInterface.IntervalExchange P := by
  intro hWF j r s u v hrs hru huv hvs
  rcases hWF with ⟨_, _, _, _, _, _, _, hsorted⟩
  rcases hrs with ⟨hrs, S, hS, hr, hs⟩
  have hrv : r < v := lt_of_le_of_lt hru huv
  have hus : u < s := lt_of_lt_of_le huv hvs
  refine ⟨huv, ?_⟩
  by_cases hu : (⟨j, u⟩ : Item m) ∈ S
  · by_cases hv : (⟨j, v⟩ : Item m) ∈ S
    · have hne : r ≠ u := by
        intro h
        subst r
        exact hr hu
      let S' := insert (⟨j, r⟩ : Item m) (S.erase ⟨j, u⟩)
      refine ⟨S', tight_swap P hS hr hu (hsorted j r u hru) rfl, ?_, ?_⟩
      · simp [S', hne.symm]
      · simp [S', hv, (ne_of_lt huv).symm]
    · have hne : r ≠ u := by
        intro h
        subst r
        exact hr hu
      let S' := insert (⟨j, r⟩ : Item m) (S.erase ⟨j, u⟩)
      have hS' : Tight P S' := tight_swap P hS hr hu (hsorted j r u hru) rfl
      have hs' : (⟨j, s⟩ : Item m) ∈ S' := by
        simp [S', hs, (ne_of_lt hus).symm]
      have hv' : (⟨j, v⟩ : Item m) ∉ S' := by
        simp [S', hv, (ne_of_lt hrv).symm]
      refine ⟨insert (⟨j, v⟩ : Item m) (S'.erase ⟨j, s⟩),
        tight_swap P hS' hv' hs' (hsorted j v s hvs) rfl, ?_, ?_⟩
      · simp [S', hne.symm, ne_of_lt huv]
      · simp
  · by_cases hv : (⟨j, v⟩ : Item m) ∈ S
    · exact ⟨S, hS, hu, hv⟩
    · refine ⟨insert (⟨j, v⟩ : Item m) (S.erase ⟨j, s⟩),
        tight_swap P hS hv hs (hsorted j v s hvs) rfl, ?_, ?_⟩
      · simp [hu, ne_of_lt huv]
      · simp

end MOR34
