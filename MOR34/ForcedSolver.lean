import MOR34.ForcedRows
import MOR34.ParitySolver

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

structure ForcedRowSolverSpec (P : Model m)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q)) : Prop where
  found : ∀ j u v s, solve j u v = some s →
    ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds s.1 s.2
  done : ∀ j u v, solve j u v = none → ∀ z y : Fin q → ℤ,
    ¬ ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y

/-- A returned integer solution produces an actual original binary exchange witness. -/
theorem forcedRows_witness (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (huv : u < v) (z y : Fin q → ℤ)
    (hh : ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y) :
    Tight P (forcedSet j u v (decodeCounts z)) ∧
      (⟨j, u⟩ : Item m) ∉ forcedSet j u v (decodeCounts z) ∧
      (⟨j, v⟩ : Item m) ∈ forcedSet j u v (decodeCounts z) := by
  obtain ⟨hb, hl, hu, he, hy⟩ := (forcedRows_iff P j u v z y).mp hh
  have hbound := decodeCounts_bounded z hb
  have hid := encode_decodeCounts z hb
  have hj := congrFun hid j
  change (decodeCounts z j : ℤ) = z j at hj
  have hl' : 1 ≤ decodeCounts z j := by omega
  have hu' : decodeCounts z j ≤ m j - 1 := by omega
  have hep : ForcedEpigraph P j u v (decodeCounts z) y := by
    apply (integerForcedEpigraph_encode P j u v _ hl' y).mp
    rw [hid]
    exact hy
  have hf := (forced_feasible_epigraph P hWF j u v (ne_of_lt huv) _ hbound hl' hu').mpr ⟨y, hep⟩
  have hc := counts_forcedSet j u v (ne_of_lt huv) _ hbound hl' hu'
  refine ⟨⟨hf, ?_⟩, forcedSet_pattern j u v (ne_of_lt huv) _⟩
  rw [candidateValue_counts, hc]
  have he' : (∑ k, P.coefficient k * encodeCounts (decodeCounts z) k) = P.rhs := by
    rw [hid]; exact he
  simpa only [encodeCounts, mul_comm] using he'

def exchangeWitness
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (j : Fin q) (u v : Fin (m j)) : Option (Finset (Item m)) :=
  if u < v then (solve j u v).map (fun s => forcedSet j u v (decodeCounts s.1)) else none

theorem exchangeWitness_some (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (j : Fin q) (u v : Fin (m j))
    (S : Finset (Item m)) (hS : exchangeWitness solve j u v = some S) :
    u < v ∧ Tight P S ∧ (⟨j, u⟩ : Item m) ∉ S ∧ (⟨j, v⟩ : Item m) ∈ S := by
  by_cases huv : u < v
  · cases he : solve j u v with
    | none => simp [exchangeWitness, huv, he] at hS
    | some s =>
      have hEq : forcedSet j u v (decodeCounts s.1) = S := by
        simpa [exchangeWitness, huv, he] using hS
      subst S
      exact ⟨huv, forcedRows_witness P hWF j u v huv s.1 s.2 (hs.found j u v s he)⟩
  · simp [exchangeWitness, huv] at hS

theorem exchangeWitness_none_iff (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (j : Fin q) (u v : Fin (m j)) :
    exchangeWitness solve j u v = none ↔ ¬ Exchange P j u v := by
  constructor
  · intro hn he
    obtain ⟨huv, z, y, hh⟩ := (exchange_iff_forced_rows P hWF j u v).mp he
    have hnone : solve j u v = none := by
      cases h : solve j u v with
      | none => rfl
      | some s => simp [exchangeWitness, huv, h] at hn
    exact hs.done j u v hnone z y hh
  · intro hn
    cases he : exchangeWitness solve j u v with
    | none => rfl
    | some S =>
      obtain ⟨huv, ht, hu, hv⟩ := exchangeWitness_some P hWF solve hs j u v S he
      exact False.elim (hn ⟨huv, S, ht, hu, hv⟩)

def exchangeDecision
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (j : Fin q) (u v : Fin (m j)) : Bool := (exchangeWitness solve j u v).isSome

theorem exchangeDecision_iff (P : Model m) (hWF : WellFormed P)
    (solve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (hs : ForcedRowSolverSpec P solve) (j : Fin q) (u v : Fin (m j)) :
    exchangeDecision solve j u v = true ↔ Exchange P j u v := by
  have hh := exchangeWitness_none_iff P hWF solve hs j u v
  cases he : exchangeWitness solve j u v with
  | none => simp [exchangeDecision, he, hh.mp he]
  | some S =>
    obtain ⟨huv, ht, hu, hv⟩ := exchangeWitness_some P hWF solve hs j u v S he
    have hx : Exchange P j u v := ⟨huv, S, ht, hu, hv⟩
    simp [exchangeDecision, he, hx]

end MOR34
