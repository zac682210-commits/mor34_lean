import MOR34.CoordinateSearch
import MOR34.OracleCellBases

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Extract the result of the scan; the proof supplies presence, not a chosen alternative point. -/
def maximumWitness (C : Set (Counts q)) (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec C solve) (hn : C.Nonempty) (j : Fin q) (n : ℕ) : Counts q :=
  (maximumSearch solve j n).get
    (Option.isSome_iff_exists.mpr (maximumSearch_exists C solve hs hn j n))

def minimumWitness (C : Set (Counts q)) (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec C solve) (hn : C.Nonempty) (j : Fin q) (n : ℕ)
    (hb : ∀ z ∈ C, z j ≤ n) : Counts q :=
  (minimumSearch solve j n).get
    (Option.isSome_iff_exists.mpr (minimumSearch_exists C solve hs hn j n hb))

theorem maximumWitness_result (C : Set (Counts q)) (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec C solve) (hn : C.Nonempty) (j : Fin q) (n : ℕ) :
    maximumSearch solve j n = some (maximumWitness C solve hs hn j n) := by
  exact (Option.some_get _).symm

theorem minimumWitness_result (C : Set (Counts q)) (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec C solve) (hn : C.Nonempty) (j : Fin q) (n : ℕ)
    (hb : ∀ z ∈ C, z j ≤ n) :
    minimumSearch solve j n = some (minimumWitness C solve hs hn j n hb) := by
  exact (Option.some_get _).symm

/-- Computed attained extrema for the original full parity set. -/
def searchedParityExtrema (P : Model m) (ε : Parity q)
    (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec {z | TightParity P ε z} solve)
    (hn : ∃ z, TightParity P ε z) : ParityExtrema P ε := by
  let C : Set (Counts q) := {z | TightParity P ε z}
  have hb : ∀ j z, z ∈ C → z j ≤ m j := fun j z hz => hz.1 j
  let lo := fun j => minimumWitness C solve hs hn j (m j) (hb j)
  let hi := fun j => maximumWitness C solve hs hn j (m j)
  have hlo := fun j => minimumSearch_spec C solve hs j (m j) (hb j) (lo j)
    (minimumWitness_result C solve hs hn j (m j) (hb j))
  have hhi := fun j => maximumSearch_spec C solve hs j (m j) (hb j) (hi j)
    (maximumWitness_result C solve hs hn j (m j))
  exact {
    low := fun j => lo j j
    high := fun j => hi j j
    lowerWitness := lo
    upperWitness := hi
    lower_mem := fun j => (hlo j).1
    upper_mem := fun j => (hhi j).1
    lower_eq := fun _ => rfl
    upper_eq := fun _ => rfl
    bounds := fun z hz j => ⟨(hlo j).2 z hz, (hhi j).2 z hz⟩
  }

theorem searchedParityExtrema_lower_result (P : Model m) (ε : Parity q)
    (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec {z | TightParity P ε z} solve)
    (hn : ∃ z, TightParity P ε z) (j : Fin q) :
    minimumSearch solve j (m j) = some ((searchedParityExtrema P ε solve hs hn).lowerWitness j) := by
  exact minimumWitness_result {z | TightParity P ε z} solve hs hn j (m j)
    (fun z hz => hz.1 j)

theorem searchedParityExtrema_upper_result (P : Model m) (ε : Parity q)
    (solve : IntegerQuery q → Option (Counts q))
    (hs : LinearOracleSpec {z | TightParity P ε z} solve)
    (hn : ∃ z, TightParity P ε z) (j : Fin q) :
    maximumSearch solve j (m j) = some ((searchedParityExtrema P ε solve hs hn).upperWitness j) := by
  exact maximumWitness_result {z | TightParity P ε z} solve hs hn j (m j)

/-- Across all full parity classes, the coordinate-search query count is singly exponential. -/
theorem all_parity_extrema_calls_le (solve : Parity q → IntegerQuery q → Option (Counts q)) :
    (∑ ε : Parity q, extremaSearchCalls (m := m) (solve ε)) ≤
      2 * (Fintype.card (Item m) + q) * 2 ^ q := by
  calc
    _ ≤ ∑ _ε : Parity q, (2 * (Fintype.card (Item m) + q)) :=
      Finset.sum_le_sum (fun ε _ => extremaSearchCalls_le (m := m) (solve ε))
    _ = _ := by simp [Parity, Nat.mul_comm]

end MOR34
