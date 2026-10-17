import MOR34.CoordinateSearch
import MOR34.CellSpan
import Mathlib.Data.List.FinRange

namespace MOR34
variable {q : ℕ}

def QueryAll (L : List (IntegerQuery q)) (z : Counts q) : Prop :=
  ∀ a ∈ L, a.Holds z

/-- A constant row removes a duplicate high endpoint when the extrema coincide. -/
def cellGuard (l h : Counts q) (mode : CellMode q) (j : Fin q) : IntegerQuery q :=
  ⟨fun _ => 0, if mode j = 0 ∨ mode j = 1 then 0 else (h j : ℤ) - (l j : ℤ) - 1⟩

def cellUpperInteger (l h : Counts q) (mode : CellMode q) (j : Fin q) : ℤ :=
  if mode j = 0 then l j else if mode j = 1 then (h j : ℤ) - 2 else h j

def cellCoordinateQueries (l h : Counts q) (mode : CellMode q) (j : Fin q) :
    List (IntegerQuery q) :=
  [coordinateLower j (cellLow l h mode j), coordinateUpper j (cellUpperInteger l h mode j),
    cellGuard l h mode j]

def cellQueries (l h : Counts q) (mode : CellMode q) : List (IntegerQuery q) :=
  (List.finRange q).flatMap (cellCoordinateQueries l h mode)

theorem cellCoordinateQueries_iff (l h : Counts q) (mode : CellMode q) (z : Counts q) (j : Fin q) :
    QueryAll (cellCoordinateQueries l h mode j) z ↔
      (if mode j = 0 then z j = l j else
        if mode j = 1 then l j + 2 ≤ z j ∧ z j + 2 ≤ h j else l j < h j ∧ z j = h j) := by
  simp only [QueryAll, cellCoordinateQueries, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, coordinateLower_iff, coordinateUpper_iff]
  by_cases h0 : mode j = 0
  · simp [cellLow, cellUpperInteger, cellGuard, IntegerQuery.Holds, h0]
    omega
  · by_cases h1 : mode j = 1
    · simp [cellLow, cellUpperInteger, cellGuard, IntegerQuery.Holds, h0, h1]
      omega
    · simp [cellLow, cellUpperInteger, cellGuard, IntegerQuery.Holds, h0, h1]
      omega

theorem cellQueries_iff (l h : Counts q) (mode : CellMode q) (z : Counts q) :
    QueryAll (cellQueries l h mode) z ↔ CellCondition l h mode z := by
  constructor
  · intro hh j
    apply (cellCoordinateQueries_iff l h mode z j).mp
    intro a ha
    exact hh a (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ha⟩)
  · intro hh a ha
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp ha
    exact (cellCoordinateQueries_iff l h mode z j).mpr (hh j) a hj

theorem cellQueries_length (l h : Counts q) (mode : CellMode q) :
    (cellQueries l h mode).length = 3 * q := by
  simp [cellQueries, List.length_flatMap, cellCoordinateQueries, List.sum_replicate, Nat.mul_comm]

/-- Arbitrarily many specified linear constraints, not an unrestricted predicate oracle. -/
structure QueryListOracleSpec (C : Set (Counts q))
    (solve : List (IntegerQuery q) → Option (Counts q)) : Prop where
  found : ∀ L z, solve L = some z → z ∈ C ∧ QueryAll L z
  done : ∀ L, solve L = none → ∀ z ∈ C, ¬ QueryAll L z

def restrictedQueryOracle (solve : List (IntegerQuery q) → Option (Counts q))
    (L : List (IntegerQuery q)) (a : IntegerQuery q) : Option (Counts q) := solve (a :: L)

theorem restrictedQueryOracle_spec (C : Set (Counts q))
    (solve : List (IntegerQuery q) → Option (Counts q)) (hs : QueryListOracleSpec C solve)
    (L : List (IntegerQuery q)) :
    LinearOracleSpec {z | z ∈ C ∧ QueryAll L z} (restrictedQueryOracle solve L) := by
  constructor
  · intro a z hz
    obtain ⟨hc, hh⟩ := hs.found (a :: L) z hz
    exact ⟨⟨hc, fun b hb => hh b (List.mem_cons_of_mem a hb)⟩, hh a List.mem_cons_self⟩
  · intro a h z hz ha
    apply hs.done (a :: L) h z hz.1
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hz.2 b hb

theorem parityCellOracle_spec {m : Fin q → ℕ} (P : Model m) (ε : Parity q)
    (e : ParityExtrema P ε) (mode : CellMode q)
    (solve : List (IntegerQuery q) → Option (Counts q))
    (hs : QueryListOracleSpec {z | TightParity P ε z} solve) :
    LinearOracleSpec (parityCellSet P ε e mode)
      (restrictedQueryOracle solve (cellQueries e.low e.high mode)) := by
  have hh := restrictedQueryOracle_spec {z | TightParity P ε z} solve hs
    (cellQueries e.low e.high mode)
  simpa only [cellQueries_iff, parityCellSet] using hh

theorem unrestrictedQueryOracle_spec (C : Set (Counts q))
    (solve : List (IntegerQuery q) → Option (Counts q)) (hs : QueryListOracleSpec C solve) :
    LinearOracleSpec C (restrictedQueryOracle solve []) := by
  have hh := restrictedQueryOracle_spec C solve hs []
  simpa [QueryAll] using hh

end MOR34
