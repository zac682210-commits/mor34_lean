import MOR34.ThresholdSearch

namespace MOR34
variable {q : ℕ}

def coordinateLower (j : Fin q) (k : ℕ) : IntegerQuery q :=
  ⟨fun i => if i = j then -1 else 0, -(k : ℤ)⟩

def coordinateUpper (j : Fin q) (b : ℤ) : IntegerQuery q :=
  ⟨fun i => if i = j then 1 else 0, b⟩

theorem coordinateLower_iff (j : Fin q) (k : ℕ) (z : Counts q) :
    (coordinateLower j k).Holds z ↔ k ≤ z j := by
  simp [coordinateLower, IntegerQuery.Holds, ite_mul]

theorem coordinateUpper_iff (j : Fin q) (b : ℤ) (z : Counts q) :
    (coordinateUpper j b).Holds z ↔ (z j : ℤ) ≤ b := by
  simp [coordinateUpper, IntegerQuery.Holds, ite_mul]

def maximumSearch (solve : IntegerQuery q → Option (Counts q)) (j : Fin q) (n : ℕ) :=
  descendingSearch (fun k => solve (coordinateLower j k)) n

def minimumSearch (solve : IntegerQuery q → Option (Counts q)) (j : Fin q) (n : ℕ) :=
  descendingSearch (fun k => solve (coordinateUpper j ((n : ℤ) - (k : ℤ)))) n

theorem maximumThreshold_spec (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve) (j : Fin q) :
    ThresholdOracleSpec C (fun z => z j) (fun k => solve (coordinateLower j k)) := by
  constructor
  · intro k z h
    obtain ⟨hz, hh⟩ := hs.found _ z h
    exact ⟨hz, (coordinateLower_iff j k z).mp hh⟩
  · intro k h z hz
    have hh := hs.done _ h z hz
    rw [coordinateLower_iff] at hh
    omega

theorem minimumThreshold_spec (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (j : Fin q) (n : ℕ) (hb : ∀ z ∈ C, z j ≤ n) :
    ThresholdOracleSpec C (fun z => n - z j)
      (fun k => solve (coordinateUpper j ((n : ℤ) - (k : ℤ)))) := by
  constructor
  · intro k z h
    obtain ⟨hz, hh⟩ := hs.found _ z h
    have hz' := hb z hz
    rw [coordinateUpper_iff] at hh
    exact ⟨hz, by omega⟩
  · intro k h z hz
    have hh := hs.done _ h z hz
    have hz' := hb z hz
    rw [coordinateUpper_iff] at hh
    omega

theorem maximumSearch_spec (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (j : Fin q) (n : ℕ) (hb : ∀ z ∈ C, z j ≤ n)
    (x : Counts q) (h : maximumSearch solve j n = some x) :
    x ∈ C ∧ ∀ z ∈ C, z j ≤ x j :=
  descendingSearch_max C (fun z => z j) _ (maximumThreshold_spec C solve hs j) n hb x h

theorem minimumSearch_spec (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (j : Fin q) (n : ℕ) (hb : ∀ z ∈ C, z j ≤ n)
    (x : Counts q) (h : minimumSearch solve j n = some x) :
    x ∈ C ∧ ∀ z ∈ C, x j ≤ z j := by
  have hh := descendingSearch_max C (fun z => n - z j) _
    (minimumThreshold_spec C solve hs j n hb) n (fun z hz => Nat.sub_le _ _) x h
  refine ⟨hh.1, ?_⟩
  intro z hz
  have hx := hb x hh.1
  have hz' := hb z hz
  have hi := hh.2 z hz
  change n - z j ≤ n - x j at hi
  omega

theorem maximumSearch_exists (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (hn : C.Nonempty) (j : Fin q) (n : ℕ) : ∃ x, maximumSearch solve j n = some x :=
  descendingSearch_exists C _ _ (maximumThreshold_spec C solve hs j) hn n

theorem minimumSearch_exists (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (hn : C.Nonempty) (j : Fin q) (n : ℕ) (hb : ∀ z ∈ C, z j ≤ n) :
    ∃ x, minimumSearch solve j n = some x :=
  descendingSearch_exists C _ _ (minimumThreshold_spec C solve hs j n hb) hn n

def extremaSearchCalls {m : Fin q → ℕ} (solve : IntegerQuery q → Option (Counts q)) : ℕ :=
  ∑ j, (descendingSearchCalls (fun k => solve (coordinateLower j k)) (m j) +
    descendingSearchCalls (fun k => solve (coordinateUpper j ((m j : ℤ) - (k : ℤ)))) (m j))

theorem extremaSearchCalls_le {m : Fin q → ℕ}
    (solve : IntegerQuery q → Option (Counts q)) :
    extremaSearchCalls (m := m) solve ≤ 2 * (Fintype.card (Item m) + q) := by
  calc
    extremaSearchCalls (m := m) solve ≤ ∑ j, (2 * (m j + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      have h₁ := descendingSearch_calls_le (fun k => solve (coordinateLower j k)) (m j)
      have h₂ := descendingSearch_calls_le
        (fun k => solve (coordinateUpper j ((m j : ℤ) - (k : ℤ)))) (m j)
      omega
    _ = 2 * (Fintype.card (Item m) + q) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp [Item, Fintype.card_sigma]

end MOR34
