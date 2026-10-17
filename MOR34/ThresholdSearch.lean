import MOR34.LinearOracle

namespace MOR34
section ThresholdSearch
variable {α : Type*}

/-- Feasibility of a lower bound on a natural-valued score. -/
structure ThresholdOracleSpec (C : Set α) (score : α → ℕ)
    (solve : ℕ → Option α) : Prop where
  found : ∀ k x, solve k = some x → x ∈ C ∧ k ≤ score x
  done : ∀ k, solve k = none → ∀ x ∈ C, score x < k

/-- Scan thresholds downwards and retain the first actual witness. -/
def descendingSearch (solve : ℕ → Option α) : ℕ → Option α
  | 0 => solve 0
  | n + 1 => match solve (n + 1) with
    | some x => some x
    | none => descendingSearch solve n

def descendingSearchCalls (solve : ℕ → Option α) : ℕ → ℕ
  | 0 => 1
  | n + 1 => match solve (n + 1) with
    | some _ => 1
    | none => 1 + descendingSearchCalls solve n

theorem descendingSearch_calls_le (solve : ℕ → Option α) (n : ℕ) :
    descendingSearchCalls solve n ≤ n + 1 := by
  induction n with
  | zero => simp [descendingSearchCalls]
  | succ n ih => cases h : solve (n + 1) <;> simp [descendingSearchCalls, h] <;> omega

/-- An unsuccessful scan certifies emptiness because it includes threshold zero. -/
theorem descendingSearch_none (C : Set α) (score : α → ℕ) (solve : ℕ → Option α)
    (hs : ThresholdOracleSpec C score solve) (n : ℕ)
    (h : descendingSearch solve n = none) : ∀ x, x ∉ C := by
  induction n with
  | zero =>
    intro x hx
    have hh := hs.done 0 h x hx
    omega
  | succ n ih =>
    cases he : solve (n + 1) with
    | some x => simp [descendingSearch, he] at h
    | none => exact ih (by simpa [descendingSearch, he] using h)

/-- A successful bounded scan returns a maximizer, not only a threshold witness. -/
theorem descendingSearch_max (C : Set α) (score : α → ℕ) (solve : ℕ → Option α)
    (hs : ThresholdOracleSpec C score solve) (n : ℕ)
    (hb : ∀ z ∈ C, score z ≤ n) (x : α) (h : descendingSearch solve n = some x) :
    x ∈ C ∧ ∀ z ∈ C, score z ≤ score x := by
  induction n with
  | zero =>
    refine ⟨(hs.found 0 x h).1, ?_⟩
    intro z hz
    have hh := hb z hz
    omega
  | succ n ih =>
    cases he : solve (n + 1) with
    | some y =>
      have hy : y = x := by simpa [descendingSearch, he] using h
      subst y
      obtain ⟨hx, hn⟩ := hs.found (n + 1) x he
      exact ⟨hx, fun z hz => le_trans (hb z hz) hn⟩
    | none =>
      have hb' : ∀ z ∈ C, score z ≤ n := by
        intro z hz
        have hh := hs.done (n + 1) he z hz
        omega
      exact ih hb' (by simpa [descendingSearch, he] using h)

theorem descendingSearch_exists (C : Set α) (score : α → ℕ) (solve : ℕ → Option α)
    (hs : ThresholdOracleSpec C score solve) (hn : C.Nonempty) (n : ℕ) :
    ∃ x, descendingSearch solve n = some x := by
  cases h : descendingSearch solve n with
  | some x => exact ⟨x, h⟩
  | none =>
    obtain ⟨x, hx⟩ := hn
    exact False.elim (descendingSearch_none C score solve hs n h x hx)

end ThresholdSearch
end MOR34
