import MOR34.FiniteCellBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace MOR34
section OracleBasis
variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [DecidableEq α]

noncomputable def selectedSpan (v : α → V) (B : Finset α) : Submodule K V :=
  Submodule.span K (v '' (B : Set α))

/-- The contract explicitly separates witness soundness from a complete stopping answer. -/
structure SpanOracleSpec (C : Set α) (v : α → V) (oracle : Finset α → Option α) : Prop where
  found : ∀ B a, oracle B = some a → a ∈ C ∧ v a ∉ selectedSpan (K := K) v B
  done : ∀ B, oracle B = none → ∀ a ∈ C, v a ∈ selectedSpan (K := K) v B

/-- A fuel-bounded procedure; it is executable whenever the supplied oracle is executable. -/
def basisSearch (oracle : Finset α → Option α) : ℕ → Finset α → Finset α
  | 0, B => B
  | n + 1, B => match oracle B with
    | none => B
    | some a => basisSearch oracle n (insert a B)

def basisSearchCalls (oracle : Finset α → Option α) : ℕ → Finset α → ℕ
  | 0, _ => 0
  | n + 1, B => match oracle B with
    | none => 1
    | some a => 1 + basisSearchCalls oracle n (insert a B)

theorem basisSearch_card (oracle : Finset α → Option α) (n : ℕ) (B : Finset α) :
    (basisSearch oracle n B).card ≤ B.card + n := by
  induction n generalizing B with
  | zero => simp [basisSearch]
  | succ n ih =>
    cases h : oracle B with
    | none => simp [basisSearch, h]
    | some a =>
      simp only [basisSearch, h]
      have hc := Finset.card_insert_le a B
      have hi := ih (insert a B)
      omega

theorem basisSearch_calls_le (oracle : Finset α → Option α) (n : ℕ) (B : Finset α) :
    basisSearchCalls oracle n B ≤ n := by
  induction n generalizing B with
  | zero => simp [basisSearchCalls]
  | succ n ih =>
    cases h : oracle B with
    | none => simp [basisSearchCalls, h]
    | some a =>
      simp only [basisSearchCalls, h]
      have hi := ih (insert a B)
      omega

theorem basisSearch_subset (C : Set α) (v : α → V) (oracle : Finset α → Option α)
    (ho : SpanOracleSpec (K := K) C v oracle) (n : ℕ) (B : Finset α) (hb : (B : Set α) ⊆ C) :
    (↑(basisSearch oracle n B) : Set α) ⊆ C := by
  induction n generalizing B with
  | zero => exact hb
  | succ n ih =>
    cases h : oracle B with
    | none => simpa [basisSearch, h] using hb
    | some a =>
      simp only [basisSearch, h]
      apply ih (insert a B)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (ho.found B a h).1
      · exact hb hx

theorem selectedSpan_insert_strict (v : α → V) (B : Finset α) (a : α)
    (ha : v a ∉ selectedSpan (K := K) v B) :
    selectedSpan (K := K) v B < selectedSpan (K := K) v (insert a B) := by
  apply lt_of_le_of_ne
  · apply Submodule.span_mono
    exact Set.image_mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
  · intro he
    apply ha
    rw [he]
    exact Submodule.subset_span ⟨a, Finset.mem_insert_self a B, rfl⟩

/-- Ambient dimension bounds the number of successful extensions. -/
theorem basisSearch_spans (C : Set α) (v : α → V) (oracle : Finset α → Option α)
    (ho : SpanOracleSpec (K := K) C v oracle) (n : ℕ) (B : Finset α)
    (hbudget : Module.finrank K V ≤ Module.finrank K (selectedSpan (K := K) v B) + n) :
    ∀ a ∈ C, v a ∈ selectedSpan (K := K) v (basisSearch oracle n B) := by
  induction n generalizing B with
  | zero =>
    have he : selectedSpan (K := K) v B = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hh := Submodule.finrank_le (selectedSpan (K := K) v B)
      omega
    simp only [basisSearch, he, Submodule.mem_top, implies_true]
  | succ n ih =>
    cases h : oracle B with
    | none => simpa only [basisSearch, h] using ho.done B h
    | some a =>
      simp only [basisSearch, h]
      apply ih (insert a B)
      have hi := Submodule.finrank_lt_finrank_of_lt
        (selectedSpan_insert_strict v B a (ho.found B a h).2)
      omega

theorem basisSearch_from_empty (C : Set α) (v : α → V) (oracle : Finset α → Option α)
    (ho : SpanOracleSpec (K := K) C v oracle) :
    let B := basisSearch oracle (Module.finrank K V) ∅
    (B : Set α) ⊆ C ∧ B.card ≤ Module.finrank K V ∧
      (∀ a ∈ C, v a ∈ selectedSpan (K := K) v B) ∧
      basisSearchCalls oracle (Module.finrank K V) ∅ ≤ Module.finrank K V := by
  dsimp
  refine ⟨basisSearch_subset C v oracle ho _ ∅ (by simp), ?_, ?_, basisSearch_calls_le _ _ _⟩
  · simpa using basisSearch_card oracle (Module.finrank K V) ∅
  · apply basisSearch_spans C v oracle ho
    simp [selectedSpan]

end OracleBasis
end MOR34

namespace MOR34

/-- Rational augmented count points used by the affine-basis subroutine. -/
def rationalCountPoint {q : ℕ} (z : Counts q) : ℚ × (Fin q → ℚ) :=
  (1, fun j => z j)

theorem countBasisSearch_correct {q : ℕ} (C : Set (Counts q))
    (oracle : Finset (Counts q) → Option (Counts q))
    (ho : SpanOracleSpec (K := ℚ) C rationalCountPoint oracle) :
    let B := basisSearch oracle (q + 1) ∅
    (B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      (∀ z ∈ C, rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B) ∧
      basisSearchCalls oracle (q + 1) ∅ ≤ q + 1 := by
  classical
  have hd : Module.finrank ℚ (ℚ × (Fin q → ℚ)) = q + 1 := by
    simp [Module.finrank_prod, Module.finrank_pi, Nat.add_comm]
  simpa only [hd] using basisSearch_from_empty C rationalCountPoint oracle ho

end MOR34
