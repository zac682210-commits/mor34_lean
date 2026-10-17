import MOR34.LinearOracle
import MOR34.BasisIndependence

namespace MOR34
section FiniteSearch
variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq α]

/-- Scan a supplied finite list for the first row outside the selected span. -/
def finiteSpanOracle (L : List α) (outside : Finset α → α → Bool) (B : Finset α) : Option α :=
  firstWitness (fun a => if outside B a then some a else none) L

theorem finiteSpanOracle_spec (L : List α) (v : α → V)
    (outside : Finset α → α → Bool)
    (hout : ∀ B a, outside B a = true ↔ v a ∉ selectedSpan (K := K) v B) :
    SpanOracleSpec (K := K) {a | a ∈ L} v (finiteSpanOracle L outside) := by
  constructor
  · intro B a ha
    obtain ⟨x, hx, he⟩ := firstWitness_some _ _ a ha
    by_cases hh : outside B x = true
    · simp only [hh, ↓reduceIte, Option.some.injEq] at he
      subst x
      exact ⟨hx, (hout B a).mp hh⟩
    · simp [hh] at he
  · intro B hB a ha
    have hh := firstWitness_none _ _ hB a ha
    by_contra hn
    have ho := (hout B a).mpr hn
    simp [ho] at hh

/-- Finite point extraction has a concrete scan, conditional only on its outside test. -/
theorem finite_basis_search (L : List α) (v : α → V)
    (outside : Finset α → α → Bool)
    (hout : ∀ B a, outside B a = true ↔ v a ∉ selectedSpan (K := K) v B) :
    let B := basisSearch (finiteSpanOracle L outside) (Module.finrank K V) ∅
    (∀ a ∈ B, a ∈ L) ∧ B.card ≤ Module.finrank K V ∧
      LinearIndepOn K v (B : Set α) ∧
      (∀ a ∈ L, v a ∈ selectedSpan (K := K) v B) := by
  have ho := finiteSpanOracle_spec L v outside hout
  have hh := basisSearch_from_empty {a | a ∈ L} v _ ho
  exact ⟨hh.1, hh.2.1, basisSearch_independent _ _ _ ho _ _ (by simp), hh.2.2.1⟩

/-- An exact finite rank evaluator implements the outside test. -/
theorem outside_iff_rank_increases (v : α → V)
    (rankEval : Finset α → ℕ)
    (hr : ∀ B, rankEval B = Module.finrank K (selectedSpan (K := K) v B))
    (B : Finset α) (a : α) :
    rankEval B < rankEval (insert a B) ↔ v a ∉ selectedSpan (K := K) v B := by
  rw [hr, hr]
  constructor
  · intro h ha
    have heq : selectedSpan (K := K) v (insert a B) = selectedSpan (K := K) v B := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨b, hb, rfl⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ha
        · exact Submodule.subset_span ⟨b, hb, rfl⟩
      · exact Submodule.span_mono (Set.image_mono (by intro b hb; exact Finset.mem_insert_of_mem hb))
    rw [heq] at h
    exact (lt_irrefl _ h)
  · intro h
    exact Submodule.finrank_lt_finrank_of_lt (selectedSpan_insert_strict v B a h)

def rankOutside (rankEval : Finset α → ℕ) (B : Finset α) (a : α) : Bool :=
  decide (rankEval B < rankEval (insert a B))

theorem finite_rank_basis_search (L : List α) (v : α → V)
    (rankEval : Finset α → ℕ)
    (hr : ∀ B, rankEval B = Module.finrank K (selectedSpan (K := K) v B)) :
    let B := basisSearch (finiteSpanOracle L (rankOutside rankEval)) (Module.finrank K V) ∅
    (∀ a ∈ B, a ∈ L) ∧ B.card ≤ Module.finrank K V ∧
      LinearIndepOn K v (B : Set α) ∧
      (∀ a ∈ L, v a ∈ selectedSpan (K := K) v B) := by
  apply finite_basis_search
  intro B a
  simp only [rankOutside, decide_eq_true_eq]
  exact outside_iff_rank_increases v rankEval hr B a
end FiniteSearch
end MOR34
