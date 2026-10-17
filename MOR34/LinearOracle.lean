import MOR34.OracleBasis

namespace MOR34

section FirstWitness
variable {α Q : Type*}

def firstWitness (solve : Q → Option α) : List Q → Option α
  | [] => none
  | a :: rest => match solve a with
    | some x => some x
    | none => firstWitness solve rest

def firstWitnessCalls (solve : Q → Option α) : List Q → ℕ
  | [] => 0
  | a :: rest => match solve a with
    | some _ => 1
    | none => 1 + firstWitnessCalls solve rest

theorem firstWitness_some (solve : Q → Option α) (L : List Q) (x : α)
    (h : firstWitness solve L = some x) : ∃ a ∈ L, solve a = some x := by
  induction L with
  | nil => simp [firstWitness] at h
  | cons a L ih =>
    cases hs : solve a with
    | none =>
      simp only [firstWitness, hs] at h
      obtain ⟨b, hb, he⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem a hb, he⟩
    | some y =>
      simp only [firstWitness, hs, Option.some.injEq] at h
      subst y
      exact ⟨a, List.mem_cons_self, hs⟩

theorem firstWitness_none (solve : Q → Option α) (L : List Q)
    (h : firstWitness solve L = none) : ∀ a ∈ L, solve a = none := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases hs : solve a with
    | some y => simp [firstWitness, hs] at h
    | none =>
      simp only [firstWitness, hs] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hs
      · exact ih h b hb

theorem firstWitness_calls_le (solve : Q → Option α) (L : List Q) :
    firstWitnessCalls solve L ≤ L.length := by
  induction L with
  | nil => simp [firstWitnessCalls]
  | cons a L ih =>
    cases hs : solve a <;> simp [firstWitnessCalls, hs] <;> omega

end FirstWitness

structure IntegerQuery (q : ℕ) where
  coefficient : Fin q → ℤ
  bound : ℤ

def IntegerQuery.Holds {q : ℕ} (a : IntegerQuery q) (z : Counts q) : Prop :=
  (∑ j, a.coefficient j * (z j : ℤ)) ≤ a.bound

structure IntegerForm (q : ℕ) where
  coefficient : Fin q → ℤ
  constant : ℤ

def IntegerForm.eval {q : ℕ} (f : IntegerForm q) (z : Counts q) : ℤ :=
  f.constant + ∑ j, f.coefficient j * (z j : ℤ)

def IntegerForm.positiveQuery {q : ℕ} (f : IntegerForm q) : IntegerQuery q :=
  ⟨fun j => -f.coefficient j, f.constant - 1⟩

def IntegerForm.negativeQuery {q : ℕ} (f : IntegerForm q) : IntegerQuery q :=
  ⟨f.coefficient, -1 - f.constant⟩

theorem positiveQuery_iff {q : ℕ} (f : IntegerForm q) (z : Counts q) :
    f.positiveQuery.Holds z ↔ 1 ≤ f.eval z := by
  simp only [IntegerQuery.Holds, IntegerForm.positiveQuery, IntegerForm.eval,
    neg_mul, Finset.sum_neg_distrib]
  omega

theorem negativeQuery_iff {q : ℕ} (f : IntegerForm q) (z : Counts q) :
    f.negativeQuery.Holds z ↔ f.eval z ≤ -1 := by
  unfold IntegerQuery.Holds IntegerForm.negativeQuery IntegerForm.eval
  omega

def outsideQueries {q : ℕ} (forms : List (IntegerForm q)) : List (IntegerQuery q) :=
  forms.flatMap fun f => [f.positiveQuery, f.negativeQuery]

theorem outsideQueries_length {q : ℕ} (forms : List (IntegerForm q)) :
    (outsideQueries forms).length = 2 * forms.length := by
  induction forms with
  | nil => simp [outsideQueries]
  | cons a L ih => simp [outsideQueries] at *; omega

/-- Only feasibility with one additional integer linear inequality is assumed. -/
structure LinearOracleSpec {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) : Prop where
  found : ∀ a z, solve a = some z → z ∈ C ∧ a.Holds z
  done : ∀ a, solve a = none → ∀ z ∈ C, ¬ a.Holds z

/-- A finite list of integer equations describes the current augmented rational span. -/
def FormsDescribe {q : ℕ} (B : Finset (Counts q)) (forms : List (IntegerForm q)) : Prop :=
  ∀ z : Counts q, rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B ↔
    ∀ f ∈ forms, f.eval z = 0

def linearSpanOracle {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (forms : Finset (Counts q) → List (IntegerForm q)) (B : Finset (Counts q)) : Option (Counts q) :=
  firstWitness solve (outsideQueries (forms B))

theorem linearSpanOracle_spec {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hf : ∀ B, FormsDescribe B (forms B)) :
    SpanOracleSpec (K := ℚ) C rationalCountPoint (linearSpanOracle solve forms) := by
  constructor
  · intro B z hz
    obtain ⟨a, ha, he⟩ := firstWitness_some solve (outsideQueries (forms B)) z hz
    obtain ⟨hc, hh⟩ := hs.found a z he
    refine ⟨hc, ?_⟩
    intro hmem
    have hzero := (hf B z).mp hmem
    rcases List.mem_flatMap.mp ha with ⟨f, hfb, ha⟩
    have heval := hzero f hfb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · have hi := (positiveQuery_iff f z).mp hh
      omega
    · have hi := (negativeQuery_iff f z).mp hh
      omega
  · intro B hnone z hz
    apply (hf B z).mpr
    intro f hfb
    have hp : f.positiveQuery ∈ outsideQueries (forms B) :=
      List.mem_flatMap.mpr ⟨f, hfb, by simp⟩
    have hn : f.negativeQuery ∈ outsideQueries (forms B) :=
      List.mem_flatMap.mpr ⟨f, hfb, by simp⟩
    have hpnone := firstWitness_none solve (outsideQueries (forms B)) hnone _ hp
    have hnnone := firstWitness_none solve (outsideQueries (forms B)) hnone _ hn
    have hp' := hs.done f.positiveQuery hpnone z hz
    have hn' := hs.done f.negativeQuery hnnone z hz
    rw [positiveQuery_iff] at hp'
    rw [negativeQuery_iff] at hn'
    omega

theorem linearSpanOracle_calls_le {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (forms : Finset (Counts q) → List (IntegerForm q)) (B : Finset (Counts q)) :
    firstWitnessCalls solve (outsideQueries (forms B)) ≤ 2 * (forms B).length := by
  simpa only [outsideQueries_length] using firstWitness_calls_le solve (outsideQueries (forms B))

end MOR34

namespace MOR34

def linearBasisCalls {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (forms : Finset (Counts q) → List (IntegerForm q)) : ℕ → Finset (Counts q) → ℕ
  | 0, _ => 0
  | n + 1, B => firstWitnessCalls solve (outsideQueries (forms B)) +
      match linearSpanOracle solve forms B with
      | none => 0
      | some z => linearBasisCalls solve forms n (insert z B)

theorem linearBasisCalls_le {q : ℕ} (solve : IntegerQuery q → Option (Counts q))
    (forms : Finset (Counts q) → List (IntegerForm q)) (d : ℕ)
    (hd : ∀ B, (forms B).length ≤ d) (n : ℕ) (B : Finset (Counts q)) :
    linearBasisCalls solve forms n B ≤ 2 * d * n := by
  induction n generalizing B with
  | zero => simp [linearBasisCalls]
  | succ n ih =>
    have hc := linearSpanOracle_calls_le solve forms B
    have hh := hd B
    cases h : linearSpanOracle solve forms B with
    | none =>
      simp only [linearBasisCalls, h, add_zero]
      nlinarith
    | some z =>
      simp only [linearBasisCalls, h]
      have hi := ih (insert z B)
      nlinarith

/-- Correctness and a quadratic feasibility-call bound under explicit normal and solver contracts. -/
theorem linear_count_basis_correct {q : ℕ} (C : Set (Counts q))
    (solve : IntegerQuery q → Option (Counts q)) (hs : LinearOracleSpec C solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hf : ∀ B, FormsDescribe B (forms B)) (hsize : ∀ B, (forms B).length ≤ q + 1) :
    let B := basisSearch (linearSpanOracle solve forms) (q + 1) ∅
    (B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      (∀ z ∈ C, rationalCountPoint z ∈ selectedSpan (K := ℚ) rationalCountPoint B) ∧
      linearBasisCalls solve forms (q + 1) ∅ ≤ 2 * (q + 1) ^ 2 := by
  have ho := linearSpanOracle_spec C solve hs forms hf
  have hc := countBasisSearch_correct C (linearSpanOracle solve forms) ho
  dsimp at hc ⊢
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  have hb := linearBasisCalls_le solve forms (q + 1) hsize (q + 1) ∅
  nlinarith

end MOR34
