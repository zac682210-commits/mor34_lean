import MOR34.DenseViolationSolver
import MOR34.BuiltNormalBasis

namespace MOR34

/-- The charged query is evaluated once; the returned option chooses whether
the recursive search is evaluated. Terminal list inspection is charged too. -/
def chargedFirstWitness {α β : Type*} (solve : α → Option β × ℕ) :
    List α → Option β × ℕ
  | [] => (none,1)
  | a::L =>
    let out := solve a
    match out.1 with
    | some b => (some b,out.2+1)
    | none => let tail := chargedFirstWitness solve L
              (tail.1,out.2+tail.2+1)

theorem chargedFirstWitness_value {α β : Type*} (solve : α → Option β × ℕ) (L : List α) :
    (chargedFirstWitness solve L).1 = firstWitness (fun a => (solve a).1) L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      cases h : (solve a).1 <;> simp [chargedFirstWitness,firstWitness,h,ih]

theorem chargedFirstWitness_cost {α β : Type*} (solve : α → Option β × ℕ)
    (L : List α) (U : ℕ) (hU : ∀ a ∈ L, (solve a).2 ≤ U) :
    (chargedFirstWitness solve L).2 ≤
      firstWitnessCalls (fun a => (solve a).1) L*(U+1)+1 := by
  induction L with
  | nil => simp [chargedFirstWitness,firstWitnessCalls]
  | cons a L ih =>
      have ha := hU a (by simp)
      have ht := ih (fun b hb => hU b (by simp [hb]))
      cases h : (solve a).1 <;> simp only [chargedFirstWitness,firstWitnessCalls,h] <;> nlinarith

/-- Descending threshold search likewise retains every solver answer and stops
at the first success. Its return value is the original extremum-search value. -/
def chargedDescendingSearch {α : Type*} (solve : ℕ → Option α × ℕ) : ℕ → Option α × ℕ
  | 0 => let out := solve 0; (out.1,out.2+1)
  | n+1 => let out := solve (n+1)
      match out.1 with
      | some z => (some z,out.2+1)
      | none => let tail := chargedDescendingSearch solve n
                (tail.1,out.2+tail.2+1)

theorem chargedDescendingSearch_value {α : Type*} (solve : ℕ → Option α × ℕ) (n : ℕ) :
    (chargedDescendingSearch solve n).1 = descendingSearch (fun k => (solve k).1) n := by
  induction n with
  | zero => rfl
  | succ n ih => cases h : (solve (n+1)).1 <;>
      simp [chargedDescendingSearch,descendingSearch,h,ih]

theorem chargedDescendingSearch_cost {α : Type*} (solve : ℕ → Option α × ℕ) (n U : ℕ)
    (hU : ∀ k ≤ n, (solve k).2 ≤ U) :
    (chargedDescendingSearch solve n).2 ≤ descendingSearchCalls (fun k => (solve k).1) n*(U+1) := by
  induction n with
  | zero => have hh := hU 0 (by omega); simpa [chargedDescendingSearch,descendingSearchCalls] using Nat.add_le_add_right hh 1
  | succ n ih =>
      have ha := hU (n+1) le_rfl
      have ht := ih (fun k hk => hU k (by omega))
      cases h : (solve (n+1)).1 <;> simp only [chargedDescendingSearch,descendingSearchCalls,h] <;> nlinarith

/-- Charged basis search with an external finite-collection insertion primitive.
Only insertion correctness and its local size-dependent cost are supplied. -/
def chargedBasisExecution {α : Type*} [DecidableEq α]
    (step : Finset α → Option α × ℕ) (put : α → Finset α → Finset α × ℕ) :
    ℕ → Finset α → Finset α × ℕ
  | 0,B => (B,1)
  | n+1,B =>
    let out := step B
    match out.1 with
    | none => (B,out.2+1)
    | some z => let next := put z B
                let tail := chargedBasisExecution step put n next.1
                (tail.1,out.2+next.2+tail.2+1)

theorem chargedBasisExecution_value {α : Type*} [DecidableEq α]
    (step : Finset α → Option α × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) (fuel : ℕ) (B : Finset α) :
    (chargedBasisExecution step put fuel B).1 = basisSearch (fun B => (step B).1) fuel B := by
  induction fuel generalizing B with
  | zero => rfl
  | succ n ih =>
      cases h : (step B).1 <;> simp [chargedBasisExecution,basisSearch,h,ih,hp]

theorem chargedBasisExecution_cost {α : Type*} [DecidableEq α]
    (step : Finset α → Option α × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ z B, (put z B).1 = insert z B) (d S I : ℕ)
    (hs : ∀ B, B.card ≤ d → (step B).2 ≤ S)
    (hi : ∀ z B, B.card ≤ d → (put z B).2 ≤ I)
    (fuel : ℕ) (B : Finset α) (hB : B.card+fuel ≤ d) :
    (chargedBasisExecution step put fuel B).2 ≤ fuel*(S+I+1)+1 := by
  induction fuel generalizing B with
  | zero => simp [chargedBasisExecution]
  | succ n ih =>
      have hstep := hs B (by omega)
      cases h : (step B).1 with
      | none => simp only [chargedBasisExecution,h]; nlinarith
      | some z =>
          have hn : (insert z B).card+n ≤ d := by
            have hh := Finset.card_insert_le z B; omega
          have ht := ih (insert z B) hn
          have hin := hi z B (by omega)
          simp only [chargedBasisExecution,h,hp]
          nlinarith

end MOR34
