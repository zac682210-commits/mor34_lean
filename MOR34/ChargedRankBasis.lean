import MOR34.CellLoopComposition
import MOR34.ComputedRankPayload

namespace MOR34

/-- Both ranks and the candidate insertion are evaluated once per outside test.
The rank callback includes construction of its concrete matrix input. -/
def chargedRankOutside {α : Type*} [DecidableEq α]
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (B : Finset α) (a : α) : Bool × ℕ :=
  let old := rank B
  let next := put a B
  let fresh := rank next.1
  (decide (old.1 < fresh.1),old.2+next.2+fresh.2+1)

theorem chargedRankOutside_value {α : Type*} [DecidableEq α]
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (B : Finset α) (a : α) :
    (chargedRankOutside rank put B a).1 = rankOutside (fun S => (rank S).1) B a := by
  simp only [chargedRankOutside,hp,rankOutside]

theorem chargedRankOutside_cost {α : Type*} [DecidableEq α]
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (d U J : ℕ)
    (hr : ∀ B, B.card ≤ d+1 → (rank B).2 ≤ U)
    (hi : ∀ a B, B.card ≤ d → (put a B).2 ≤ J)
    (B : Finset α) (a : α) (hB : B.card ≤ d) :
    (chargedRankOutside rank put B a).2 ≤ 2*U+J+1 := by
  have h0 := hr B (by omega)
  have hcard := Finset.card_insert_le a B
  have h1 := hr (insert a B) (by omega)
  have h2 := hi a B hB
  simp only [chargedRankOutside,hp]
  omega

def chargedRankStep {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (B : Finset α) : Option α × ℕ :=
  chargedFirstWitness (fun a =>
    let out := chargedRankOutside rank put B a
    (if out.1 then some a else none,out.2)) L

theorem chargedRankStep_value {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (B : Finset α) :
    (chargedRankStep L rank put B).1 = finiteSpanOracle L (rankOutside (fun S => (rank S).1)) B := by
  simp only [chargedRankStep,chargedFirstWitness_value,chargedRankOutside_value _ _ hp,finiteSpanOracle]

theorem chargedRankStep_cost {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (d U J : ℕ)
    (hr : ∀ B, B.card ≤ d+1 → (rank B).2 ≤ U)
    (hi : ∀ a B, B.card ≤ d → (put a B).2 ≤ J) (B : Finset α) (hB : B.card ≤ d) :
    (chargedRankStep L rank put B).2 ≤ L.length*(2*U+J+2)+1 := by
  have hh := chargedFirstWitness_cost (fun a =>
    let out := chargedRankOutside rank put B a
    (if out.1 then some a else none,out.2)) L (2*U+J+1)
    (fun a _ => chargedRankOutside_cost rank put hp d U J hr hi B a hB)
  have hc := firstWitness_calls_le (fun a =>
    if (chargedRankOutside rank put B a).1 then some a else none) L
  exact hh.trans (by
    simpa only [Nat.add_assoc] using
      (Nat.add_le_add_right (Nat.mul_le_mul_right (2*U+J+1+1) hc) 1))

def chargedRankBasis {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ) (d : ℕ) :
    Finset α × ℕ := chargedBasisExecution (chargedRankStep L rank put) put d ∅

theorem chargedRankBasis_value {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (d : ℕ) :
    (chargedRankBasis L rank put d).1 =
      basisSearch (finiteSpanOracle L (rankOutside (fun S => (rank S).1))) d ∅ := by
  rw [chargedRankBasis,chargedBasisExecution_value _ _ hp]
  simp only [chargedRankStep_value _ _ _ hp]

theorem chargedRankBasis_cost {α : Type*} [DecidableEq α] (L : List α)
    (rank : Finset α → ℕ × ℕ) (put : α → Finset α → Finset α × ℕ)
    (hp : ∀ a B, (put a B).1 = insert a B) (d U J : ℕ)
    (hr : ∀ B, B.card ≤ d+1 → (rank B).2 ≤ U)
    (hi : ∀ a B, B.card ≤ d → (put a B).2 ≤ J) :
    (chargedRankBasis L rank put d).2 ≤ d*(L.length*(2*U+J+2)+J+2)+1 := by
  have hh := chargedBasisExecution_cost (chargedRankStep L rank put) put hp d
    (L.length*(2*U+J+2)+1) J
    (fun B hB => chargedRankStep_cost L rank put hp d U J hr hi B hB) hi d ∅ (by simp)
  simpa only [Nat.add_assoc,show 1+J+1=J+2 by omega] using hh

end MOR34
