import MOR34.RetainedPrefixReads
import MOR34.MaterializedRowConstruction

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- T and its length are retained data. The coefficient and the prefix are read
from T; the scalar vRead is an already returned original-input read. -/
def retainedSlopeRow {N : ℕ} (j : Fin q) (a : Fin N) (T : List ℤ)
    (vRead : ℤ × ℕ) : ConstructedIntegerRow q × ℕ :=
  let slope := storedIntegerRead T a.val
  let pref := readPrefixConstruction (fun i : Fin N => storedIntegerRead T i.val) a.val
  (⟨fun k => .atom (integerPick j slope.1 k),
    fun k => .atom (integerPick j (-1) k),
    .add (.add (.mul (.add (.atom a.val) (.atom 1)) (.atom slope.1))
      (.neg pref.1)) (.neg (.atom vRead.1))⟩,
    pref.2+slope.2+vRead.2+12*(q+1))

theorem retainedSlopeRow_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (R : ℕ) (T : List ℤ)
    (hT : T = (chargedResidualWeights P j u v R).1) (vRead : ℤ × ℕ)
    (hv : vRead.1 = P.weight ⟨j,v⟩) :
    (retainedSlopeRow j a T vRead).1 = forcedSlopeConstruction P j u v a := by
  simp only [retainedSlopeRow, retainedResidualScalar_value P j u v R T hT,
    retainedResidualPrefix_value P j u v R T hT, hv, forcedSlopeConstruction]

theorem retainedSlopeRow_cost {N : ℕ} (j : Fin q) (a : Fin N) (T : List ℤ)
    (vRead : ℤ × ℕ) (n : ℕ) (hq : q ≤ n) (hN : N ≤ n)
    (hT : T.length ≤ n) (hv : vRead.2 ≤ n+1) :
    (retainedSlopeRow j a T vRead).2 ≤ 32*(n+1)^2 := by
  have hs := (storedIntegerRead_cost T a.val).trans (Nat.add_le_add_right hT 1)
  have hp := readPrefixConstruction_cost (fun i : Fin N => storedIntegerRead T i.val)
    a.val (n+1) (fun i => (storedIntegerRead_cost T i.val).trans (Nat.add_le_add_right hT 1))
  have hp' := hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (n+1+8) hN) 2)
  dsimp only [retainedSlopeRow]
  nlinarith

/-- Replace the slope branch in the actual forced-row constructor. T is passed
through to every row; no row reconstructs its residual table. -/
def retainedForcedRow (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ) :
    ForcedRow m j u v → ConstructedIntegerRow q × ℕ
  | .inr (.inr (.inl a)) => retainedSlopeRow j a T vRead
  | k => builtForcedRow P j u v R k

theorem retainedForcedRow_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ)
    (hT : T = (chargedResidualWeights P j u v R).1)
    (hv : vRead.1 = P.weight ⟨j,v⟩) (k : ForcedRow m j u v) :
    (retainedForcedRow P j u v T vRead R k).1 = forcedRowConstruction P j u v k := by
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  all_goals first
  | exact builtForcedRow_value P j u v R _
  | exact retainedSlopeRow_value P j u v a R T hT vRead hv

theorem retainedForcedRow_cost (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (n R : ℕ)
    (hq : q ≤ n) (hm : ∀ k, m k ≤ n) (hR : R ≤ n+1)
    (hT : T.length ≤ n) (hv : vRead.2 ≤ n+1) (k : ForcedRow m j u v) :
    (retainedForcedRow P j u v T vRead R k).2 ≤ 32*(n+1)^2 := by
  have hc : (pairAllowed u v).card ≤ n :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans (hm j)
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  all_goals first
  | exact builtForcedRow_cost P j u v n R hq hm hR _
  | exact retainedSlopeRow_cost j a T vRead n hq hc hT hv

theorem retainedForcedRow_interpret (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ)
    (hT : T = (chargedResidualWeights P j u v R).1)
    (hv : vRead.1 = P.weight ⟨j,v⟩) (k : ForcedRow m j u v) :
    (retainedForcedRow P j u v T vRead R k).1.value = forcedRow P j u v k := by
  rw [retainedForcedRow_value P j u v T vRead R hT hv, forcedRowConstruction_value]

end MOR34
