import MOR34.TracedListConstruction
import MOR34.FiniteTable

namespace MOR34

/-- Enumerate once per rank, retaining the previous layer. Each resulting map
is materialized as a dense table; its r+1 entries are charged to the callback. -/
def chargedFinFunctions : (r d : ℕ) → List (Fin r → Fin d) × ℕ
  | 0, _ => ([Fin.elim0],1)
  | r+1,d =>
      let old := chargedFinFunctions r d
      let out := chargedFlatMap (fun j : Fin d =>
        chargedMap (fun f => (materializeFin (Fin.cases j f),r+1)) old.1) (List.finRange d)
      (out.1, old.2+out.2+d+1)

theorem chargedFinFunctions_value (r d : ℕ) :
    (chargedFinFunctions r d).1 = allFinFunctions r d := by
  induction r with
  | zero => rfl
  | succ r ih => simp [chargedFinFunctions, chargedFlatMap_value, chargedMap_value,
      materializeFin_eq, allFinFunctions, ih]

def functionEnumerationBudget : ℕ → ℕ → ℕ
  | 0,_ => 1
  | r+1,d => functionEnumerationBudget r d + d*(d^r*(r+3)+1)+d+1

theorem chargedFinFunctions_cost (r d : ℕ) :
    (chargedFinFunctions r d).2 ≤ functionEnumerationBudget r d := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hlen : (chargedFinFunctions r d).1.length = d^r := by
        rw [chargedFinFunctions_value, allFinFunctions_length]
      have hmap (j : Fin d) :
          (chargedMap (fun f => (materializeFin (Fin.cases j f),r+1))
            (chargedFinFunctions r d).1).2 ≤ d^r*(r+2) := by
        simpa only [hlen, show r+1+1=r+2 by omega] using
          chargedMap_cost (fun f => (materializeFin (Fin.cases j f),r+1))
            (chargedFinFunctions r d).1 (r+1) (fun _ _ => le_rfl)
      have hf := chargedFlatMap_cost
        (fun j : Fin d => chargedMap (fun f => (materializeFin (Fin.cases j f),r+1))
          (chargedFinFunctions r d).1) (List.finRange d) (d^r*(r+2)) (d^r)
        (fun j _ => hmap j)
        (by intro j _; simp [chargedMap_value, hlen])
      simp only [List.length_finRange] at hf
      simp only [chargedFinFunctions, functionEnumerationBudget]
      nlinarith

theorem functionEnumerationBudget_bound (r d : ℕ) :
    functionEnumerationBudget r d ≤ (r+3)^2*(d+1)^(r+1) := by
  induction r with
  | zero => simp [functionEnumerationBudget]; omega
  | succ r ih =>
      have hb : 1 ≤ d+1 := by omega
      have hp : (d+1)^(r+1) ≤ (d+1)^(r+2) := pow_le_pow_right' hb (by omega)
      have hpow : d*d^r ≤ (d+1)^(r+2) := by
        rw [← pow_succ']
        exact (pow_le_pow_left' (by omega) _).trans hp
      have hd : d+1 ≤ (d+1)^(r+2) := le_self_pow₀ hb (by omega)
      have hI := ih.trans (Nat.mul_le_mul_left ((r+3)^2) hp)
      have hnew := Nat.mul_le_mul_right (r+3) hpow
      unfold functionEnumerationBudget
      nlinarith

theorem chargedFinFunctions_parameter_cost (r d : ℕ) :
    (chargedFinFunctions r d).2 ≤ (r+3)^2*(d+1)^(r+1) :=
  (chargedFinFunctions_cost r d).trans (functionEnumerationBudget_bound r d)

end MOR34
