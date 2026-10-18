import MOR34.StoredListPrimitives

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- A prefix row constructs its prefix expression from stored data. R bounds
one scalar table read; the dense coefficient records are charged separately. -/
def builtPrefixRow (P : Model m) (j : Fin q) (t : Fin (m j)) (R : ℕ) :
    ConstructedIntegerRow q × ℕ :=
  let pref := chargedPrefixConstruction (fun u => P.weight ⟨j,u⟩) t.val R
  (⟨fun k => .atom (integerPick j (P.weight ⟨j,t⟩) k),
    fun k => .atom (integerPick j (-1) k),
    .add (.mul (.atom (P.weight ⟨j,t⟩)) (.atom t.val)) (.neg pref.1)⟩,
    pref.2+8*(q+1)*(R+1))

theorem builtPrefixRow_value (P : Model m) (j : Fin q) (t : Fin (m j)) (R : ℕ) :
    (builtPrefixRow P j t R).1 = prefixRowConstruction P j t := by
  simp only [builtPrefixRow, chargedPrefixConstruction_value, prefixRowConstruction]

theorem builtPrefixRow_cost (P : Model m) (j : Fin q) (t : Fin (m j))
    (n R : ℕ) (hq : q ≤ n) (hm : m j ≤ n) (hR : R ≤ n+1) :
    (builtPrefixRow P j t R).2 ≤ 32*(n+1)^2 := by
  have hp := chargedPrefixConstruction_cost (fun u => P.weight ⟨j,u⟩) t.val R
  have hp' := Nat.mul_le_mul hm (show R+8 ≤ n+9 by omega)
  have hd := Nat.mul_le_mul (show q+1 ≤ n+1 by omega) (show R+1 ≤ n+2 by omega)
  dsimp only [builtPrefixRow]
  nlinarith

/-- The residual function comes from a previously retained table; its equality
with the original weights and its linear read cost were proved separately. -/
def builtForcedSlope (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (R : ℕ) : ConstructedIntegerRow q × ℕ :=
  let pref := chargedPrefixConstruction (forcedResidualWeights P j u v) a.val R
  (⟨fun k => .atom (integerPick j (forcedResidualWeights P j u v a) k),
    fun k => .atom (integerPick j (-1) k),
    .add (.add
      (.mul (.add (.atom a.val) (.atom 1)) (.atom (forcedResidualWeights P j u v a)))
      (.neg pref.1)) (.neg (.atom (P.weight ⟨j,v⟩)))⟩,
    pref.2+12*(q+1)*(R+1))

theorem builtForcedSlope_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (R : ℕ) :
    (builtForcedSlope P j u v a R).1 = forcedSlopeConstruction P j u v a := by
  simp only [builtForcedSlope, chargedPrefixConstruction_value, forcedSlopeConstruction]

theorem builtForcedSlope_cost (P : Model m) (j : Fin q) (u v : Fin (m j))
    (a : Fin (pairAllowed u v).card) (n R : ℕ)
    (hq : q ≤ n) (hm : m j ≤ n) (hR : R ≤ n+1) :
    (builtForcedSlope P j u v a R).2 ≤ 32*(n+1)^2 := by
  have hc : (pairAllowed u v).card ≤ n :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans hm
  have hp := chargedPrefixConstruction_cost (forcedResidualWeights P j u v) a.val R
  have hp' := Nat.mul_le_mul hc (show R+8 ≤ n+9 by omega)
  have hd := Nat.mul_le_mul (show q+1 ≤ n+1 by omega) (show R+1 ≤ n+2 by omega)
  dsimp only [builtForcedSlope]
  nlinarith

/-- All expensive prefix cases use the explicit constructors. Remaining cases
contain only dense stored-data reads and a bounded number of arithmetic nodes. -/
def builtForcedRow (P : Model m) (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    ForcedRow m j u v → ConstructedIntegerRow q × ℕ
  | .inr (.inl ⟨k,a⟩) => if k=j then (atomicIntegerRow 0 0 0,12*(q+1)*(R+1))
      else builtPrefixRow P k a R
  | .inr (.inr (.inl a)) => builtForcedSlope P j u v a R
  | k => (forcedRowConstruction P j u v k,12*(q+1)*(R+1))

theorem builtForcedRow_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (k : ForcedRow m j u v) :
    (builtForcedRow P j u v R k).1 = forcedRowConstruction P j u v k := by
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  all_goals simp only [builtForcedRow, forcedRowConstruction, forcedOrdinaryConstruction,
    builtPrefixRow_value, builtForcedSlope_value]
  all_goals split_ifs <;> simp only [builtPrefixRow_value]

theorem builtForcedRow_cost (P : Model m) (j : Fin q) (u v : Fin (m j))
    (n R : ℕ) (hq : q ≤ n) (hm : ∀ k, m k ≤ n) (hR : R ≤ n+1)
    (k : ForcedRow m j u v) :
    (builtForcedRow P j u v R k).2 ≤ 32*(n+1)^2 := by
  have hd : 12*(q+1)*(R+1) ≤ 32*(n+1)^2 := by
    have hh := Nat.mul_le_mul (show q+1 ≤ n+1 by omega) (show R+1 ≤ n+2 by omega)
    nlinarith
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  · exact hd
  · exact hd
  · exact hd
  · exact hd
  · simp only [builtForcedRow]
    split_ifs
    · exact hd
    · exact builtPrefixRow_cost P k a n R hq (hm k) hR
  · exact builtForcedSlope_cost P j u v a n R hq (hm j) hR
  · exact hd
  · exact hd

theorem builtForcedRows_interpret (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (k : ForcedRow m j u v) :
    (builtForcedRow P j u v R k).1.value = forcedRow P j u v k := by
  rw [builtForcedRow_value, forcedRowConstruction_value]

theorem builtForcedRows_total_cost (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) (hR : R ≤ Fintype.card (Item m)+1) :
    (∑ k : ForcedRow m j u v, (builtForcedRow P j u v R k).2) ≤
      192*(Fintype.card (Item m)+1)^3 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  have hc : (pairAllowed u v).card ≤ n :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans (hm j)
  calc
    _ ≤ ∑ _k : ForcedRow m j u v, 32*(n+1)^2 :=
      Finset.sum_le_sum (fun k _ => builtForcedRow_cost P j u v n R hq hm hR k)
    _ = (n+2*q+(pairAllowed u v).card+6)*(32*(n+1)^2) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, forcedRow_card]; rfl
    _ ≤ (6*(n+1))*(32*(n+1)^2) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end MOR34
