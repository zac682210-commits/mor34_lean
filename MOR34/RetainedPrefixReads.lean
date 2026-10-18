import MOR34.StoredListPrimitives

namespace MOR34

/-- A supplied reader is called once for each selected index. Its returned
value and actual reference charge are both retained. -/
def readPrefixConstruction {n : ℕ} (read : Fin n → ℤ × ℕ) (z : ℕ) :
    IntegerConstruction × ℕ :=
  let indices := chargedFilter (fun i : Fin n => (decide (i.val < z),1)) (List.finRange n)
  let weights := chargedMap read indices.1
  (sumConstruction weights.1, indices.2+weights.2+n+1+2*weights.1.length+1)

theorem readPrefixConstruction_value {n : ℕ} (read : Fin n → ℤ × ℕ) (z : ℕ) :
    (readPrefixConstruction read z).1 = prefixConstruction (fun i => (read i).1) z := by
  simp only [readPrefixConstruction, chargedFilter_value, chargedMap_value, prefixConstruction]
  rw [show (List.finRange n).filter (fun i => decide (i.val < z)) =
    (classPrefix n z).sort (· ≤ ·) from prefixIndexList_sorted n z]

theorem readPrefixConstruction_cost {n : ℕ} (read : Fin n → ℤ × ℕ) (z R : ℕ)
    (hR : ∀ i, (read i).2 ≤ R) :
    (readPrefixConstruction read z).2 ≤ n*(R+8)+2 := by
  have hf := chargedFilter_cost (fun i : Fin n => (decide (i.val < z),1))
    (List.finRange n) 1 (fun _ _ => le_rfl)
  have hl : (chargedFilter (fun i : Fin n => (decide (i.val < z),1))
      (List.finRange n)).1.length ≤ n := by
    rw [chargedFilter_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hm := chargedMap_cost read
    (chargedFilter (fun i : Fin n => (decide (i.val < z),1)) (List.finRange n)).1 R
    (fun i _ => hR i)
  have hm' := hm.trans (Nat.mul_le_mul_right (R+1) hl)
  simp only [List.length_finRange] at hf
  simp only [readPrefixConstruction, chargedMap_value, List.length_map]
  nlinarith

/-- A missing entry has value zero. Correctness callers prove the supplied index
is present; a miss still pays for every visited cell. -/
def storedIntegerRead (T : List ℤ) (i : ℕ) : ℤ × ℕ :=
  let x := chargedListRead T i
  (x.1.getD 0,x.2)

theorem storedIntegerRead_cost (T : List ℤ) (i : ℕ) :
    (storedIntegerRead T i).2 ≤ T.length+1 := chargedListRead_cost T i

theorem storedIntegerRead_of_present (T : List ℤ) (i : ℕ) (v : ℤ)
    (hv : T[i]? = some v) : (storedIntegerRead T i).1 = v := by
  simp only [storedIntegerRead, chargedListRead_value, hv, Option.getD_some]

variable {q : ℕ} {m : Fin q → ℕ}

theorem retainedResidualScalar_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (T : List ℤ) (hT : T = (chargedResidualWeights P j u v R).1)
    (i : Fin (pairAllowed u v).card) :
    (storedIntegerRead T i.val).1 = forcedResidualWeights P j u v i := by
  have hh := storedResidualRead_value P j u v R T hT i
  simp only [storedIntegerRead, hh, Option.getD_some]

theorem retainedResidualPrefix_value (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (T : List ℤ) (hT : T = (chargedResidualWeights P j u v R).1) (z : ℕ) :
    (readPrefixConstruction (fun i : Fin (pairAllowed u v).card =>
      storedIntegerRead T i.val) z).1 = prefixConstruction (forcedResidualWeights P j u v) z := by
  rw [readPrefixConstruction_value]
  congr 1
  funext i
  exact retainedResidualScalar_value P j u v R T hT i

theorem retainedResidualPrefix_cost (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (T : List ℤ) (hT : T = (chargedResidualWeights P j u v R).1) (z : ℕ) :
    (readPrefixConstruction (fun i : Fin (pairAllowed u v).card =>
      storedIntegerRead T i.val) z).2 ≤ m j*(m j+9)+2 := by
  have hc : (pairAllowed u v).card ≤ m j := by simpa using Finset.card_le_univ (pairAllowed u v)
  have hh := readPrefixConstruction_cost
    (fun i : Fin (pairAllowed u v).card => storedIntegerRead T i.val) z (m j+1)
    (fun i => storedResidualRead_cost P j u v R T hT i.val)
  exact hh.trans (by nlinarith)

end MOR34
