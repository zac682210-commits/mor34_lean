import MOR34.ResidualTableConstruction

namespace MOR34

/-- A linear stored-list read charges every visited cell, including a miss. -/
def chargedListRead {α : Type*} : List α → ℕ → Option α × ℕ
  | [],_ => (none,1)
  | a::_,0 => (some a,1)
  | _::L,i+1 => let out := chargedListRead L i; (out.1,out.2+1)

theorem chargedListRead_value {α : Type*} (L : List α) (i : ℕ) :
    (chargedListRead L i).1 = L[i]? := by
  induction L generalizing i with
  | nil => simp [chargedListRead]
  | cons a L ih => cases i <;> simp [chargedListRead, ih]

theorem chargedListRead_cost {α : Type*} (L : List α) (i : ℕ) :
    (chargedListRead L i).2 ≤ L.length+1 := by
  induction L generalizing i with
  | nil => simp [chargedListRead]
  | cons a L ih =>
      cases i with
      | zero => simp [chargedListRead]
      | succ i => simpa [chargedListRead] using Nat.add_le_add_right (ih i) 1

/-- The residual table is supplied as retained data, not rebuilt at each read. -/
theorem storedResidualRead_value {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) (T : List ℤ)
    (hT : T = (chargedResidualWeights P j u v R).1)
    (i : Fin (pairAllowed u v).card) :
    (chargedListRead T i.val).1 = some (forcedResidualWeights P j u v i) := by
  subst T
  rw [chargedListRead_value]
  have hi : i.val < (chargedResidualWeights P j u v R).1.length := by
    rw [chargedResidualWeights_length]; exact i.isLt
  rw [List.getElem?_eq_getElem hi]
  exact congrArg some (builtResidualWeight_eq P j u v R i)

theorem storedResidualRead_cost {q : ℕ} {m : Fin q → ℕ} (P : Model m)
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) (T : List ℤ)
    (hT : T = (chargedResidualWeights P j u v R).1) (i : ℕ) :
    (chargedListRead T i).2 ≤ m j+1 := by
  have hh := chargedListRead_cost T i
  rw [hT, chargedResidualWeights_length] at hh
  have hc : (pairAllowed u v).card ≤ m j := by simpa using Finset.card_le_univ (pairAllowed u v)
  omega

/-- Full-range filtering is a deliberately simple polynomial implementation of
prefix indices. It does not call a sorting oracle. -/
def prefixIndexList (n z : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (i.val < z))

theorem prefixIndexList_sorted (n z : ℕ) :
    prefixIndexList n z = (classPrefix n z).sort (· ≤ ·) := by
  have hn : (prefixIndexList n z).Nodup := (List.nodup_finRange n).filter _
  have hs : (prefixIndexList n z).Sorted (· ≤ ·) := (List.pairwise_le_finRange n).filter _
  have he := (List.toFinset_sort (· ≤ ·) hn).mpr hs
  have hf : (prefixIndexList n z).toFinset = classPrefix n z := by
    ext i
    simp [prefixIndexList, classPrefix]
  rw [hf] at he
  exact he.symm

/-- Construct the prefix expression from input/stored weights, charging index
creation, filtering, reads, list storage, and expression-node allocation. -/
def chargedPrefixConstruction {n : ℕ} (w : Fin n → ℤ) (z R : ℕ) :
    IntegerConstruction × ℕ :=
  let indices := chargedFilter (fun i : Fin n => (decide (i.val < z),1)) (List.finRange n)
  let weights := chargedMap (fun i => (w i,R)) indices.1
  (sumConstruction weights.1, indices.2+weights.2+n+1+2*weights.1.length+1)

theorem chargedPrefixConstruction_value {n : ℕ} (w : Fin n → ℤ) (z R : ℕ) :
    (chargedPrefixConstruction w z R).1 = prefixConstruction w z := by
  simp only [chargedPrefixConstruction, chargedFilter_value, chargedMap_value, prefixConstruction]
  rw [show (List.finRange n).filter (fun i => decide (i.val < z)) =
    (classPrefix n z).sort (· ≤ ·) from prefixIndexList_sorted n z]

theorem chargedPrefixConstruction_interpret {n : ℕ} (w : Fin n → ℤ) (z R : ℕ) :
    (chargedPrefixConstruction w z R).1.value = prefixCost w z := by
  rw [chargedPrefixConstruction_value, prefixConstruction_value]

theorem chargedPrefixConstruction_cost {n : ℕ} (w : Fin n → ℤ) (z R : ℕ) :
    (chargedPrefixConstruction w z R).2 ≤ n*(R+8)+2 := by
  have hf := chargedFilter_cost (fun i : Fin n => (decide (i.val < z),1))
    (List.finRange n) 1 (fun _ _ => le_rfl)
  have hl : (chargedFilter (fun i : Fin n => (decide (i.val < z),1))
      (List.finRange n)).1.length ≤ n := by
    rw [chargedFilter_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hm := chargedMap_cost (fun i : Fin n => (w i,R))
    (chargedFilter (fun i : Fin n => (decide (i.val < z),1)) (List.finRange n)).1 R
    (fun _ _ => le_rfl)
  have hm' := hm.trans (Nat.mul_le_mul_right (R+1) hl)
  simp only [List.length_finRange] at hf
  simp only [chargedPrefixConstruction, chargedMap_value, List.length_map]
  nlinarith

end MOR34
