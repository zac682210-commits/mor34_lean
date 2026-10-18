import MOR34.TracedListConstruction
import MOR34.ForcedConstructionCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def residualIndexList {s : ℕ} (u v : Fin s) : List (Fin s) :=
  (List.finRange s).filter (fun i => decide (i ≠ u ∧ i ≠ v))

theorem residualIndexList_finset {s : ℕ} (u v : Fin s) :
    (residualIndexList u v).toFinset = pairAllowed u v := by
  ext i
  simp [residualIndexList, pairAllowed, and_comm]

theorem residualIndexList_sorted {s : ℕ} (u v : Fin s) :
    residualIndexList u v = (pairAllowed u v).sort (· ≤ ·) := by
  have hn : (residualIndexList u v).Nodup := (List.nodup_finRange s).filter _
  have hs : (residualIndexList u v).Sorted (· ≤ ·) :=
    (List.pairwise_le_finRange s).filter _
  have he := (List.toFinset_sort (· ≤ ·) hn).mpr hs
  rw [residualIndexList_finset] at he
  exact he.symm

theorem residualIndexList_length {s : ℕ} (u v : Fin s) :
    (residualIndexList u v).length = (pairAllowed u v).card := by
  rw [residualIndexList_sorted, Finset.length_sort]

/-- Enumerate the whole class, reject the two indices, and read the retained
weights from an existing input table. readCost is a single stored-table access. -/
def chargedResidualWeights (P : Model m) (j : Fin q) (u v : Fin (m j)) (readCost : ℕ) :
    List ℤ × ℕ :=
  let indices := chargedFilter (fun i : Fin (m j) => (decide (i ≠ u ∧ i ≠ v),2))
    (List.finRange (m j))
  let weights := chargedMap (fun i => (P.weight ⟨j,i⟩,readCost)) indices.1
  (weights.1,indices.2+weights.2+m j+1)

theorem chargedResidualWeights_value (P : Model m) (j : Fin q)
    (u v : Fin (m j)) (R : ℕ) :
    (chargedResidualWeights P j u v R).1 =
      ((pairAllowed u v).sort (· ≤ ·)).map (fun i => P.weight ⟨j,i⟩) := by
  simp only [chargedResidualWeights, chargedMap_value, chargedFilter_value]
  rw [show (List.finRange (m j)).filter (fun i => decide (i ≠ u ∧ i ≠ v)) =
    (pairAllowed u v).sort (· ≤ ·) from residualIndexList_sorted u v]

theorem chargedResidualWeights_length (P : Model m) (j : Fin q)
    (u v : Fin (m j)) (R : ℕ) :
    (chargedResidualWeights P j u v R).1.length = (pairAllowed u v).card := by
  rw [chargedResidualWeights_value, List.length_map, Finset.length_sort]

/-- This exposes the constructed list as the same finite function used by all
existing forced-row proofs. The reindexing is no longer an unexplained atom. -/
def builtResidualWeight (P : Model m) (j : Fin q) (u v : Fin (m j))
    (R : ℕ) (i : Fin (pairAllowed u v).card) : ℤ :=
  (chargedResidualWeights P j u v R).1[i.val]'(by
    rw [chargedResidualWeights_length]; exact i.isLt)

theorem builtResidualWeight_eq (P : Model m) (j : Fin q)
    (u v : Fin (m j)) (R : ℕ) (i : Fin (pairAllowed u v).card) :
    builtResidualWeight P j u v R i = forcedResidualWeights P j u v i := by
  simp [builtResidualWeight, chargedResidualWeights_value, forcedResidualWeights,
    Finset.orderEmbOfFin_apply]

theorem chargedResidualWeights_cost (P : Model m) (j : Fin q)
    (u v : Fin (m j)) (R : ℕ) :
    (chargedResidualWeights P j u v R).2 ≤ m j*(R+5)+1 := by
  have hf := chargedFilter_cost (fun i : Fin (m j) => (decide (i ≠ u ∧ i ≠ v),2))
    (List.finRange (m j)) 2 (fun _ _ => le_rfl)
  have hl : (chargedFilter (fun i : Fin (m j) => (decide (i ≠ u ∧ i ≠ v),2))
      (List.finRange (m j))).1.length ≤ m j := by
    rw [chargedFilter_value]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange _)
  have hm := chargedMap_cost (fun i : Fin (m j) => (P.weight ⟨j,i⟩,R))
    (chargedFilter (fun i : Fin (m j) => (decide (i ≠ u ∧ i ≠ v),2))
      (List.finRange (m j))).1 R (fun _ _ => le_rfl)
  have hm' := hm.trans (Nat.mul_le_mul_right (R+1) hl)
  simp only [List.length_finRange] at hf
  unfold chargedResidualWeights
  nlinarith

theorem residual_table_polynomial_work (P : Model m) (j : Fin q)
    (u v : Fin (m j)) (n R : ℕ) (hm : m j ≤ n) (hR : R ≤ n+1) :
    (chargedResidualWeights P j u v R).2 ≤ 8*(n+1)^2 := by
  have hh := chargedResidualWeights_cost P j u v R
  have hb := Nat.mul_le_mul hm (show R+5 ≤ n+6 by omega)
  nlinarith

end MOR34
