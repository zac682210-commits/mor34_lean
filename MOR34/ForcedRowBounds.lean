import MOR34.CountRowBounds

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem forcedOrdinaryRow_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N) (hw : ∀ i, |P.weight i| ≤ M)
    (j k : Fin q) (t : Fin (m k)) :
    (forcedOrdinaryRow P j k t).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  have hM0 : 0 ≤ M := by omega
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hprod : 0 ≤ (2 * (N : ℤ)) * M := mul_nonneg (by positivity) hM0
  by_cases hk : k = j
  · rw [forcedOrdinaryRow, if_pos hk]
    apply integerRow_bounded
    · intro i; simp; omega
    · simp
    · simp only [abs_zero]; unfold rowConstantBound; nlinarith [hprod]
  · rw [forcedOrdinaryRow, if_neg hk]
    apply integerRow_bounded
    · exact integerPick_abs_bound k _ _ (by omega) ((hw _).trans (by omega))
    · exact integerPick_abs_bound k _ _ (by norm_num) (by norm_num)
    · have ht := prefixIntercept_abs_bound (fun u => P.weight ⟨k, u⟩) M hM0 (fun u => hw ⟨k, u⟩) t
      have hm' : (m k : ℤ) ≤ N := by exact_mod_cast hm k
      unfold rowConstantBound
      nlinarith

theorem forcedSlopeRow_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N) (hw : ∀ i, |P.weight i| ≤ M)
    (j : Fin q) (u v : Fin (m j)) (t : Fin (pairAllowed u v).card) :
    (forcedSlopeRow P j u v t).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  have hM0 : 0 ≤ M := by omega
  have hw' : ∀ i, |forcedResidualWeights P j u v i| ≤ M := fun i => hw _
  have hs : (pairAllowed u v).card ≤ N :=
    (by simpa using Finset.card_le_univ (pairAllowed u v) : (pairAllowed u v).card ≤ m j).trans (hm j)
  unfold forcedSlopeRow
  apply integerRow_bounded
  · exact integerPick_abs_bound j _ _ (by omega) ((hw' t).trans (by omega))
  · exact integerPick_abs_bound j _ _ (by norm_num) (by norm_num)
  · have ht := shiftedPrefixIntercept_abs_bound (forcedResidualWeights P j u v) (P.weight ⟨j, v⟩) M
      hM0 hw' (hw _) t
    have hs' : ((pairAllowed u v).card : ℤ) ≤ N := by exact_mod_cast hs
    have hN0 : (0 : ℤ) ≤ N := by positivity
    unfold rowConstantBound
    nlinarith

theorem forcedEmptyRow_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hw : ∀ i, |P.weight i| ≤ M)
    (j : Fin q) (u v : Fin (m j)) :
    (forcedEmptyRow P j u v).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  have hM0 : 0 ≤ M := by omega
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hprod : 0 ≤ (2 * (N : ℤ)) * M := mul_nonneg (by positivity) hM0
  have hRM : M ≤ rowConstantBound N M 0 := by unfold rowConstantBound; nlinarith [hprod]
  by_cases he : (pairAllowed u v).card = 0
  · rw [forcedEmptyRow, if_pos he]
    apply integerRow_bounded
    · intro i; simp; omega
    · exact integerPick_abs_bound j _ _ (by norm_num) (by norm_num)
    · simpa using (hw ⟨j, v⟩).trans hRM
  · rw [forcedEmptyRow, if_neg he]
    apply integerRow_bounded
    · intro i; simp; omega
    · simp
    · simp only [abs_zero]; omega

theorem forcedRows_integer_bounded (P : Model m) (N : ℕ) (M : ℤ)
    (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M)
    (j : Fin q) (u v : Fin (m j)) (k : ForcedRow m j u v) :
    (forcedRow P j u v k).IntegerBounded (M+1) 1 (rowConstantBound N M 0) := by
  have hM0 : 0 ≤ M := by omega
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hprod : 0 ≤ (2 * (N : ℤ)) * M := mul_nonneg (by positivity) hM0
  have hRM : M ≤ rowConstantBound N M 0 := by unfold rowConstantBound; nlinarith [hprod]
  have hRN : (N : ℤ)+1 ≤ rowConstantBound N M 0 := by unfold rowConstantBound; nlinarith [hprod]
  have h0 : 0 ≤ rowConstantBound N M 0 := by omega
  rcases k with ((k | k) | (b | b)) | (⟨k, t⟩ | (t | (w | w)))
  · exact integerRow_bounded _ _ _ _ _ _
      (integerPick_abs_bound k _ _ (by omega) (by norm_num; omega)) (by simp) (by simpa using h0)
  · apply integerRow_bounded
    · exact integerPick_abs_bound k _ _ (by omega) (by norm_num; omega)
    · simp
    · have hm' : (m k : ℤ) ≤ N := by exact_mod_cast hm k
      rw [abs_of_nonneg (by positivity)]; omega
  · dsimp only [forcedRow]
    split_ifs with h
    · exact integerRow_bounded _ _ _ _ _ _ (fun k => (hc k).trans (by omega)) (by simp) (hd.trans hRM)
    · exact integerRow_bounded _ _ _ _ _ _
        (fun k => by simpa using (hc k).trans (show M ≤ M+1 by omega)) (by simp) (by simpa using hd.trans hRM)
  · dsimp only [forcedRow]
    split_ifs with h
    · exact integerRow_bounded _ _ _ _ _ _
        (integerPick_abs_bound j _ _ (by omega) (by norm_num; omega)) (by simp) (by norm_num; omega)
    · apply integerRow_bounded
      · exact integerPick_abs_bound j _ _ (by omega) (by norm_num; omega)
      · simp
      · have hm' : (m j : ℤ) ≤ N := by exact_mod_cast hm j
        apply abs_le.mpr
        constructor <;> omega
  · exact forcedOrdinaryRow_integer_bounded P N M hM hm hw j k t
  · exact forcedSlopeRow_integer_bounded P N M hM hm hw j u v t
  · exact forcedEmptyRow_integer_bounded P N M hM hw j u v
  · exact integerRow_bounded _ _ _ _ _ _ (by intro k; simp; omega) (by simp) (hb.trans hRM)

end MOR34
