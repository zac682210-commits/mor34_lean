import MOR34.CountRowBounds

namespace MOR34
variable {q : ℕ}

theorem integerQuery_bound_mono (a : IntegerQuery q) {C D C' D' : ℤ}
    (h : a.Bounded C D) (hC : C ≤ C') (hD : D ≤ D') : a.Bounded C' D' :=
  ⟨fun j => (h.1 j).trans hC, h.2.trans hD⟩

theorem coordinateLower_bound (j : Fin q) (k N : ℕ) (hk : k ≤ N) :
    (coordinateLower j k).Bounded 1 N := by
  constructor
  · intro i
    dsimp [coordinateLower]
    split_ifs <;> norm_num
  · simpa [coordinateLower] using (show (k : ℤ) ≤ N by exact_mod_cast hk)

theorem coordinateUpper_bound (j : Fin q) (b D : ℤ) (hb : |b| ≤ D) :
    (coordinateUpper j b).Bounded 1 D := by
  constructor
  · intro i
    dsimp [coordinateUpper]
    split_ifs <;> norm_num
  · exact hb

theorem cellCoordinateQueries_bound (l h : Counts q) (mode : CellMode q) (N : ℕ)
    (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N) (j : Fin q) :
    ∀ a ∈ cellCoordinateQueries l h mode j, a.Bounded 1 ((N : ℤ)+2) := by
  have hlow : cellLow l h mode j ≤ N+2 := by
    unfold cellLow
    split_ifs <;> have := hl j <;> have := hh j <;> omega
  have hupper : |cellUpperInteger l h mode j| ≤ (N : ℤ)+2 := by
    have hl' : (l j : ℤ) ≤ N := by exact_mod_cast hl j
    have hh' : (h j : ℤ) ≤ N := by exact_mod_cast hh j
    unfold cellUpperInteger
    split_ifs <;> apply abs_le.mpr <;> constructor <;> omega
  have hguard : (cellGuard l h mode j).Bounded 1 ((N : ℤ)+2) := by
    constructor
    · intro i; simp [cellGuard]
    · have hl' : (l j : ℤ) ≤ N := by exact_mod_cast hl j
      have hh' : (h j : ℤ) ≤ N := by exact_mod_cast hh j
      dsimp [cellGuard]
      split_ifs <;> apply abs_le.mpr <;> constructor <;> omega
  intro a ha
  simp only [cellCoordinateQueries, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using coordinateLower_bound j _ (N+2) hlow
  · exact coordinateUpper_bound j _ _ hupper
  · exact hguard

theorem cellQueries_bound (l h : Counts q) (mode : CellMode q) (N : ℕ)
    (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N) :
    ∀ a ∈ cellQueries l h mode, a.Bounded 1 ((N : ℤ)+2) := by
  intro a ha
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp ha
  exact cellCoordinateQueries_bound l h mode N hl hh j a hj

/-- A strict separating row is appended to all three cell rows per coordinate. -/
theorem cell_normal_queries_bound (l h : Counts q) (mode : CellMode q) (N : ℕ)
    (hN : 1 ≤ N) (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N)
    (B : Finset (Counts q)) (hB : ∀ z ∈ B, ∀ j, z j ≤ N)
    (a : IntegerQuery q) (ha : a ∈ outsideQueries (boundedCountForms B)) :
    ∀ t ∈ a :: cellQueries l h mode,
      t.Bounded (normalCoefficientBound q N + 1) ((N : ℤ) + normalCoefficientBound q N + 3) := by
  have hH : (0 : ℤ) ≤ normalCoefficientBound q N := by unfold normalCoefficientBound; positivity
  intro t ht
  rcases List.mem_cons.mp ht with he | ht
  · subst t
    exact integerQuery_bound_mono a (boundedCountQueries_bound B N hN hB a ha) (by omega) (by omega)
  · exact integerQuery_bound_mono t (cellQueries_bound l h mode N hl hh t ht) (by omega) (by omega)

/-- Coefficient control for the exact scalar query supplied by a cell-span search. -/
theorem cell_normal_parity_rows_bounded {m : Fin q → ℕ} (P : Model m)
    (N : ℕ) (M : ℤ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ M) (hc : ∀ j, |P.coefficient j| ≤ M)
    (hb : |P.capacity| ≤ M) (hd : |P.rhs| ≤ M)
    (l h : Counts q) (mode : CellMode q) (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N)
    (B : Finset (Counts q)) (hB : ∀ z ∈ B, ∀ j, z j ≤ N)
    (a : IntegerQuery q) (ha : a ∈ outsideQueries (boundedCountForms B)) (ε : Parity q)
    (k : CountRow m (a :: cellQueries l h mode).length) :
    ((countRow P (queryCoefficients (a :: cellQueries l h mode))
      (queryBounds (a :: cellQueries l h mode)) k).withParity ε).IntegerBounded
      (2 * (M + (normalCoefficientBound q N + 1) + 1)) 1
      (rowConstantBound N M ((N : ℤ) + normalCoefficientBound q N + 3) +
        q * (M + (normalCoefficientBound q N + 1) + 1)) := by
  apply parityRows_integer_bounded P N M _ _ hM
  · unfold normalCoefficientBound; positivity
  · unfold normalCoefficientBound; positivity
  · exact hm
  · exact hw
  · exact hc
  · exact hb
  · exact hd
  · exact cell_normal_queries_bound l h mode N hN hl hh B hB a ha

end MOR34
