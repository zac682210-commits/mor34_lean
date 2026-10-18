import MOR34.DenseCellCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- The actual dense input bound for any bounded list of base/count queries,
including support and coordinate-extremum calls outside the cell recursion. -/
theorem boundedCountRequest_payload (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (Q : List (IntegerQuery q)) (R : ℕ) (hQ : Q.length ≤ 3*q+1)
    (hqueries : ∀ t ∈ Q, t.Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3)) :
    (((compiledCountRequest P ε Q R).1).map DenseIntegerRow.payload).sum ≤
      168*(Fintype.card (Item m)+L+2)^4 := by
  let N := Fintype.card (Item m)+1
  have hq := coefficient_classes_le_items P hWF
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hrows := parityRows_integer_bounded P N M
    (normalCoefficientBound q N+1) ((N : ℤ)+normalCoefficientBound q N+3)
    hM' (by unfold normalCoefficientBound; positivity)
    (by unfold normalCoefficientBound; positivity)
    (fun j => (class_size_le_items j).trans (Nat.le_succ _)) hw hc hb hd Q hqueries ε
  obtain ⟨a,b,d,he,hbits⟩ := uniform_system_payload
    (fun k : CountRow m Q.length =>
      (countRow P (queryCoefficients Q) (queryBounds Q) k).withParity ε)
    N M (by dsimp [N]; omega)
    (fun k => cellRow_uniform_bound _ N M (by dsimp [N]; omega) hM
      (by dsimp [N]; omega) (hrows k))
  rw [compiledCountRequest_payload P ε Q R a b d he]
  apply hbits.trans
  rw [countRow_card]
  exact dense_query_payload_polynomial q (Fintype.card (Item m)) M L _ hq hML (by omega)

theorem boundedCountSolver_cost (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (Q : List (IntegerQuery q)) (R I c : ℕ) (hQ : Q.length ≤ 3*q+1)
    (hqueries : ∀ t ∈ Q, t.Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3))
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hcost : DenseSolverCostBound solve I c) :
    (solve (compiledCountRequest P ε Q R).1).2 ≤
      I*(180*(Fintype.card (Item m)+L+2)^4)^c := by
  have hq := coefficient_classes_le_items P hWF
  have hsize := denseProblemSize_polynomial (compiledCountRequest P ε Q R).1
    (Fintype.card (Item m)) L hq (by rw [compiledCountRequest_length]; omega)
    (boundedCountRequest_payload P hWF M L hM hML hw hc hb hd ε Q R hQ hqueries)
  exact (hcost _ (compiledCountRequest_sized P ε Q R)).trans
    (Nat.mul_le_mul_left I (pow_le_pow_left' hsize c))

/-- Both kinds of coordinate scan use only these small signed thresholds. -/
theorem simpleQuery_normal_bound (t : IntegerQuery q) (N : ℕ)
    (h : t.Bounded 1 N) :
    t.Bounded (normalCoefficientBound q N+1) ((N : ℤ)+normalCoefficientBound q N+3) := by
  have hh : (0 : ℤ) ≤ normalCoefficientBound q N := by unfold normalCoefficientBound; positivity
  exact integerQuery_bound_mono t h (by omega) (by omega)

theorem maximumScanQuery_bound (P : Model m) (j : Fin q) (k : ℕ) (hk : k ≤ m j) :
    (coordinateLower j k).Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3) :=
  simpleQuery_normal_bound _ _ (coordinateLower_bound j k _
    (hk.trans ((class_size_le_items j).trans (Nat.le_succ _))))

theorem minimumScanQuery_bound (P : Model m) (j : Fin q) (k : ℕ) (hk : k ≤ m j) :
    (coordinateUpper j ((m j : ℤ)-(k : ℤ))).Bounded
      (normalCoefficientBound q (Fintype.card (Item m)+1)+1)
      ((Fintype.card (Item m)+1 : ℕ)+normalCoefficientBound q (Fintype.card (Item m)+1)+3) := by
  apply simpleQuery_normal_bound
  apply coordinateUpper_bound
  have hm : (m j : ℤ) ≤ Fintype.card (Item m)+1 := by
    exact_mod_cast ((class_size_le_items j).trans (Nat.le_succ _))
  have hk' : (k : ℤ) ≤ m j := by exact_mod_cast hk
  apply abs_le.mpr
  constructor <;> omega

end MOR34
