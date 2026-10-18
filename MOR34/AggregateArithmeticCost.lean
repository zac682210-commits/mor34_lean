import MOR34.NormalArithmeticCost
import MOR34.StoredEdgeWitnesses
import MOR34.ComputedRankPayload

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Sum only along nonempty parity classes, with one normal computation per
visited cell-basis state. This is the reference algorithm's cached policy. -/
noncomputable def allNormalArithmeticCharge (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) : ℕ := by
  classical
  exact ∑ ε : Parity q, if hn : ∃ z, TightParity P ε z then
    ∑ mode : CellMode q, normalBasisArithmeticCharge
      (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) (q+1) ∅
    else 0

theorem allNormalArithmeticCharge_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    allNormalArithmeticCharge P hWF solve hs ≤
      (6^q*((q+1)*((q+2)*(q+1)^(2*(q+1)))))*normalKeyBudget (q+1) := by
  classical
  unfold allNormalArithmeticCharge
  calc
    _ ≤ ∑ _ε : Parity q, ∑ _mode : CellMode q,
        (q+1)*(((q+2)*(q+1)^(2*(q+1)))*normalKeyBudget (q+1)) := by
      apply Finset.sum_le_sum
      intro ε _
      split_ifs with hn
      · exact Finset.sum_le_sum (fun mode _ => normalBasisArithmeticCharge_bound _ _ _ (by simp))
      · exact Nat.zero_le _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.nsmul_eq_mul, Parity, CellMode]
      rw [show (6:ℕ)=2*3 from rfl, mul_pow]
      ring

/-- Each of the finitely many normal-check charges has a factorial parameter bound. -/
theorem normalKeyBudget_factorial_bound (d : ℕ) :
    normalKeyBudget d ≤ 4*(d+3)^5*(d.factorial+2) := by
  have hb : 1 ≤ d+3 := by omega
  have h2 : d^2+1 ≤ (d+3)^2 := by nlinarith
  have hD : (d+3)^2*d.factorial+1 ≤ (d+3)^2*(d.factorial+2) := by nlinarith
  have hD' : (d+3)^2*d.factorial+2 ≤ (d+3)^2*(d.factorial+2) := by nlinarith
  have h₁ : d^2+1 ≤ (d+3)^5*(d.factorial+2) := by
    exact h2.trans ((pow_le_pow_right' hb (by decide : 2 ≤ 5)).trans
      (Nat.le_mul_of_pos_right _ (by omega)))
  have h₂ : (d+3)^2*d.factorial+1 ≤ (d+3)^5*(d.factorial+2) :=
    hD.trans (Nat.mul_le_mul_right _ (pow_le_pow_right' hb (by decide : 2 ≤ 5)))
  have h₃ : d*d*((d+1)*((d+3)^2*d.factorial+2)) ≤ (d+3)^5*(d.factorial+2) := by
    calc
      _ ≤ (d+3)^2*((d+3)*((d+3)^2*(d.factorial+2))) :=
        Nat.mul_le_mul (by nlinarith) (Nat.mul_le_mul (by omega) hD')
      _ = _ := by ring
  have h₄ : d*d*(2*d+1) ≤ (d+3)^5*(d.factorial+2) := by
    have hh : d*d*(2*d+1) ≤ (d+3)^4 := by nlinarith
    exact hh.trans ((pow_le_pow_right' hb (by decide : 4 ≤ 5)).trans
      (Nat.le_mul_of_pos_right _ (by omega)))
  unfold normalKeyBudget
  omega

theorem normalKeyBudget_parameter_bound (d : ℕ) :
    normalKeyBudget d ≤ (d+3)^(d+8) := by
  have hb : 1 ≤ d+3 := by omega
  have hp : 1 ≤ (d+3)^d := Nat.one_le_pow _ _ hb
  have hf : d.factorial ≤ (d+3)^d :=
    (Nat.factorial_le_pow d).trans (pow_le_pow_left' (by omega) _)
  have hF : d.factorial+2 ≤ (d+3)^(d+1) := by rw [pow_succ]; nlinarith
  calc
    _ ≤ 4*(d+3)^5*(d.factorial+2) := normalKeyBudget_factorial_bound d
    _ ≤ (d+3)^2*(d+3)^5*(d+3)^(d+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by nlinarith)) hF
    _ = _ := by simp only [← pow_add]; congr 1; omega

theorem allNormalArithmeticCharge_parameter (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) :
    allNormalArithmeticCharge P hWF solve hs ≤ (q+4)^(6*q+13) := by
  calc
    _ ≤ (6^q*((q+1)*((q+2)*(q+1)^(2*(q+1)))))*normalKeyBudget (q+1) :=
      allNormalArithmeticCharge_bound P hWF solve hs
    _ ≤ (q+4)^(5*q+4)*(q+4)^(q+9) := by
      apply Nat.mul_le_mul
      · exact (normal_calls_parameter_bound q).trans (pow_le_pow_left' (by omega) _)
      · simpa only [show q+1+3=q+4 by omega, show q+1+8=q+9 by omega]
          using normalKeyBudget_parameter_bound (q+1)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The exponent depends only on externally fixed primitive exponents. -/
def chargedPhaseDegree (c e : ℕ) : ℕ := 4*c+2*e+3

/-- Charges all solver calls (including edges), the actual rank path, and normal
arithmetic. Input construction, data movement, and primitive bit costs beyond
these supplied contracts are explicitly not part of this expression. -/
noncomputable def chargedPhaseCost (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) (ranker : ExactIntegerRank m)
    (ilpUnit rankUnit arithmeticUnit : ℕ) : ℕ :=
  (rowSearchCalls P hWF solve hs computedCountForms + Fintype.card (AdjacentPair m))*ilpUnit +
  finiteBasisRankCalls (orderedBinarySets (computedReturnedSets P hWF solve hs edgeSolve he))
    (fun B => ranker.evaluate (binaryPointMatrix B)) (Fintype.card (Item m)+1) ∅*rankUnit +
  allNormalArithmeticCharge P hWF solve hs*arithmeticUnit

theorem all_solver_cost_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (forms : Finset (Counts q) → List (IntegerForm q))
    (hsize : ∀ B, (forms B).length ≤ q+1) (L I c perCall : ℕ)
    (hcost : perCall ≤ I*(168*(Fintype.card (Item m)+L+2)^4)^c) :
    (rowSearchCalls P hWF solve hs forms + Fintype.card (AdjacentPair m))*perCall ≤
      ((rowCallFactor q+1)*I*168^c)*(Fintype.card (Item m)+L+2)^(4*c+1) := by
  have hh := all_solver_calls_bound P hWF solve hs forms hsize
  calc
    _ ≤ ((rowCallFactor q+1)*(Fintype.card (Item m)+L+2))*
        (I*(168*(Fintype.card (Item m)+L+2)^4)^c) :=
      Nat.mul_le_mul (hh.trans (Nat.mul_le_mul_left _ (by omega))) hcost
    _ = _ := by rw [mul_pow, ← pow_mul, pow_succ]; ring


/-- Combining the three charged phases does not put the parameter into the
polynomial exponent. No bound on total running time is assumed here. -/
theorem chargedPhaseCost_bound (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve)
    (edgeSolve : (j : Fin q) → Fin (m j) → Fin (m j) → Option (IntegerRowSolution q))
    (he : ForcedRowSolverSpec P edgeSolve) (ranker : ExactIntegerRank m)
    (L I R H c e a ilpUnit rankUnit arithmeticUnit : ℕ)
    (hi : ilpUnit ≤ I*(168*(Fintype.card (Item m)+L+2)^4)^c)
    (hr : rankUnit ≤ R*(2*(Fintype.card (Item m)+2)^2)^e)
    (ha : arithmeticUnit ≤ H*(Fintype.card (Item m)+L+2)^a) :
    chargedPhaseCost P hWF solve hs edgeSolve he ranker ilpUnit rankUnit arithmeticUnit ≤
      (((rowCallFactor q+1)*I*168^c) + (2*((q+1)*6^q+2)*R*2^e) +
        (q+4)^(6*q+13)*H) * (Fintype.card (Item m)+L+2)^(chargedPhaseDegree c e+a) := by
  let t := Fintype.card (Item m)+L+2
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hI := all_solver_cost_bound P hWF solve hs computedCountForms
    (fun B => (computedCountForms_length B).le) L I c ilpUnit hi
  have hR := counted_rank_cost_bound P hWF solve hs edgeSolve he ranker R e rankUnit hr
  have hN := Nat.mul_le_mul (allNormalArithmeticCharge_parameter P hWF solve hs) ha
  have hpowI : t^(4*c+1) ≤ t^(chargedPhaseDegree c e+a) :=
    pow_le_pow_right' ht (by unfold chargedPhaseDegree; omega)
  have hpowR : (Fintype.card (Item m)+2)^(2*e+2) ≤ t^(chargedPhaseDegree c e+a) :=
    (pow_le_pow_left' (by dsimp [t]; omega) _).trans
      (pow_le_pow_right' ht (by unfold chargedPhaseDegree; omega))
  have hpowN : t^a ≤ t^(chargedPhaseDegree c e+a) :=
    pow_le_pow_right' ht (by unfold chargedPhaseDegree; omega)
  have hI' := hI.trans (Nat.mul_le_mul_left _ hpowI)
  have hR' := hR.trans (Nat.mul_le_mul_left _ hpowR)
  have hN' : allNormalArithmeticCharge P hWF solve hs*arithmeticUnit ≤
      ((q+4)^(6*q+13)*H)*t^(chargedPhaseDegree c e+a) := by
    calc
      _ ≤ (q+4)^(6*q+13)*(H*t^a) := hN
      _ = ((q+4)^(6*q+13)*H)*t^a := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpowN
  unfold chargedPhaseCost
  calc
    _ ≤ (((rowCallFactor q+1)*I*168^c)*t^(chargedPhaseDegree c e+a)) +
        ((2*((q+1)*6^q+2)*R*2^e)*t^(chargedPhaseDegree c e+a)) +
        (((q+4)^(6*q+13)*H)*t^(chargedPhaseDegree c e+a)) :=
      Nat.add_le_add (Nat.add_le_add hI' hR') hN'
    _ = _ := by ring

end MOR34
