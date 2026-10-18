import MOR34.WeightedRequestPolynomial
import MOR34.DenseCellCost

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem forms_cell_query_literals (l h : Counts q) (mode : CellMode q) (n M : ℕ)
    (hM : 1 ≤ M) (hl : ∀ j, l j ≤ n+1) (hh : ∀ j, h j ≤ n+1)
    (forms : List (IntegerForm q)) (hf : FormsBounded forms (n+1))
    (t : IntegerQuery q) (ht : t ∈ outsideQueries forms) :
    ∀ u ∈ t::cellQueries l h mode,
      (∀ j, (u.coefficient j).natAbs ≤ uniformRowRadius q (n+1) M) ∧
      u.bound.natAbs ≤ uniformRowRadius q (n+1) M := by
  have hquery := forms_cell_queries_bound l h mode (n+1) hl hh forms hf t ht
  have hR := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hcoef : normalCoefficientBound q (n+1)+1 ≤ (uniformRowRadius q (n+1) M : ℤ) := by
    rw [← normalRadius_cast]
    exact_mod_cast (show normalRadius q (n+1)+1 ≤ uniformRowRadius q (n+1) M by omega)
  have hbound : ((n+1 : ℕ) : ℤ)+normalCoefficientBound q (n+1)+3 ≤
      (uniformRowRadius q (n+1) M : ℤ) := by
    rw [← normalRadius_cast]
    exact_mod_cast (show (n+1)+normalRadius q (n+1)+3 ≤ uniformRowRadius q (n+1) M by omega)
  intro u hu
  have hx := hquery u hu
  refine ⟨fun j => ?_,?_⟩
  · have h := (hx.1 j).trans hcoef
    exact_mod_cast (show ((u.coefficient j).natAbs : ℤ) ≤ (uniformRowRadius q (n+1) M : ℤ) by simpa using h)
  · have h := hx.2.trans hbound
    exact_mod_cast (show (u.bound.natAbs : ℤ) ≤ (uniformRowRadius q (n+1) M : ℤ) by simpa using h)

/-- The bit-priced compiler is bounded on every reached cell state. The normal
and endpoint literal hypotheses are discharged from containment, not supplied
as an additional caller obligation. -/
theorem weightedReachedCellRequests_polynomial (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (R M L H a : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (hc : ∀ j, (P.coefficient j).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (2000*(Fintype.card (Item m)+L+2)^4)
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a))
    (ε : Parity q) (e : ParityExtrema P ε) (mode : CellMode q) :
    SearchStates
      (linearSpanOracle (rowCellOracle (denseCountOracle P R solve) ε e mode) computedCountForms)
      (fun B => ∀ t ∈ outsideQueries (computedCountForms B),
        (weightedCompiledCountRequest A P ε (t::cellQueries e.low e.high mode) R).2 ≤
          (144*H*2000^a+1260)*(Fintype.card (Item m)+L+2)^(4*a+4)) (q+1) ∅ := by
  have hor := linearSpanOracle_spec (parityCellSet P ε e mode)
    (rowCellOracle (denseCountOracle P R solve) ε e mode)
    (rowCellOracle_spec P hWF _ (denseCountOracle_spec P R solve hs) ε e mode)
    computedCountForms computedCountForms_spec
  apply searchStates_of_containment (parityCellSet P ε e mode) _ (fun B z hz => (hor.found B z hz).1)
  · intro B hB t ht
    apply weightedCompiledCountRequest_polynomial P hWF ε _ R M L H a hR
      (by rw [List.length_cons,cellQueries_length]) hM hML hw hc hr hcap _ A hA
    apply forms_cell_query_literals e.low e.high mode (Fintype.card (Item m)) M hM
    · intro j
      rw [← e.lower_eq j]
      exact ((e.lower_mem j).1 j).trans ((class_size_le_items j).trans (Nat.le_succ _))
    · intro j
      rw [← e.upper_eq j]
      exact ((e.upper_mem j).1 j).trans ((class_size_le_items j).trans (Nat.le_succ _))
    · exact computedCountForms_bound B _ (by omega)
        (fun z hz j => ((hB hz).1.1 j).trans ((class_size_le_items j).trans (Nat.le_succ _)))
    · exact ht
  · simp

end MOR34
