import MOR34.WeightedRowEvaluation

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

/- These applications discharge the row-work and literal premises from original
input magnitudes and the actual constructor. Query literals are stated only for
the extra count rows; normal-search callers must supply their proved bound. -/

theorem weightedCountRow_polynomial (P : Model m) (Q : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (n L M H a : ℕ) (hq : q ≤ n) (hm : ∀ i, m i ≤ n)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M)
    (hc : ∀ i, (P.coefficient i).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (hQ : ∀ i j, (Q i j).natAbs ≤ uniformRowRadius q (n+1) M)
    (hb : ∀ i, (b i).natAbs ≤ uniformRowRadius q (n+1) M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (170*(n+L+2)^3) (H*(170*(n+L+2)^3)^a)) (k : CountRow m r) :
    (weightedEvaluateRow A (countRowConstruction P Q b k)).2 ≤
      (12*H*170^a+5)*(n+L+2)^(3*a+1) := by
  have hd := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hm' : ∀ i, m i ≤ uniformRowRadius q (n+1) M := fun i => by
    have hi := hm i
    omega
  have hMR : M ≤ uniformRowRadius q (n+1) M := by omega
  have hw' := fun i => (hw i).trans hMR
  have hc' := fun i => (hc i).trans hMR
  apply weightedEvaluateRow_polynomial A _ n L M H a hq hML
  · have hh := countRowConstruction_work P Q b n hm k
    omega
  · exact countRowConstruction_literals P Q b (uniformRowRadius q (n+1) M) (by omega)
      hm' hw' hc' (hr.trans hMR) (hcap.trans hMR) hQ hb k
  · exact hA

theorem weightedForcedRow_polynomial (P : Model m) (j : Fin q) (u v : Fin (m j))
    (n L M H a : ℕ) (hq : q ≤ n) (hm : ∀ i, m i ≤ n)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M)
    (hc : ∀ i, (P.coefficient i).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (170*(n+L+2)^3) (H*(170*(n+L+2)^3)^a)) (k : ForcedRow m j u v) :
    (weightedEvaluateRow A (forcedRowConstruction P j u v k)).2 ≤
      (12*H*170^a+5)*(n+L+2)^(3*a+1) := by
  have hd := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hm' : ∀ i, m i ≤ uniformRowRadius q (n+1) M := fun i => by
    have hi := hm i
    omega
  have hMR : M ≤ uniformRowRadius q (n+1) M := by omega
  have hw' := fun i => (hw i).trans hMR
  have hc' := fun i => (hc i).trans hMR
  apply weightedEvaluateRow_polynomial A _ n L M H a hq hML
  · have hh := forcedRowConstruction_work P j u v n hm k
    omega
  · exact forcedRowConstruction_literals P j u v (uniformRowRadius q (n+1) M) (by omega)
      hm' hw' hc' (hr.trans hMR) (hcap.trans hMR) k
  · exact hA

theorem weightedViolationRow_polynomial (P : Model m) 
    (n L M H a : ℕ) (hq : q ≤ n) (hm : ∀ i, m i ≤ n)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M)
    (hc : ∀ i, (P.coefficient i).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (170*(n+L+2)^3) (H*(170*(n+L+2)^3)^a)) (k : ViolationRow m) :
    (weightedEvaluateRow A (violationRowConstruction P k)).2 ≤
      (12*H*170^a+5)*(n+L+2)^(3*a+1) := by
  have hd := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hm' : ∀ i, m i ≤ uniformRowRadius q (n+1) M := fun i => by
    have hi := hm i
    omega
  have hMR : M ≤ uniformRowRadius q (n+1) M := by omega
  have hw' := fun i => (hw i).trans hMR
  have hc' := fun i => (hc i).trans hMR
  apply weightedEvaluateRow_polynomial A _ n L M H a hq hML
  · have hh := violationRowConstruction_work P n hm k
    omega
  · exact violationRowConstruction_literals P (uniformRowRadius q (n+1) M) (by omega)
      hm' hw' hc' (hr.trans hMR) (hcap.trans hMR) k
  · exact hA

end MOR34
