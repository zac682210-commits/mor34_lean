import MOR34.CompleteWeightedApplication
import MOR34.EnumerationParameterBound

namespace MOR34

/-- A concrete q^{O(q)} envelope, including q=0 without conventions. -/
def ParameterGrowth (f : ℕ → ℕ) : Prop := ∃ C : ℕ, ∀ q, f q ≤ (q+6)^(C*(q+1))

theorem parameterGrowth_mono {f g : ℕ → ℕ} (h : ∀ q, f q ≤ g q)
    (hg : ParameterGrowth g) : ParameterGrowth f := by
  obtain ⟨C,hg⟩ := hg
  exact ⟨C,fun q => (h q).trans (hg q)⟩

theorem parameterGrowth_constant (v : ℕ) : ParameterGrowth (fun _ => v) := by
  refine ⟨v,fun q => ?_⟩
  exact (Nat.le_of_lt (show v < 2^v from Nat.lt_two_pow_self)).trans
    ((pow_le_pow_left' (by omega : 2 ≤ q+6) v).trans
      (pow_le_pow_right' (by omega) (by nlinarith : v ≤ v*(q+1))))

theorem parameterGrowth_q : ParameterGrowth (fun q => q) := by
  refine ⟨1,fun q => ?_⟩
  simpa only [one_mul] using (show q ≤ q+6 by omega).trans
    (le_self_pow₀ (by omega) (by omega : q+1 ≠ 0))

theorem parameterGrowth_add {f g : ℕ → ℕ} (hf : ParameterGrowth f) (hg : ParameterGrowth g) :
    ParameterGrowth (fun q => f q+g q) := by
  obtain ⟨C,hf⟩ := hf
  obtain ⟨D,hg⟩ := hg
  refine ⟨C+D+1,fun q => ?_⟩
  have h₁ := (hf q).trans (pow_le_pow_right' (by omega : 1 ≤ q+6)
    (Nat.mul_le_mul_right (q+1) (by omega : C ≤ C+D)))
  have h₂ := (hg q).trans (pow_le_pow_right' (by omega : 1 ≤ q+6)
    (Nat.mul_le_mul_right (q+1) (by omega : D ≤ C+D)))
  have htwo : 2 ≤ (q+6)^(q+1) := (by omega : 2 ≤ q+6).trans
    (le_self_pow₀ (by omega) (by omega))
  have h := Nat.mul_le_mul_left ((q+6)^((C+D)*(q+1))) htwo
  rw [show (C+D+1)*(q+1)=(C+D)*(q+1)+(q+1) by ring,pow_add]
  nlinarith only [h₁,h₂,h]

theorem parameterGrowth_mul {f g : ℕ → ℕ} (hf : ParameterGrowth f) (hg : ParameterGrowth g) :
    ParameterGrowth (fun q => f q*g q) := by
  obtain ⟨C,hf⟩ := hf
  obtain ⟨D,hg⟩ := hg
  refine ⟨C+D,fun q => ?_⟩
  simpa only [← pow_add,← Nat.add_mul] using Nat.mul_le_mul (hf q) (hg q)

theorem parameterGrowth_pow {f : ℕ → ℕ} (hf : ParameterGrowth f) (d : ℕ) :
    ParameterGrowth (fun q => (f q)^d) := by
  obtain ⟨C,hf⟩ := hf
  refine ⟨C*d,fun q => ?_⟩
  have h := pow_le_pow_left' (hf q) d
  simpa only [← pow_mul,show C*(q+1)*d=C*d*(q+1) by ring] using h

theorem parameterGrowth_linearPower (k u v : ℕ) (hk : k ≤ 6) :
    ParameterGrowth (fun q => (q+k)^(u*q+v)) := by
  refine ⟨u+v,fun q => ?_⟩
  exact (pow_le_pow_left' (by omega : q+k ≤ q+6) _).trans
    (pow_le_pow_right' (by omega) (by nlinarith : u*q+v ≤ (u+v)*(q+1)))

theorem parameterGrowth_exp (b : ℕ) (hb : b ≤ 6) : ParameterGrowth (fun q => b^q) := by
  refine ⟨1,fun q => ?_⟩
  exact (pow_le_pow_left' (by omega : b ≤ q+6) q).trans
    (pow_le_pow_right' (by omega) (by omega))

theorem parameterGrowth_enumeration (d : ℕ) (hd : d ≤ 5) :
    ParameterGrowth (fun q => functionEnumerationBudget q d) := by
  apply parameterGrowth_mono (fun q => functionEnumerationBudget_bound q d)
  apply parameterGrowth_mul
  · exact parameterGrowth_pow (parameterGrowth_add parameterGrowth_q (parameterGrowth_constant 3)) 2
  · refine ⟨1,fun q => ?_⟩
    simpa only [one_mul] using pow_le_pow_left' (by omega : d+1 ≤ q+6) (q+1)

theorem parameterGrowth_builtForms : ParameterGrowth builtCountFormBudget := by
  have hkey : ParameterGrowth (fun q => normalKeyBuildBudget (q+1)) := by
    apply parameterGrowth_mono (fun q => normalKeyBuildBudget_parameter_bound (q+1))
    simpa only [show ∀ q : ℕ, q+1+4=q+5 by omega,
      show ∀ q : ℕ, 2*(q+1)+7=2*q+9 by omega] using parameterGrowth_linearPower 5 2 9 (by decide)
  have hnormal : ParameterGrowth (fun q => normalKeyBudget (q+1)) := by
    apply parameterGrowth_mono (fun q => normalKeyBudget_parameter_bound (q+1))
    simpa only [Nat.add_assoc,Nat.reduceAdd,one_mul] using parameterGrowth_linearPower 4 1 9 (by decide)
  have hpow : ParameterGrowth (fun q => (q+1)^(2*(q+1))) := by
    simpa only [show ∀ q : ℕ, 2*(q+1)=2*q+2 by omega] using parameterGrowth_linearPower 1 2 2 (by decide)
  unfold builtCountFormBudget
  apply parameterGrowth_add
  · apply parameterGrowth_add
    · exact parameterGrowth_add hkey (parameterGrowth_mul
        (parameterGrowth_mul (parameterGrowth_add parameterGrowth_q (parameterGrowth_constant 2)) hpow) hnormal)
    · exact parameterGrowth_mul (parameterGrowth_add parameterGrowth_q (parameterGrowth_constant 1))
        (parameterGrowth_add parameterGrowth_q (parameterGrowth_constant 2))
  · exact parameterGrowth_constant 1

/-- Both exponents precede the instance dimension and length. -/
def SharpPolynomial (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ d C : ℕ, ∀ q n L, f q n L ≤ (q+6)^(C*(q+1))*(n+L+2)^d

theorem sharpPolynomial_parameter {f : ℕ → ℕ} (hf : ParameterGrowth f) :
    SharpPolynomial (fun q _ _ => f q) := by
  obtain ⟨C,hf⟩ := hf
  refine ⟨0,C,?_⟩
  intro q n L
  simpa only [pow_zero,mul_one] using hf q

theorem sharpPolynomial_n : SharpPolynomial (fun _ n _ => n) := by
  exact ⟨1,0,by intro q n L; simp; omega⟩

theorem sharpPolynomial_L : SharpPolynomial (fun _ _ L => L) := by
  exact ⟨1,0,by intro q n L; simp; omega⟩

theorem sharpPolynomial_add {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : SharpPolynomial f) (hg : SharpPolynomial g) :
    SharpPolynomial (fun q n L => f q n L+g q n L) := by
  obtain ⟨d,C,hf⟩ := hf
  obtain ⟨e,D,hg⟩ := hg
  have hp : ParameterGrowth (fun q => (q+6)^(C*(q+1))+(q+6)^(D*(q+1))) :=
    parameterGrowth_add ⟨C,fun _ => le_rfl⟩ ⟨D,fun _ => le_rfl⟩
  obtain ⟨W,hw⟩ := hp
  refine ⟨d+e,W,fun q n L => ?_⟩
  have h₁ := (hf q n L).trans (Nat.mul_le_mul_left _
    (pow_le_pow_right' (by omega : 1 ≤ n+L+2) (by omega : d ≤ d+e)))
  have h₂ := (hg q n L).trans (Nat.mul_le_mul_left _
    (pow_le_pow_right' (by omega : 1 ≤ n+L+2) (by omega : e ≤ d+e)))
  have h₃ := Nat.mul_le_mul_right ((n+L+2)^(d+e)) (hw q)
  nlinarith only [h₁,h₂,h₃]

theorem sharpPolynomial_mul {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : SharpPolynomial f) (hg : SharpPolynomial g) :
    SharpPolynomial (fun q n L => f q n L*g q n L) := by
  obtain ⟨d,C,hf⟩ := hf
  obtain ⟨e,D,hg⟩ := hg
  refine ⟨d+e,C+D,fun q n L => ?_⟩
  calc
    _ ≤ ((q+6)^(C*(q+1))*(n+L+2)^d)*((q+6)^(D*(q+1))*(n+L+2)^e) :=
      Nat.mul_le_mul (hf q n L) (hg q n L)
    _ = _ := by rw [Nat.add_mul,pow_add,pow_add]; ring

theorem sharpPolynomial_pow {f : ℕ → ℕ → ℕ → ℕ} (hf : SharpPolynomial f) (c : ℕ) :
    SharpPolynomial (fun q n L => (f q n L)^c) := by
  obtain ⟨d,C,hf⟩ := hf
  refine ⟨d*c,C*c,fun q n L => ?_⟩
  have h := pow_le_pow_left' (hf q n L) c
  simpa only [mul_pow,← pow_mul,show C*(q+1)*c=C*c*(q+1) by ring] using h

open Lean Elab Tactic Meta in
syntax "sharp_polynomial" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| sharp_polynomial) => do
    try
      evalTactic (← `(tactic| first
        | exact sharpPolynomial_n
        | exact sharpPolynomial_L
        | exact sharpPolynomial_parameter (by assumption)
        | exact sharpPolynomial_parameter parameterGrowth_q
        | exact sharpPolynomial_parameter (parameterGrowth_constant _)
        | exact sharpPolynomial_parameter (parameterGrowth_exp _ (by decide))
        | exact sharpPolynomial_parameter (parameterGrowth_enumeration _ (by decide))
        | exact sharpPolynomial_parameter parameterGrowth_builtForms))
      return
    catch _ => pure ()
    let target ← getMainTarget
    let fn := target.getAppArgs.back!
    let head ← lambdaTelescope fn fun _ body => pure body.headBeta.getAppFn.constName?
    match head with
    | some ``HAdd.hAdd => evalTactic (← `(tactic| apply sharpPolynomial_add <;> sharp_polynomial))
    | some ``HMul.hMul => evalTactic (← `(tactic| apply sharpPolynomial_mul <;> sharp_polynomial))
    | some ``HPow.hPow => evalTactic (← `(tactic| apply sharpPolynomial_pow <;> sharp_polynomial))
    | _ => throwError "Unsupported sharp polynomial expression: {target}"

/-- The complete derived budget, not an assumed core cost, has q^{O(q)}
parameter dependence when the standard primitive factors have that dependence. -/
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4000 in
theorem weightedNormalizedBudget_sharp (I BI H K : ℕ → ℕ) (c bc a d : ℕ)
    (hI : ParameterGrowth I) (hBI : ParameterGrowth BI)
    (hH : ParameterGrowth H) (hK : ParameterGrowth K) :
    SharpPolynomial (fun q n L => weightedNormalizedExecutionBudget q n L
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
      (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc
      (H q) a (K q*(n+L+2)^d) (K q*(n+L+2)^d)) := by
  unfold weightedNormalizedExecutionBudget weightedRecognitionBudget weightedReturnedFamilyBudget
    weightedSelectionExecutionBudget weightedEdgeExecutionBudget weightedViolationRequestBudget
    weightedForcedRequestBudget weightedBranchRowBudget finalBasisBudget binaryRankBudget
    retainedFamilyLength weightedParityBudget weightedExtremaBudget weightedModesBudget
    preparedWeightedCellBudget preparedCellStepBudget weightedCellQueryBudget
  sharp_polynomial

end MOR34
