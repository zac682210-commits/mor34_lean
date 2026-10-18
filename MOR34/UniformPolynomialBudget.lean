import MOR34.ChargedNormalizedExecution
import MOR34.CompressionCostOffset

namespace MOR34

/-- The exponent is outside the parameter quantifier. This excludes an XP
bound whose polynomial degree grows with q. -/
def UniformPolynomial (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∃ F : ℕ → ℕ, ∀ q n L, f q n L ≤ F q*(n+L+2)^d

theorem uniformPolynomial_parameter (F : ℕ → ℕ) :
    UniformPolynomial (fun q _ _ => F q) := by
  exact ⟨0,F,by simp⟩

theorem uniformPolynomial_n : UniformPolynomial (fun _ n _ => n) := by
  exact ⟨1,fun _ => 1,by intro q n L; simp; omega⟩

theorem uniformPolynomial_L : UniformPolynomial (fun _ _ L => L) := by
  exact ⟨1,fun _ => 1,by intro q n L; simp; omega⟩

theorem uniformPolynomial_add {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : UniformPolynomial f) (hg : UniformPolynomial g) :
    UniformPolynomial (fun q n L => f q n L+g q n L) := by
  obtain ⟨d,F,hf⟩ := hf
  obtain ⟨e,G,hg⟩ := hg
  refine ⟨d+e,fun q => F q+G q,?_⟩
  intro q n L
  have h₁ := (hf q n L).trans (Nat.mul_le_mul_left (F q)
    (pow_le_pow_right' (by omega : 1 ≤ n+L+2) (by omega : d ≤ d+e)))
  have h₂ := (hg q n L).trans (Nat.mul_le_mul_left (G q)
    (pow_le_pow_right' (by omega : 1 ≤ n+L+2) (by omega : e ≤ d+e)))
  nlinarith only [h₁,h₂]

theorem uniformPolynomial_mul {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : UniformPolynomial f) (hg : UniformPolynomial g) :
    UniformPolynomial (fun q n L => f q n L*g q n L) := by
  obtain ⟨d,F,hf⟩ := hf
  obtain ⟨e,G,hg⟩ := hg
  refine ⟨d+e,fun q => F q*G q,?_⟩
  intro q n L
  calc
    _ ≤ (F q*(n+L+2)^d)*(G q*(n+L+2)^e) := Nat.mul_le_mul (hf q n L) (hg q n L)
    _ = _ := by rw [pow_add]; ring

theorem uniformPolynomial_pow {f : ℕ → ℕ → ℕ → ℕ}
    (hf : UniformPolynomial f) (c : ℕ) :
    UniformPolynomial (fun q n L => (f q n L)^c) := by
  obtain ⟨d,F,hf⟩ := hf
  refine ⟨d*c,fun q => (F q)^c,?_⟩
  intro q n L
  calc
    _ ≤ (F q*(n+L+2)^d)^c := pow_le_pow_left' (hf q n L) c
    _ = _ := by rw [mul_pow,← pow_mul]

open Lean Elab Tactic Meta in
syntax "uniform_polynomial" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| uniform_polynomial) => do
    try
      evalTactic (← `(tactic| first
        | exact uniformPolynomial_parameter _
        | exact uniformPolynomial_n
        | exact uniformPolynomial_L))
      return
    catch _ => pure ()
    let target ← getMainTarget
    let fn := target.getAppArgs.back!
    let head ← lambdaTelescope fn fun _ body =>
      pure body.headBeta.getAppFn.constName?
    match head with
    | some ``HAdd.hAdd =>
      evalTactic (← `(tactic| apply uniformPolynomial_add <;> uniform_polynomial))
    | some ``HMul.hMul =>
      evalTactic (← `(tactic| apply uniformPolynomial_mul <;> uniform_polynomial))
    | some ``HPow.hPow =>
      evalTactic (← `(tactic| apply uniformPolynomial_pow <;> uniform_polynomial))
    | _ => throwError "Unsupported uniform polynomial expression: {target}"

/-- All nonlinear dependence on the parameter occurs in the factor. Local
primitive input degrees c, bc and d are fixed before q is quantified. -/
theorem normalizedExecutionBudget_uniform (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    UniformPolynomial (fun q n L =>
      normalizedExecutionBudget q n L (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (I q) c (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc) := by
  unfold normalizedExecutionBudget recognitionBudget returnedFamilyBudget
    selectionExecutionBudget edgeExecutionBudget finalBasisBudget binaryRankBudget
    retainedFamilyLength denseParityBudget denseExtremaBudget denseModesBudget
    denseCellLoopBudget denseCellQueryBudget chargedCellStepBudget
  uniform_polynomial

/-- Monotonicity is used only for primitive envelopes, after the full execution
has been bounded phase by phase. -/
theorem normalizedExecutionBudget_mono (q n L N D I c J E C O BJ BE BI bc U : ℕ)
    (hN : N ≤ U) (hD : D ≤ U) (hJ : J ≤ U) (hE : E ≤ U)
    (hC : C ≤ U) (hO : O ≤ U) (hBJ : BJ ≤ U) (hBE : BE ≤ U) :
    normalizedExecutionBudget q n L N D I c J E C O BJ BE BI bc ≤
      normalizedExecutionBudget q n L U U I c U U U U U U BI bc := by
  unfold normalizedExecutionBudget recognitionBudget returnedFamilyBudget
    selectionExecutionBudget edgeExecutionBudget finalBasisBudget binaryRankBudget
    retainedFamilyLength denseParityBudget denseExtremaBudget denseModesBudget
    denseCellLoopBudget denseCellQueryBudget chargedCellStepBudget
  gcongr

/-- One uniform polynomial bounds the *complete* normalized reference budget.
Only local decoding, construction, collection and external solver/rank costs
are premises. There is no whole-execution cost premise. -/
theorem normalizedExecutionBudget_fpt (I BI K : ℕ → ℕ) (c bc d : ℕ) :
    ∃ e : ℕ, ∃ F : ℕ → ℕ, ∀ q n L N D J E C O BJ BE,
      N ≤ K q*(n+L+2)^d → D ≤ K q*(n+L+2)^d →
      J ≤ K q*(n+L+2)^d → E ≤ K q*(n+L+2)^d →
      C ≤ K q*(n+L+2)^d → O ≤ K q*(n+L+2)^d →
      BJ ≤ K q*(n+L+2)^d → BE ≤ K q*(n+L+2)^d →
      normalizedExecutionBudget q n L N D (I q) c J E C O BJ BE (BI q) bc ≤
        F q*(n+L+2)^e := by
  obtain ⟨e,F,hF⟩ := normalizedExecutionBudget_uniform I BI K c bc d
  refine ⟨e,F,?_⟩
  intro q n L N D J E C O BJ BE hN hD hJ hE hC hO hBJ hBE
  exact (normalizedExecutionBudget_mono q n L N D (I q) c J E C O BJ BE (BI q) bc _
    hN hD hJ hE hC hO hBJ hBE).trans (hF q n L)

end MOR34
