import MOR34.OriginalWeightedApplication
import MOR34.SharpPolynomialBudget

namespace MOR34
variable {n : ℕ} {a v : Fin n → ℤ} {b rhs : ℤ}

/-- The local primitive dictionary for one normalized input. The only bounds
stored here concern primitive calls, never the composed MOR34 procedure. -/
structure WeightedRunPrimitives (N : RawNormalization a v b rhs) where
  R : ℕ
  R_bound : R ≤ n+1
  solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ
  spec : DenseRowSolverSpec solve
  arithmetic : WeightedPipelinePrimitives N.model solve
  point : PointOperations N.sizes
  ranker : ExactIntegerRank N.sizes
  rankOps : BinaryRankOperations ranker
  sets : BinaryCollectionOperations N.sizes
  relabelPoint : RelabelPointOperation N.itemEquiv
  relabelBasis : RelabelBasisOperations N.sizes n
  C : ℕ
  O : ℕ
  BJ : ℕ
  BE : ℕ
  BI : ℕ
  bc : ℕ
  RC : ℕ
  RE : ℕ
  RJ : ℕ
  point_bound : PointOperationBounds point C
  rank_bound : BinaryRankBounds ranker rankOps BE BI bc
  sets_bound : BinaryCollectionBounds sets O BJ
  relabel_bound : RelabelLocalBounds N.itemEquiv relabelPoint relabelBasis RC RE RJ

def WeightedRunPrimitives.run (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N) :
    RawOutput n × ℕ :=
  N.runWeighted s.R s.solve s.spec s.arithmetic s.point s.ranker s.rankOps s.sets s.relabelPoint s.relabelBasis

def WeightedRunPrimitives.budget (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N) : ℕ :=
  rawWeightedBudget N.classes n s.arithmetic.base.L s.arithmetic.base.N s.arithmetic.base.D
    s.arithmetic.base.I s.arithmetic.base.c s.arithmetic.base.J s.arithmetic.base.E
    s.C s.O s.BJ s.BE s.BI s.bc s.arithmetic.H s.arithmetic.a s.arithmetic.unit
    s.arithmetic.prepCost s.RC s.RE s.RJ

theorem weightedRun_correct (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N) :
    (s.run N).1.Correct a v b rhs :=
  weightedRawExecution_correct N s.R s.solve s.spec s.arithmetic s.point s.ranker s.rankOps s.sets
    s.relabelPoint s.relabelBasis

theorem weightedRun_cost (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N) :
    (s.run N).2 ≤ s.budget N :=
  weightedRawExecution_cost N s.R s.solve s.spec s.arithmetic s.R_bound s.point s.ranker s.rankOps
    s.sets s.relabelPoint s.relabelBasis s.C s.O s.BJ s.BE s.BI s.bc s.RC s.RE s.RJ
    s.point_bound s.rank_bound s.sets_bound s.relabel_bound

/-- A common local polynomial envelope, with separately supplied ILP and rank
factors. This is a conjunction of local primitive bounds only. -/
structure WeightedRunBounds (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N)
    (I BI H K : ℕ → ℕ) (c bc ae d : ℕ) : Prop where
  ilp_factor : s.arithmetic.base.I = I N.classes
  ilp_degree : s.arithmetic.base.c = c
  rank_factor : s.BI = BI N.classes
  rank_degree : s.bc = bc
  arithmetic_factor : s.arithmetic.H = H N.classes
  arithmetic_degree : s.arithmetic.a = ae
  elementary : WeightedExecutionLocalBounds N.model s.solve s.arithmetic s.C s.O s.BJ s.BE
    (K N.classes*(n+s.arithmetic.base.L+2)^d)
  relabelPoint : s.RC ≤ K N.classes*(n+s.arithmetic.base.L+2)^d
  relabelEmit : s.RE ≤ K N.classes*(n+s.arithmetic.base.L+2)^d
  relabelCollect : s.RJ ≤ K N.classes*(n+s.arithmetic.base.L+2)^d

theorem rawWeightedBudget_sharp (I BI H K : ℕ → ℕ) (c bc ae d : ℕ)
    (hI : ParameterGrowth I) (hBI : ParameterGrowth BI)
    (hH : ParameterGrowth H) (hK : ParameterGrowth K) :
    SharpPolynomial (fun q n L =>
      rawWeightedBudget q n L (K q*(n+L+2)^d) (K q*(n+L+2)^d) (I q) c
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d) (BI q) bc
        (H q) ae (K q*(n+L+2)^d) (K q*(n+L+2)^d)
        (K q*(n+L+2)^d) (K q*(n+L+2)^d) (K q*(n+L+2)^d)) := by
  unfold rawWeightedBudget
  apply sharpPolynomial_add
  · apply sharpPolynomial_add
    · apply sharpPolynomial_add
      · apply sharpPolynomial_add
        · apply sharpPolynomial_add
          · exact weightedNormalizedBudget_sharp I BI H K c bc ae d hI hBI hH hK
          · sharp_polynomial
        · sharp_polynomial
      · sharp_polynomial
    · sharp_polynomial
  · sharp_polynomial

theorem weightedRun_local_envelope (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N)
    (I BI H K : ℕ → ℕ) (c bc ae d : ℕ) (h : WeightedRunBounds N s I BI H K c bc ae d) :
    s.budget N ≤ rawWeightedBudget N.classes n s.arithmetic.base.L
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (I N.classes) c (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (BI N.classes) bc (H N.classes) ae
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (K N.classes*(n+s.arithmetic.base.L+2)^d) (K N.classes*(n+s.arithmetic.base.L+2)^d)
      (K N.classes*(n+s.arithmetic.base.L+2)^d) := by
  have hm := weightedNormalizedBudget_mono N.classes n s.arithmetic.base.L s.arithmetic.base.N
    s.arithmetic.base.D (I N.classes) c s.arithmetic.base.J s.arithmetic.base.E s.C s.O s.BJ s.BE
    (BI N.classes) bc (H N.classes) ae s.arithmetic.unit s.arithmetic.prepCost _
    h.elementary.base.normalRead h.elementary.base.decode h.elementary.base.insertCount h.elementary.base.emitCount
    h.elementary.base.point h.elementary.base.order h.elementary.base.insertBinary h.elementary.base.emitBinary
    h.elementary.normalUnit h.elementary.prepare
  unfold WeightedRunPrimitives.budget rawWeightedBudget
  rw [h.ilp_factor,h.ilp_degree,h.rank_factor,h.rank_degree,h.arithmetic_factor,h.arithmetic_degree]
  have ht := Nat.mul_le_mul_left (n+1) (Nat.add_le_add_right h.relabelPoint 1)
  linarith [h.relabelPoint,h.relabelEmit,h.relabelCollect]

/-- The parameter factor is now explicit up to an absolute constant exponent,
not an arbitrary function of the parameter. -/
theorem weightedRun_sharp (I BI H K : ℕ → ℕ) (c bc ae d : ℕ)
    (hI : ParameterGrowth I) (hBI : ParameterGrowth BI)
    (hH : ParameterGrowth H) (hK : ParameterGrowth K) :
    ∃ e W : ℕ, ∀ {n : ℕ} {a v : Fin n → ℤ} {b rhs : ℤ}
      (N : RawNormalization a v b rhs) (s : WeightedRunPrimitives N),
      WeightedRunBounds N s I BI H K c bc ae d →
      (s.run N).1.Correct a v b rhs ∧
      (s.run N).2 ≤ (N.classes+6)^(W*(N.classes+1))*(n+s.arithmetic.base.L+2)^e := by
  obtain ⟨e,W,hw⟩ := rawWeightedBudget_sharp I BI H K c bc ae d hI hBI hH hK
  refine ⟨e,W,?_⟩
  intro n a v b rhs N s h
  exact ⟨weightedRun_correct N s,(weightedRun_cost N s).trans
    ((weightedRun_local_envelope N s I BI H K c bc ae d h).trans (hw N.classes n s.arithmetic.base.L))⟩

end MOR34
