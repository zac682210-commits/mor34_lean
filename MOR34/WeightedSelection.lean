import MOR34.WeightedModes
import MOR34.ExecutableReturnedSets

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def weightedModesBudget (q n L N D I c J E H a unit prep : ℕ) : ℕ :=
  functionEnumerationBudget q 3+3^q*(preparedWeightedCellBudget q n L N D I c J H a unit prep+E+q+3)+1

def weightedParityBudget (q n L N D I c J E H a unit prep : ℕ) : ℕ :=
  weightedCellQueryBudget q n L D I c H a+weightedExtremaBudget q n L D I c H a+
    weightedModesBudget q n L N D I c J E H a unit prep+1

theorem weightedDenseSupport_nonempty (arith : IntegerArithmeticCharge) (P : Model m)
    (hWF : WellFormed P) (R D : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ε : Parity q)
    (h : (weightedDenseListQuery arith P R D solve ε []).1.isSome = true) :
    ∃ z, TightParity P ε z := by
  let z := (weightedDenseListQuery arith P R D solve ε []).1.get h
  have hz : parityListSolver (denseCountOracle P R solve) ε [] = some z := by
    rw [← weightedDenseListQuery_value arith P R D solve ε []]
    exact (Option.some_get h).symm
  exact ⟨z,((parityListSolver_spec P hWF _ (denseCountOracle_spec P R solve hs) ε).found [] z hz).1⟩

/-- One support answer decides whether extrema and modes run. Their returned
values are retained and reused; no test for mathematical nonemptiness occurs. -/
def weightedDenseParityFamily (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ε : Parity q) :
    List (Counts q) × ℕ :=
  let support := weightedDenseListQuery A.arith P A.base.R A.base.D solve ε []
  if h : support.1.isSome then
    have hn : ∃ w, TightParity P ε w := weightedDenseSupport_nonempty A.arith P hWF A.base.R A.base.D solve hs ε h
    let ex := weightedDenseExtrema A.arith P hWF A.base.R A.base.D solve hs ε hn
    let points := weightedDenseModes P solve A ε ex.1
    (points.1,support.2+ex.2+points.2+1)
  else ([],support.2+1)

theorem weightedDenseParityFamily_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ε : Parity q) :
    (weightedDenseParityFamily P hWF solve hs A ε).1.toFinset =
      computedParityFamily P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs) computedCountForms ε := by
  classical
  simp only [weightedDenseParityFamily,computedParityFamily,weightedDenseListQuery_value]
  split
  · simp only [weightedDenseExtrema_value,weightedDenseModes_value P hWF solve hs A ε,
      computedCellSelection_basis,storedParityExtrema_eq]
  · rfl

theorem weightedDenseParityFamily_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ε : Parity q) :
    (weightedDenseParityFamily P hWF solve hs A ε).2 ≤
      weightedParityBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E A.H A.a A.unit A.prepCost := by
  let U := weightedCellQueryBudget q (Fintype.card (Item m)) A.base.L A.base.D A.base.I A.base.c A.H A.a
  let V := weightedExtremaBudget q (Fintype.card (Item m)) A.base.L A.base.D A.base.I A.base.c A.H A.a
  let W := weightedModesBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E A.H A.a A.unit A.prepCost
  have hsupport : (weightedDenseListQuery A.arith P A.base.R A.base.D solve ε []).2 ≤ U :=
    weightedDenseListQuery_cost P hWF solve A.base A.arith A.H A.a A.arithmetic_bound ε [] (by simp) (by simp)
  have he (hn : ∃ w, TightParity P ε w) :
      (weightedDenseExtrema A.arith P hWF A.base.R A.base.D solve hs ε hn).2 ≤ V :=
    weightedDenseExtrema_cost P hWF solve hs A.base A.arith A.H A.a A.arithmetic_bound ε hn
  have hm (hn : ∃ w, TightParity P ε w) :
      (weightedDenseModes P solve A ε (weightedDenseExtrema A.arith P hWF A.base.R A.base.D solve hs ε hn).1).2 ≤ W := by
    rw [weightedDenseExtrema_value]
    exact weightedDenseModes_cost P hWF solve hs A ε hn
  change _ ≤ U+V+W+1
  dsimp only [weightedDenseParityFamily]
  split
  · rename_i h
    have hn := weightedDenseSupport_nonempty A.arith P hWF A.base.R A.base.D solve hs ε h
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hsupport (he hn)) (hm hn)) 1
  · omega

theorem weightedDenseParityFamily_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) (ε : Parity q) :
    (weightedDenseParityFamily P hWF solve hs A ε).1.length ≤ 3^q*(q+1) := by
  dsimp only [weightedDenseParityFamily]
  split
  · rename_i h
    have hn := weightedDenseSupport_nonempty A.arith P hWF A.base.R A.base.D solve hs ε h
    rw [weightedDenseExtrema_value]
    exact weightedDenseModes_length P hWF solve hs A ε hn
  · exact Nat.zero_le _

/-- Enumerate all parities once, retaining the concatenated point output. This
is the cell-selection phase, not the complete recognition/rank algorithm. -/
def weightedDenseSelection (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) : List (Counts q) × ℕ :=
  let parities := chargedFinFunctions q 2
  let out := chargedFlatMap (weightedDenseParityFamily P hWF solve hs A) parities.1
  (out.1,parities.2+out.2+1)

theorem weightedDenseSelection_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) :
    (weightedDenseSelection P hWF solve hs A).1.toFinset =
      computedSelectionFamily P hWF (denseCountOracle P A.base.R solve) (denseCountOracle_spec P A.base.R solve hs) := by
  classical
  ext z
  simp only [weightedDenseSelection,chargedFlatMap_value,chargedFinFunctions_value,
    List.mem_toFinset,List.mem_flatMap,computedSelectionFamily,Finset.mem_biUnion,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ε,_,hz⟩
    refine ⟨ε, ?_⟩
    have hh := List.mem_toFinset.mpr hz
    simpa only [weightedDenseParityFamily_value] using hh
  · rintro ⟨ε,hz⟩
    refine ⟨ε,mem_allFinFunctions q 2 ε,List.mem_toFinset.mp ?_⟩
    simpa only [weightedDenseParityFamily_value] using hz

theorem weightedDenseSelection_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) :
    (weightedDenseSelection P hWF solve hs A).2 ≤
      functionEnumerationBudget q 2+2^q*
        (weightedParityBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E A.H A.a A.unit A.prepCost+3^q*(q+1)+1)+1 := by
  have hh := chargedFlatMap_cost (weightedDenseParityFamily P hWF solve hs A)
    (chargedFinFunctions q 2).1
    (weightedParityBudget q (Fintype.card (Item m)) A.base.L A.base.N A.base.D A.base.I A.base.c A.base.J A.base.E A.H A.a A.unit A.prepCost) (3^q*(q+1))
    (fun ε _ => weightedDenseParityFamily_cost P hWF solve hs A ε)
    (fun ε _ => weightedDenseParityFamily_length P hWF solve hs A ε)
  have hlen : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hlen] at hh
  have hf := chargedFinFunctions_cost q 2
  exact Nat.add_le_add_right (Nat.add_le_add hf hh) 1

/-- The retained list, including repetitions, has the parameter-only bound.
This is stronger for later data-movement accounting than a bound on its set. -/
theorem weightedDenseSelection_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) :
    (weightedDenseSelection P hWF solve hs A).1.length ≤ (q+1)*6^q := by
  have hh := flatMap_length_bound (chargedFinFunctions q 2).1
    (fun ε => (weightedDenseParityFamily P hWF solve hs A ε).1) (3^q*(q+1))
    (fun ε _ => weightedDenseParityFamily_length P hWF solve hs A ε)
  have hlen : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hlen] at hh
  have heq : 2^q*(3^q*(q+1)) = (q+1)*6^q := by
    rw [show (6:ℕ)=2*3 from rfl,mul_pow]
    ring
  simpa only [weightedDenseSelection,chargedFlatMap_value,heq] using hh

theorem weightedDenseSelection_set (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) :
    (↑(weightedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q)) =
      selectedCounts P (computedCellSelection P hWF (denseCountOracle P A.base.R solve)
        (denseCountOracle_spec P A.base.R solve hs)) := by
  rw [weightedDenseSelection_value,computedSelectionFamily_eq,selectionFinset_coe]

theorem weightedDenseSelection_points (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve)
    (z : Counts q) (hz : z ∈ (weightedDenseSelection P hWF solve hs A).1) :
    BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
  have hz' : z ∈ (↑(weightedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q)) :=
    List.mem_toFinset.mpr hz
  rw [weightedDenseSelection_set] at hz'
  obtain ⟨ε,hn,mode,hz''⟩ := hz'
  have h := (computedCellSelection P hWF (denseCountOracle P A.base.R solve)
    (denseCountOracle_spec P A.base.R solve hs)).contained ε hn mode hz''
  exact ⟨h.1.1,h.1.2.1⟩

/-- The retained output feeds the same new span theorem as the pure selection. -/
theorem weightedDenseSelection_span (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : WeightedPipelinePrimitives P solve) :
    augmentedSpan (tightPointSet P) =
      augmentedSpan ((fun z => pointVector (prefixSet z)) ''
        (↑(weightedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q))) ⊔
        (adjacentDirectionSpan P).map zeroAugment := by
  rw [weightedDenseSelection_set]
  exact selected_augmented_span P hWF _

end MOR34
