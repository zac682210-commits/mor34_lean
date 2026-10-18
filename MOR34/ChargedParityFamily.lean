import MOR34.DenseModeComposition
import MOR34.ExecutableReturnedSets

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def denseExtremaBudget (q n L D I c : ℕ) : ℕ :=
  2*q*((n+1)*(denseCellQueryBudget q n L D I c+q+5)+3)+2*q+3

def denseModesBudget (q n L N D I c J E : ℕ) : ℕ :=
  functionEnumerationBudget q 3+3^q*(denseCellLoopBudget q n L N D I c J+E+q+3)+1

def denseParityBudget (q n L N D I c J E : ℕ) : ℕ :=
  denseCellQueryBudget q n L D I c+denseExtremaBudget q n L D I c+
    denseModesBudget q n L N D I c J E+1

/-- One support answer decides whether extrema and modes run. Their returned
values are retained and reused; no test for mathematical nonemptiness occurs. -/
def chargedDenseParityFamily (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ε : Parity q) :
    List (Counts q) × ℕ :=
  let support := chargedDenseListQuery P A.R A.D solve ε []
  if h : support.1.isSome then
    let z := support.1.get h
    have hz : parityListSolver (denseCountOracle P A.R solve) ε [] = some z := by
      rw [← chargedDenseListQuery_value P A.R A.D solve ε []]
      exact (Option.some_get h).symm
    have hn : ∃ w, TightParity P ε w :=
      ⟨z, ((parityListSolver_spec P hWF _ (denseCountOracle_spec P A.R solve hs) ε).found [] z hz).1⟩
    let ex := chargedDenseExtrema P hWF A.R A.D solve hs ε hn
    let points := chargedDenseModes P solve A ε ex.1
    (points.1,support.2+ex.2+points.2+1)
  else ([],support.2+1)

theorem chargedDenseParityFamily_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ε : Parity q) :
    (chargedDenseParityFamily P hWF solve hs A ε).1.toFinset =
      computedParityFamily P hWF (denseCountOracle P A.R solve)
        (denseCountOracle_spec P A.R solve hs) computedCountForms ε := by
  classical
  simp only [chargedDenseParityFamily,computedParityFamily,chargedDenseListQuery_value]
  split
  · simp only [chargedDenseExtrema_value,chargedDenseModes_value,
      computedCellSelection_basis,storedParityExtrema_eq]
  · rfl

theorem chargedDenseParityFamily_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ε : Parity q) :
    (chargedDenseParityFamily P hWF solve hs A ε).2 ≤
      denseParityBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E := by
  let U := denseCellQueryBudget q (Fintype.card (Item m)) A.L A.D A.I A.c
  let V := denseExtremaBudget q (Fintype.card (Item m)) A.L A.D A.I A.c
  let W := denseModesBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E
  have hsupport : (chargedDenseListQuery P A.R A.D solve ε []).2 ≤ U :=
    chargedDenseListQuery_cost P hWF A.R A.D A.I A.c A.M A.L A.read_bound
      A.magnitude_pos A.magnitude_bits A.weights A.coefficients A.capacity A.rhs
      solve A.solver_cost ε [] (by simp) (by simp)
  have he (hn : ∃ w, TightParity P ε w) :
      (chargedDenseExtrema P hWF A.R A.D solve hs ε hn).2 ≤ V :=
    chargedDenseExtrema_cost P hWF A.R A.D A.I A.c A.M A.L A.read_bound
      A.magnitude_pos A.magnitude_bits A.weights A.coefficients A.capacity A.rhs
      solve hs A.solver_cost ε hn
  have hm (hn : ∃ w, TightParity P ε w) :
      (chargedDenseModes P solve A ε (chargedDenseExtrema P hWF A.R A.D solve hs ε hn).1).2 ≤ W := by
    rw [chargedDenseExtrema_value]
    exact chargedDenseModes_cost P hWF solve hs A ε hn
  change _ ≤ U+V+W+1
  unfold chargedDenseParityFamily
  split
  · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hsupport (he _)) (hm _)) 1
  · omega

theorem chargedDenseParityFamily_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) (ε : Parity q) :
    (chargedDenseParityFamily P hWF solve hs A ε).1.length ≤ 3^q*(q+1) := by
  unfold chargedDenseParityFamily
  split
  · rw [chargedDenseExtrema_value]
    exact chargedDenseModes_length P hWF solve hs A ε _
  · exact Nat.zero_le _

/-- Enumerate all parities once, retaining the concatenated point output. This
is the cell-selection phase, not the complete recognition/rank algorithm. -/
def chargedDenseSelection (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) : List (Counts q) × ℕ :=
  let parities := chargedFinFunctions q 2
  let out := chargedFlatMap (chargedDenseParityFamily P hWF solve hs A) parities.1
  (out.1,parities.2+out.2+1)

theorem chargedDenseSelection_value (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) :
    (chargedDenseSelection P hWF solve hs A).1.toFinset =
      computedSelectionFamily P hWF (denseCountOracle P A.R solve) (denseCountOracle_spec P A.R solve hs) := by
  classical
  ext z
  simp only [chargedDenseSelection,chargedFlatMap_value,chargedFinFunctions_value,
    List.mem_toFinset,List.mem_flatMap,computedSelectionFamily,Finset.mem_biUnion,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ε,_,hz⟩
    refine ⟨ε, ?_⟩
    have hh := List.mem_toFinset.mpr hz
    simpa only [chargedDenseParityFamily_value] using hh
  · rintro ⟨ε,hz⟩
    refine ⟨ε,mem_allFinFunctions q 2 ε,List.mem_toFinset.mp ?_⟩
    simpa only [chargedDenseParityFamily_value] using hz

theorem chargedDenseSelection_cost (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) :
    (chargedDenseSelection P hWF solve hs A).2 ≤
      functionEnumerationBudget q 2+2^q*
        (denseParityBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E+3^q*(q+1)+1)+1 := by
  have hh := chargedFlatMap_cost (chargedDenseParityFamily P hWF solve hs A)
    (chargedFinFunctions q 2).1
    (denseParityBudget q (Fintype.card (Item m)) A.L A.N A.D A.I A.c A.J A.E) (3^q*(q+1))
    (fun ε _ => chargedDenseParityFamily_cost P hWF solve hs A ε)
    (fun ε _ => chargedDenseParityFamily_length P hWF solve hs A ε)
  have hlen : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hlen] at hh
  have hf := chargedFinFunctions_cost q 2
  exact Nat.add_le_add_right (Nat.add_le_add hf hh) 1

/-- The retained list, including repetitions, has the parameter-only bound.
This is stronger for later data-movement accounting than a bound on its set. -/
theorem chargedDenseSelection_length (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) :
    (chargedDenseSelection P hWF solve hs A).1.length ≤ (q+1)*6^q := by
  have hh := flatMap_length_bound (chargedFinFunctions q 2).1
    (fun ε => (chargedDenseParityFamily P hWF solve hs A ε).1) (3^q*(q+1))
    (fun ε _ => chargedDenseParityFamily_length P hWF solve hs A ε)
  have hlen : (chargedFinFunctions q 2).1.length = 2^q := by
    rw [chargedFinFunctions_value,allFinFunctions_length]
  rw [hlen] at hh
  have heq : 2^q*(3^q*(q+1)) = (q+1)*6^q := by
    rw [show (6:ℕ)=2*3 from rfl,mul_pow]
    ring
  simpa only [chargedDenseSelection,chargedFlatMap_value,heq] using hh

theorem chargedDenseSelection_set (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) :
    (↑(chargedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q)) =
      selectedCounts P (computedCellSelection P hWF (denseCountOracle P A.R solve)
        (denseCountOracle_spec P A.R solve hs)) := by
  rw [chargedDenseSelection_value,computedSelectionFamily_eq,selectionFinset_coe]

theorem chargedDenseSelection_points (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve)
    (z : Counts q) (hz : z ∈ (chargedDenseSelection P hWF solve hs A).1) :
    BoundedCounts (m := m) z ∧ Tight P (prefixSet z) := by
  have hz' : z ∈ (↑(chargedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q)) :=
    List.mem_toFinset.mpr hz
  rw [chargedDenseSelection_set] at hz'
  obtain ⟨ε,hn,mode,hz''⟩ := hz'
  have h := (computedCellSelection P hWF (denseCountOracle P A.R solve)
    (denseCountOracle_spec P A.R solve hs)).contained ε hn mode hz''
  exact ⟨h.1.1,h.1.2.1⟩

/-- The retained output feeds the same new span theorem as the pure selection. -/
theorem chargedDenseSelection_span (P : Model m) (hWF : WellFormed P)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives P solve) :
    augmentedSpan (tightPointSet P) =
      augmentedSpan ((fun z => pointVector (prefixSet z)) ''
        (↑(chargedDenseSelection P hWF solve hs A).1.toFinset : Set (Counts q))) ⊔
        (adjacentDirectionSpan P).map zeroAugment := by
  rw [chargedDenseSelection_set]
  exact selected_augmented_span P hWF _

end MOR34
