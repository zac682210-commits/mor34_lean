import MOR34.DenseCountSolver
import MOR34.MaterializedViolationRows

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def violationRowIndexList (m : Fin q → ℕ) : List (ViolationRow m) :=
  ((List.finRange q).map fun k => .inl (.inl (.inl k))) ++
  ((List.finRange q).map fun k => .inl (.inl (.inr k))) ++
  ((List.ofFn (fun k : Fin q => k)).flatMap fun k =>
    (List.finRange (m k)).map fun a => .inl (.inr (.inl ⟨k,a⟩))) ++
  [.inl (.inr (.inr ())),.inr ()]

theorem violationRowIndexList_complete (k : ViolationRow m) : k ∈ violationRowIndexList m := by
  rcases k with ((k | k) | (⟨k,a⟩ | u)) | u
  all_goals simp [violationRowIndexList, List.mem_flatMap]

theorem violationRowIndexList_length :
    (violationRowIndexList m).length = Fintype.card (Item m)+2*q+2 := by
  simp only [violationRowIndexList, List.length_append, List.length_map,
    List.length_finRange, List.length_flatMap, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    List.length_cons, List.length_nil]
  simp only [Item, Fintype.card_sigma, Fintype.card_fin]
  omega

def compiledViolationRequest (P : Model m) (R : ℕ) : List (DenseIntegerRow q) × ℕ :=
  let indices := violationRowIndexList m
  let out := chargedMap (fun k => compileRetainedRow (builtViolationRow P R k)) indices
  (out.1,out.2+8*indices.length+q+1)

theorem compiledViolationRequest_sized (P : Model m) (R : ℕ) :
    ∀ row ∈ (compiledViolationRequest P R).1, row.WellSized := by
  intro row hrow
  simp only [compiledViolationRequest, chargedMap_value, List.mem_map] at hrow
  obtain ⟨k,_,rfl⟩ := hrow
  exact evaluateConstructedRow_sized _

theorem compiledViolationRequest_iff (P : Model m) (R : ℕ) (z y : Fin q → ℤ) :
    (∀ row ∈ (compiledViolationRequest P R).1, row.value.Holds z y) ↔
      ∀ k : ViolationRow m, (violationRow P k).Holds z y := by
  simp only [compiledViolationRequest, chargedMap_value, List.forall_mem_map,
    compileRetainedRow_value, builtViolationRow_interpret]
  exact ⟨fun h k => h k (violationRowIndexList_complete k),fun h k _ => h k⟩

theorem compiledViolationRequest_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) :
    (compiledViolationRequest P R).2 ≤ 2048*(Fintype.card (Item m)+1)^4 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  have hrow (k : ViolationRow m) :
      (compileRetainedRow (builtViolationRow P R k)).2 ≤ 256*(n+1)^3 := by
    rw [compileRetainedRow_cost, builtViolationRow_value]
    have hbuild := builtViolationRow_cost P n R hq hm hR k
    have heval := violationRowConstruction_work P n hm k
    nlinarith
  have hmap := chargedMap_cost (fun k => compileRetainedRow (builtViolationRow P R k))
    (violationRowIndexList m) (256*(n+1)^3) (fun k _ => hrow k)
  have hi : (violationRowIndexList m).length ≤ 6*(n+1) := by
    rw [violationRowIndexList_length]; change n+2*q+2 ≤ _; omega
  have hmap' := hmap.trans (Nat.mul_le_mul_right (256*(n+1)^3+1) hi)
  dsimp only [compiledViolationRequest]
  change _ ≤ 2048*(n+1)^4
  nlinarith

def chargedDenseViolationSolve (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) :
    Option (IntegerRowSolution q) × ℕ :=
  let request := compiledViolationRequest P R
  let result := solve request.1
  (result.1,request.2+result.2+1)

theorem denseViolation_spec (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) :
    ViolationSolverSpec P (chargedDenseViolationSolve P R solve).1 := by
  constructor
  · intro s h
    exact (compiledViolationRequest_iff P R s.1 s.2).mp
      (hs.found _ (compiledViolationRequest_sized P R) s h)
  · intro h z y hh
    exact hs.done _ (compiledViolationRequest_sized P R) h z y
      ((compiledViolationRequest_iff P R z y).mpr hh)

theorem chargedDenseViolationSolve_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ) (U : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2)
    (hU : (solve (compiledViolationRequest P R).1).2 ≤ U) :
    (chargedDenseViolationSolve P R solve).2 ≤ 2048*(Fintype.card (Item m)+1)^4+U+1 := by
  have hh := compiledViolationRequest_cost P hWF R hR
  dsimp only [chargedDenseViolationSolve]
  omega

/-- All three solver interfaces are supplied by one established dense integer
solver. Correctness includes invalid and empty branches, not just supported faces. -/
def denseNormalizedPipeline (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ranker : ExactIntegerRank m) : NormalizedOutput m :=
  constructedNormalizedPipeline P hWF (denseCountOracle P R solve)
    (denseCountOracle_spec P R solve hs) (denseForcedOracle P R solve)
    (chargedDenseViolationSolve P R solve).1 ranker

theorem denseNormalizedPipeline_correct (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) (ranker : ExactIntegerRank m) :
    (denseNormalizedPipeline P hWF R solve hs ranker).Correct P :=
  constructedNormalizedPipeline_correct P hWF (denseCountOracle P R solve)
    (denseCountOracle_spec P R solve hs) (denseForcedOracle P R solve)
    (denseForcedOracle_spec P R solve hs) (chargedDenseViolationSolve P R solve).1
    (denseViolation_spec P R solve hs) ranker

end MOR34
