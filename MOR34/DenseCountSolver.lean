import MOR34.DenseParityRows
import MOR34.DenseForcedSolver

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

def countRowIndexList (m : Fin q → ℕ) (r : ℕ) : List (CountRow m r) :=
  ((List.finRange q).map fun k => .inl (.inl k)) ++
  ((List.finRange q).map fun k => .inl (.inr k)) ++
  [.inr (.inl (.inl ())),.inr (.inl (.inr ()))] ++
  ((List.ofFn (fun k : Fin q => k)).flatMap fun k =>
    (List.finRange (m k)).map fun a => .inr (.inr (.inl ⟨k,a⟩))) ++
  [.inr (.inr (.inr (.inl ())))] ++
  ((List.finRange r).map fun i => .inr (.inr (.inr (.inr i))))

theorem countRowIndexList_complete (k : CountRow m r) : k ∈ countRowIndexList m r := by
  rcases k with (k | k) | ((u | u) | (⟨k,a⟩ | (u | i)))
  all_goals simp [countRowIndexList, List.mem_flatMap]

theorem countRowIndexList_length :
    (countRowIndexList m r).length = Fintype.card (Item m)+2*q+r+3 := by
  simp only [countRowIndexList, List.length_append, List.length_map,
    List.length_finRange, List.length_flatMap, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    List.length_cons, List.length_nil]
  simp only [Item, Fintype.card_sigma, Fintype.card_fin]
  omega

/-- Construction, expression evaluation, parity substitution and integer-array
emission for one actual parity query. R bounds input/query-table scalar access. -/
def compiledCountRequest (P : Model m) (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ) :
    List (DenseIntegerRow q) × ℕ :=
  let indices := countRowIndexList m L.length
  let out := chargedMap (fun k => compileParityRow
    (builtCountRow P (fun i j => (L.get i).coefficient j) (fun i => (L.get i).bound) R k) ε) indices
  (out.1,out.2+8*indices.length+q+1)

theorem compiledCountRequest_sized (P : Model m) (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ) :
    ∀ row ∈ (compiledCountRequest P ε L R).1, row.WellSized := by
  intro row hrow
  simp only [compiledCountRequest, chargedMap_value, List.mem_map] at hrow
  obtain ⟨k,_,rfl⟩ := hrow
  exact compileParityRow_sized _ _

theorem compiledCountRequest_iff (P : Model m) (ε : Parity q) (L : List (IntegerQuery q))
    (R : ℕ) (s : IntegerRowSolution q) :
    (∀ row ∈ (compiledCountRequest P ε L R).1, row.value.Holds s.1 s.2) ↔ ParityRows P ε L s := by
  simp only [compiledCountRequest, chargedMap_value, List.forall_mem_map,
    compileParityRow_value, builtCountRow_interpret]
  change (∀ k ∈ countRowIndexList m L.length,
      ((countRow P (queryCoefficients L) (queryBounds L) k).withParity ε).Holds s.1 s.2) ↔ _
  exact ⟨fun h k => h k (countRowIndexList_complete k),fun h k _ => h k⟩

theorem compiledCountRequest_cost (P : Model m) (hWF : WellFormed P)
    (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hL : L.length ≤ 3*q+1) :
    (compiledCountRequest P ε L R).2 ≤ 2048*(Fintype.card (Item m)+1)^4 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  have hmap := chargedMap_cost (fun k => compileParityRow
    (builtCountRow P (fun i j => (L.get i).coefficient j) (fun i => (L.get i).bound) R k) ε)
    (countRowIndexList m L.length) (256*(n+1)^3)
    (fun k _ => compiledCountParity_cost P _ _ n R hq hm hR ε k)
  have hi : (countRowIndexList m L.length).length ≤ 6*(n+1) := by
    rw [countRowIndexList_length]; change n+2*q+L.length+3 ≤ _; omega
  have hmap' := hmap.trans (Nat.mul_le_mul_right (256*(n+1)^3+1) hi)
  dsimp only [compiledCountRequest]
  change _ ≤ 2048*(n+1)^4
  nlinarith

def chargedDenseCountSolve (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (L : List (IntegerQuery q)) : Option (IntegerRowSolution q) × ℕ :=
  let request := compiledCountRequest P ε L R
  let result := solve request.1
  (result.1,request.2+result.2+1)

def denseCountOracle (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (L : List (IntegerQuery q)) : Option (IntegerRowSolution q) :=
  (chargedDenseCountSolve P R solve ε L).1

theorem denseCountOracle_spec (P : Model m) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (hs : DenseRowSolverSpec solve) : ParityRowSolverSpec P (denseCountOracle P R solve) := by
  constructor
  · intro ε L s h
    exact (compiledCountRequest_iff P ε L R s).mp
      (hs.found _ (compiledCountRequest_sized P ε L R) s h)
  · intro ε L h s hh
    exact hs.done _ (compiledCountRequest_sized P ε L R) h s.1 s.2
      ((compiledCountRequest_iff P ε L R s).mpr hh)

theorem chargedDenseCountSolve_cost (P : Model m) (hWF : WellFormed P) (R : ℕ)
    (solve : List (DenseIntegerRow q) → Option (IntegerRowSolution q) × ℕ)
    (ε : Parity q) (L : List (IntegerQuery q)) (U : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hL : L.length ≤ 3*q+1)
    (hU : (solve (compiledCountRequest P ε L R).1).2 ≤ U) :
    (chargedDenseCountSolve P R solve ε L).2 ≤
      2048*(Fintype.card (Item m)+1)^4+U+1 := by
  have hh := compiledCountRequest_cost P hWF ε L R hR hL
  dsimp only [chargedDenseCountSolve]
  omega

end MOR34
