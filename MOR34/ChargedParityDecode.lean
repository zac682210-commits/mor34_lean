import MOR34.CellLoopComposition

namespace MOR34

/-- Decode each of the q stored solver count coordinates once, retain the
resulting natural-number table, and expose its indexed value. D is a local
coordinate-read/arithmetic allowance, not a solver or algorithm total. -/
def chargedParityDecode {q : ℕ} (ε : Parity q) (s : IntegerRowSolution q) (D : ℕ) :
    Counts q × ℕ :=
  let out := chargedMap (fun j : Fin q => ((2*s.1 j+(ε j).val).toNat,D)) (List.finRange q)
  (fun j => out.1[j.val]?.getD 0,out.2+q+1)

theorem chargedParityDecode_value {q : ℕ} (ε : Parity q) (s : IntegerRowSolution q) (D : ℕ) :
    (chargedParityDecode ε s D).1 = decodedParitySolution ε s := by
  funext j
  simp [chargedParityDecode,chargedMap_value,List.finRange,decodedParitySolution,
    decodeCounts,paritySubstitution]

theorem chargedParityDecode_cost {q : ℕ} (ε : Parity q) (s : IntegerRowSolution q) (D : ℕ) :
    (chargedParityDecode ε s D).2 = q*(D+2)+1 := by
  simp only [chargedParityDecode,chargedMap_cost_eq,List.map_map,Function.comp_def,
    List.map_const',List.length_finRange,List.sum_replicate]
  ring

def chargedDecodedRequest {q : ℕ} (ε : Parity q)
    (request : Option (IntegerRowSolution q) × ℕ) (D : ℕ) : Option (Counts q) × ℕ :=
  match request.1 with
  | none => (none,request.2+1)
  | some s => let out := chargedParityDecode ε s D
              (some out.1,request.2+out.2+1)

theorem chargedDecodedRequest_value {q : ℕ} (ε : Parity q)
    (request : Option (IntegerRowSolution q) × ℕ) (D : ℕ) :
    (chargedDecodedRequest ε request D).1 = request.1.map (decodedParitySolution ε) := by
  cases h : request.1 <;> simp [chargedDecodedRequest,h,chargedParityDecode_value]

theorem chargedDecodedRequest_cost {q : ℕ} (ε : Parity q)
    (request : Option (IntegerRowSolution q) × ℕ) (D : ℕ) :
    (chargedDecodedRequest ε request D).2 ≤ request.2+q*(D+2)+2 := by
  cases h : request.1 <;> simp only [chargedDecodedRequest,h,chargedParityDecode_cost] <;> omega

/-- Solver correctness itself bounds the coordinates that decoding reads.
Unbounded, unused epigraph witnesses do not enter this statement. -/
theorem parity_solution_count_bounds {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) (ε : Parity q) (Q : List (IntegerQuery q))
    (s : IntegerRowSolution q) (hs : ParityRows P ε Q s) (j : Fin q) :
    0 ≤ s.1 j ∧ s.1 j ≤ (m j : ℤ) := by
  have he : CountEpigraph P (paritySubstitution ε s.1) s.2 ∧
      RationalRestrictions (queryCoefficients Q) (queryBounds Q) (paritySubstitution ε s.1) := by
    simpa only [ParityRows,row_parity_iff,countRows_iff] using hs
  have hb := he.1.1 j
  have hp := (ε j).isLt
  simp only [paritySubstitution] at hb
  omega

end MOR34
