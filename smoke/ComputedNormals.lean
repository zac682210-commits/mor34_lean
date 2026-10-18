import MOR34.ExecutableCountForms
import MOR34.ExecutableNormalization

open MOR34

private def assertCheck (name : String) (ok : Bool) : IO Unit := do
  if ok then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

private def accepts {q : ℕ} (forms : List (IntegerForm q)) (z : Counts q) : Bool :=
  forms.all (fun f => decide (f.eval z = 0))

/- Runtime checks, separate from and not used by any proof. -/
#eval do
  let emptyForms := computedCountForms (∅ : Finset (Counts 1))
  assertCheck "empty set rejects all sampled points"
    ((List.range 5).all (fun k => !(accepts emptyForms (fun _ => k))))
  let pointForms := computedCountForms ({fun _ => 2} : Finset (Counts 1))
  assertCheck "singleton accepts its point" (accepts pointForms (fun _ => 2))
  assertCheck "singleton rejects another point" (!(accepts pointForms (fun _ => 3)))
  let lineForms := computedCountForms ({fun _ => 0, fun _ => 1} : Finset (Counts 1))
  assertCheck "full affine line accepts extrapolation" (accepts lineForms (fun _ => 37))
  let B : Finset (Counts 2) := {![0,0], ![1,2], ![2,4]}
  let forms := computedCountForms B
  assertCheck "dependent rows accept extrapolation" (accepts forms ![3,6])
  assertCheck "dependent rows reject off-line point" (!(accepts forms ![3,7]))
  assertCheck "normal family has exactly q+1 entries" (decide (forms.length = 3))
  let emptyZero := computedCountForms (∅ : Finset (Counts 0))
  assertCheck "zero coordinates and empty set" (!(accepts emptyZero Fin.elim0))
  let pointZero := computedCountForms ({Fin.elim0} : Finset (Counts 0))
  assertCheck "zero coordinates and singleton" (accepts pointZero Fin.elim0)
  let zeroMatrix : Matrix (Fin 2) (Fin 2) ℤ := fun _ _ => 0
  let normals := computedMatrixNormals zeroMatrix
  assertCheck "zero matrix has identity annihilator"
    (decide ((List.ofFn (fun j => List.ofFn (normals j))) = [[1,0],[0,1]]))
  let fullMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1,2;3,5]
  let fullNormals := computedMatrixNormals fullMatrix
  assertCheck "full rank matrix has zero annihilator"
    (decide ((List.ofFn (fun j => List.ofFn (fullNormals j))) = [[0,0],[0,0]]))
  IO.println "11 computed-normal runtime checks passed"

#eval do
  let N := normalizeRawExecutable (n := 4) (by decide) ![4,2,3,1] ![1,0,1,0] 4 2
    (by decide) (by decide) (by decide) (by decide)
  assertCheck "raw coefficient grouping includes zero class" (decide (N.classes = 2))
  assertCheck "raw classes sorted by coefficient"
    (decide (List.ofFn N.model.coefficient = [0,1]))
  assertCheck "raw within-class weights sorted"
    (decide ((List.ofFn (fun j => List.ofFn (fun k => N.model.weight ⟨j,k⟩))) = [[1,2],[3,4]]))
  assertCheck "raw item permutation retains original labels"
    (decide ((List.ofFn (fun j => List.ofFn (fun k => (N.itemEquiv ⟨j,k⟩).val))) = [[3,1],[2,0]]))
  IO.println "4 computed-normalization runtime checks passed"
