import MOR34.RetainedForcedRows

namespace MOR34

theorem chargedMap_cost_eq {α β : Type*} (f : α → β × ℕ) (L : List α) :
    (chargedMap f L).2 = (L.map (fun a => (f a).2)).sum+L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [chargedMap, List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- Evaluates every arithmetic node once. The charge counts integer operations;
bit costs are supplied by the arithmetic primitive, separately from this trace. -/
def evaluateInteger : IntegerConstruction → ℤ × ℕ
  | .atom z => (z,1)
  | .add a b => let x := evaluateInteger a; let y := evaluateInteger b
      (x.1+y.1,x.2+y.2+1)
  | .mul a b => let x := evaluateInteger a; let y := evaluateInteger b
      (x.1*y.1,x.2+y.2+1)
  | .neg a => let x := evaluateInteger a; (-x.1,x.2+1)

theorem evaluateInteger_value (e : IntegerConstruction) :
    (evaluateInteger e).1 = e.value := by
  induction e <;> simp_all [evaluateInteger, IntegerConstruction.value]

theorem evaluateInteger_cost (e : IntegerConstruction) :
    (evaluateInteger e).2 = e.work := by
  induction e <;> simp_all [evaluateInteger, IntegerConstruction.work]

/-- Integer arrays are materialized before invoking the established solver. -/
structure DenseIntegerRow (q : ℕ) where
  counts : List ℤ
  costs : List ℤ
  bound : ℤ

def DenseIntegerRow.value {q : ℕ} (row : DenseIntegerRow q) : CountInequality q :=
  integerRow (fun j => row.counts[j.val]?.getD 0)
    (fun j => row.costs[j.val]?.getD 0) row.bound

def DenseIntegerRow.WellSized {q : ℕ} (row : DenseIntegerRow q) : Prop :=
  row.counts.length = q ∧ row.costs.length = q

def evaluateConstructedRow {q : ℕ} (row : ConstructedIntegerRow q) : DenseIntegerRow q × ℕ :=
  let indices := List.ofFn (fun j : Fin q => j)
  let a := chargedMap (fun j => evaluateInteger (row.counts j)) indices
  let b := chargedMap (fun j => evaluateInteger (row.costs j)) indices
  let c := evaluateInteger row.bound
  (⟨a.1,b.1,c.1⟩,a.2+b.2+c.2+q+2)

theorem evaluateConstructedRow_arrays {q : ℕ} (row : ConstructedIntegerRow q) :
    (evaluateConstructedRow row).1 =
      ⟨List.ofFn (fun j => (row.counts j).value),
       List.ofFn (fun j => (row.costs j).value),row.bound.value⟩ := by
  simp only [evaluateConstructedRow, chargedMap_value, List.map_ofFn, Function.comp_def, evaluateInteger_value]

theorem evaluateConstructedRow_sized {q : ℕ} (row : ConstructedIntegerRow q) :
    (evaluateConstructedRow row).1.WellSized := by
  rw [evaluateConstructedRow_arrays]
  simp [DenseIntegerRow.WellSized]

theorem evaluateConstructedRow_value {q : ℕ} (row : ConstructedIntegerRow q) :
    (evaluateConstructedRow row).1.value = row.value := by
  rw [evaluateConstructedRow_arrays]
  simp [DenseIntegerRow.value, ConstructedIntegerRow.value]

theorem evaluateConstructedRow_cost {q : ℕ} (row : ConstructedIntegerRow q) :
    (evaluateConstructedRow row).2 = row.work+3*q+2 := by
  simp only [evaluateConstructedRow, chargedMap_cost_eq, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, List.length_ofFn, evaluateInteger_cost, ConstructedIntegerRow.work]
  omega

/-- Compile a retained row to concrete integer arrays. No evaluation of its AST
is delegated to an unspecified cost-free interpretation. -/
def compileRetainedRow {q : ℕ} (row : ConstructedIntegerRow q × ℕ) : DenseIntegerRow q × ℕ :=
  let out := evaluateConstructedRow row.1
  (out.1,row.2+out.2)

theorem compileRetainedRow_value {q : ℕ} (row : ConstructedIntegerRow q × ℕ) :
    (compileRetainedRow row).1.value = row.1.value := evaluateConstructedRow_value _

theorem compileRetainedRow_cost {q : ℕ} (row : ConstructedIntegerRow q × ℕ) :
    (compileRetainedRow row).2 = row.2+row.1.work+3*q+2 := by
  simp only [compileRetainedRow, evaluateConstructedRow_cost]; omega

end MOR34
