import MOR34.EvaluatedIntegerRows
import MOR34.MaterializedCountRows

namespace MOR34

/-- Each old count coefficient is read once, retained, then used both in the
new coefficient and in the parity correction. The old cost array is shared. -/
def denseParityRow {q : ℕ} (row : DenseIntegerRow q) (ε : Parity q) : DenseIntegerRow q × ℕ :=
  let data := chargedMap (fun j : Fin q =>
    let old := storedIntegerRead row.counts j.val
    ((2*old.1,old.1*(ε j).val),old.2+4)) (List.ofFn (fun j : Fin q => j))
  (⟨data.1.map Prod.fst,row.costs,row.bound-(data.1.map Prod.snd).sum⟩,
    data.2+4*q+3)

theorem denseParityRow_arrays {q : ℕ} (row : DenseIntegerRow q) (ε : Parity q) :
    (denseParityRow row ε).1 =
      ⟨List.ofFn (fun j : Fin q => 2*row.counts[j.val]?.getD 0),row.costs,
        row.bound-∑ j : Fin q, row.counts[j.val]?.getD 0*(ε j).val⟩ := by
  simp only [denseParityRow, chargedMap_value, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    storedIntegerRead, chargedListRead_value]

theorem denseParityRow_value {q : ℕ} (row : DenseIntegerRow q) (ε : Parity q) :
    (denseParityRow row ε).1.value = row.value.withParity ε := by
  rw [denseParityRow_arrays]
  simp [DenseIntegerRow.value, integerRow, CountInequality.withParity, mul_comm]

theorem denseParityRow_sized {q : ℕ} (row : DenseIntegerRow q) (ε : Parity q)
    (h : row.WellSized) : (denseParityRow row ε).1.WellSized := by
  rw [denseParityRow_arrays]
  exact ⟨List.length_ofFn, h.2⟩

theorem denseParityRow_cost {q : ℕ} (row : DenseIntegerRow q) (ε : Parity q)
    (h : row.WellSized) : (denseParityRow row ε).2 ≤ 16*(q+1)^2 := by
  have hh := chargedMap_cost (fun j : Fin q =>
    let old := storedIntegerRead row.counts j.val
    ((2*old.1,old.1*(ε j).val),old.2+4)) (List.ofFn (fun j : Fin q => j)) (q+5)
    (by intro j _; have hr := storedIntegerRead_cost row.counts j.val; rw [h.1] at hr; dsimp; omega)
  simp only [List.length_ofFn] at hh
  dsimp only [denseParityRow]
  nlinarith

/-- Evaluate the original row before parity substitution and retain that result.
Both the expression traversal and the array transformation are charged. -/
def compileParityRow {q : ℕ} (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) :
    DenseIntegerRow q × ℕ :=
  let original := compileRetainedRow row
  let out := denseParityRow original.1 ε
  (out.1,original.2+out.2+1)

theorem compileParityRow_value {q : ℕ} (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) :
    (compileParityRow row ε).1.value = row.1.value.withParity ε := by
  simp only [compileParityRow, denseParityRow_value, compileRetainedRow_value]

theorem compileParityRow_sized {q : ℕ} (row : ConstructedIntegerRow q × ℕ) (ε : Parity q) :
    (compileParityRow row ε).1.WellSized :=
  denseParityRow_sized _ _ (evaluateConstructedRow_sized _)

variable {q r : ℕ} {m : Fin q → ℕ}

theorem compiledCountParity_cost (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (n R : ℕ) (hq : q ≤ n) (hm : ∀ j, m j ≤ n) (hR : R ≤ 4*(n+1)^2)
    (ε : Parity q) (k : CountRow m r) :
    (compileParityRow (builtCountRow P A b R k) ε).2 ≤ 256*(n+1)^3 := by
  have hbuild := builtCountRow_cost P A b n R hq hm hR k
  have heval := countRowConstruction_work P A b n hm k
  have hpar := denseParityRow_cost (compileRetainedRow (builtCountRow P A b R k)).1 ε
    (evaluateConstructedRow_sized _)
  have hp : (q+1)^2 ≤ (n+1)^2 := pow_le_pow_left' (by omega) _
  dsimp only [compileParityRow]
  rw [compileRetainedRow_cost, builtCountRow_value]
  nlinarith

end MOR34
