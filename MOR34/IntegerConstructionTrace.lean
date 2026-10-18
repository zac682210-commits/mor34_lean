import MOR34.ParityLinearEncoding
import MOR34.ForcedLinearEncoding
import MOR34.NormalSearchCost

namespace MOR34

/-- Expressions for a reference integer-row constructor. Literals are input or
stored-table reads; their bit/lookup cost is supplied by a standard primitive model. -/
inductive IntegerConstruction where
  | atom : ℤ → IntegerConstruction
  | add : IntegerConstruction → IntegerConstruction → IntegerConstruction
  | mul : IntegerConstruction → IntegerConstruction → IntegerConstruction
  | neg : IntegerConstruction → IntegerConstruction

def IntegerConstruction.value : IntegerConstruction → ℤ
  | .atom z => z
  | .add a b => a.value+b.value
  | .mul a b => a.value*b.value
  | .neg a => -a.value

def IntegerConstruction.work : IntegerConstruction → ℕ
  | .atom _ => 1
  | .add a b => a.work+b.work+1
  | .mul a b => a.work+b.work+1
  | .neg a => a.work+1

def sumConstruction (L : List ℤ) : IntegerConstruction :=
  L.foldr (fun z a => .add (.atom z) a) (.atom 0)

theorem sumConstruction_value (L : List ℤ) : (sumConstruction L).value = L.sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa [sumConstruction, IntegerConstruction.value] using congrArg (a+·) ih

theorem sumConstruction_work (L : List ℤ) : (sumConstruction L).work = 2*L.length+1 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      change 1+(sumConstruction L).work+1 = 2*(a::L).length+1
      rw [ih, List.length_cons]
      omega

/-- All original prefix values are constructed by finite sums, with no arithmetic
oracle hidden in the row constant. A shared table may improve this bound. -/
def prefixConstruction {n : ℕ} (w : Fin n → ℤ) (z : ℕ) : IntegerConstruction :=
  sumConstruction (((classPrefix n z).sort (· ≤ ·)).map w)

theorem prefixConstruction_value {n : ℕ} (w : Fin n → ℤ) (z : ℕ) :
    (prefixConstruction w z).value = prefixCost w z := by
  rw [prefixConstruction, sumConstruction_value]
  have hh := List.sum_toFinset w (Finset.sort_nodup (· ≤ ·) (classPrefix n z))
  simpa [prefixCost] using hh.symm

theorem prefixConstruction_work {n : ℕ} (w : Fin n → ℤ) (z : ℕ) :
    (prefixConstruction w z).work ≤ 2*n+1 := by
  rw [prefixConstruction, sumConstruction_work]
  have hh : (classPrefix n z).card ≤ n := by simpa using Finset.card_le_univ (classPrefix n z)
  simp only [List.length_map, Finset.length_sort]
  omega

/-- Integer row data before interpretation as a rational inequality. -/
structure ConstructedIntegerRow (q : ℕ) where
  counts : Fin q → IntegerConstruction
  costs : Fin q → IntegerConstruction
  bound : IntegerConstruction

def ConstructedIntegerRow.value {q : ℕ} (R : ConstructedIntegerRow q) : CountInequality q :=
  integerRow (fun j => (R.counts j).value) (fun j => (R.costs j).value) R.bound.value

def ConstructedIntegerRow.work {q : ℕ} (R : ConstructedIntegerRow q) : ℕ :=
  (∑ j, (R.counts j).work) + (∑ j, (R.costs j).work) + R.bound.work

def atomicIntegerRow {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) : ConstructedIntegerRow q :=
  ⟨fun j => .atom (a j), fun j => .atom (b j), .atom d⟩

theorem atomicIntegerRow_value {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) :
    (atomicIntegerRow a b d).value = integerRow a b d := rfl

theorem atomicIntegerRow_work {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) :
    (atomicIntegerRow a b d).work = 2*q+1 := by
  simp [ConstructedIntegerRow.work, atomicIntegerRow, IntegerConstruction.work] <;> omega

/-- Construct a parity row from a previously materialized integer row. The q
products and their sum, as well as coefficient doubling, are explicitly charged. -/
def parityRowConstruction {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) (ε : Parity q) :
    ConstructedIntegerRow q :=
  ⟨fun j => .mul (.atom (a j)) (.atom 2), fun j => .atom (b j),
    .add (.atom d) (.neg
      ((List.ofFn (fun j => IntegerConstruction.mul (.atom (a j)) (.atom (ε j).val))).foldr
        IntegerConstruction.add (.atom 0)))⟩

theorem construction_fold_value (L : List IntegerConstruction) :
    (L.foldr IntegerConstruction.add (.atom 0)).value = (L.map IntegerConstruction.value).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [IntegerConstruction.value, ih]

theorem construction_fold_work (L : List IntegerConstruction) :
    (L.foldr IntegerConstruction.add (.atom 0)).work =
      (L.map IntegerConstruction.work).sum+L.length+1 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.foldr_cons, IntegerConstruction.work, ih,
      List.map_cons, List.sum_cons, List.length_cons]; omega

theorem parityRowConstruction_value {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) (ε : Parity q) :
    (parityRowConstruction a b d ε).value = (integerRow a b d).withParity ε := by
  simp only [ConstructedIntegerRow.value, parityRowConstruction, construction_fold_value,
    IntegerConstruction.value]
  simp only [List.map_ofFn, List.sum_ofFn, integerRow, CountInequality.withParity]
  congr 1
  · funext j
    push_cast
    rfl
  · simp [Function.comp_def, IntegerConstruction.value, sub_eq_add_neg]

theorem parityRowConstruction_work {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) (ε : Parity q) :
    (parityRowConstruction a b d ε).work = 8*q+4 := by
  simp only [ConstructedIntegerRow.work, parityRowConstruction, IntegerConstruction.work,
    construction_fold_work, List.map_ofFn, List.length_ofFn, List.sum_ofFn]
  simp [IntegerConstruction.work] <;> omega

end MOR34
