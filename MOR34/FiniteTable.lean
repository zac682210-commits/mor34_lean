import Mathlib.Data.List.OfFn

namespace MOR34

/-- Eagerly construct a finite list, then expose lookup as a function. This specifies
stored data, but does not by itself provide a backend operation-count theorem. -/
def materializeFin {n : ℕ} {α : Type*} (f : Fin n → α) : Fin n → α :=
  let values := List.ofFn f
  fun i => values[i.val]'(by simpa using i.isLt)

@[simp] theorem materializeFin_apply {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) :
    materializeFin f i = f i := by simp [materializeFin]

@[simp] theorem materializeFin_eq {n : ℕ} {α : Type*} (f : Fin n → α) :
    materializeFin f = f := funext (materializeFin_apply f)

end MOR34
