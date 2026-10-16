-- Gate 2: Lean core only. This proves no MOR34 statement.
theorem mor34_core_smoke (n : Nat) : n = n := by
  rfl
#print axioms mor34_core_smoke
