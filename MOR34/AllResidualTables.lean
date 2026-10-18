import MOR34.ConstructedAdjacentIndices
import MOR34.ResidualTableConstruction

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Store every residual-weight table before any forced-row constructor uses it. -/
def chargedAllResidualTables (P : Model m) (R : ℕ) :
    List (AdjacentPair m × List ℤ) × ℕ :=
  let indices := chargedAdjacentIndices m
  let out := chargedMap (fun e : AdjacentPair m =>
    let t := chargedResidualWeights P e.val.1 e.val.2.1 e.val.2.2 R
    ((e,t.1),t.2+1)) indices.1
  (out.1,indices.2+out.2)

theorem chargedAllResidualTables_length (P : Model m) (R : ℕ) :
    (chargedAllResidualTables P R).1.length ≤ Fintype.card (Item m) := by
  simpa [chargedAllResidualTables, chargedMap_value] using
    (chargedAdjacentIndices_length (m := m))

theorem chargedAllResidualTables_contains (P : Model m) (R : ℕ) (e : AdjacentPair m) :
    (e,((pairAllowed e.val.2.1 e.val.2.2).sort (· ≤ ·)).map
      (fun i => P.weight ⟨e.val.1,i⟩)) ∈ (chargedAllResidualTables P R).1 := by
  simp only [chargedAllResidualTables, chargedMap_value, List.mem_map]
  exact ⟨e,chargedAdjacentIndices_complete e,by simp [chargedResidualWeights_value]⟩

theorem chargedAllResidualTables_cost (P : Model m) (hWF : WellFormed P)
    (R : ℕ) (hR : R ≤ Fintype.card (Item m)+1) :
    (chargedAllResidualTables P R).2 ≤ 18*(Fintype.card (Item m)+1)^3 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ j, m j ≤ n := fun j => class_size_le_items j
  have hi := chargedAdjacentIndices_cost n hq hm
  have hl := chargedAdjacentIndices_length (m := m)
  have ht (e : AdjacentPair m) :
      (chargedResidualWeights P e.val.1 e.val.2.1 e.val.2.2 R).2 ≤ 8*(n+1)^2 :=
    residual_table_polynomial_work P _ _ _ n R (hm _) hR
  have hh := chargedMap_cost (fun e : AdjacentPair m =>
    let t := chargedResidualWeights P e.val.1 e.val.2.1 e.val.2.2 R
    ((e,t.1),t.2+1)) (chargedAdjacentIndices m).1 (8*(n+1)^2+1)
    (by intro e _; have h := ht e; dsimp; omega)
  have hb := hh.trans (Nat.mul_le_mul_right (8*(n+1)^2+1+1) hl)
  unfold chargedAllResidualTables
  change _ ≤ 18*(n+1)^3
  nlinarith

end MOR34
