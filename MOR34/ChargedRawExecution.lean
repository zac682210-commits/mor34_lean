import MOR34.CompleteReferenceApplication
import MOR34.DenseRawPipeline

namespace MOR34
variable {q n : ℕ} {m : Fin q → ℕ}

/-- Relabel one binary point using the stored item permutation. This is a
standard finite-array primitive; its semantic transport is proved separately. -/
structure RelabelPointOperation (e : Item m ≃ Fin n) where
  run : Finset (Item m) → Finset (Fin n) × ℕ
  value : ∀ S, (run S).1 = S.map e.toEmbedding

/-- Emit and collect a small basis as a finite list. -/
structure RelabelBasisOperations (m : Fin q → ℕ) (n : ℕ) where
  emit : Finset (Finset (Item m)) → List (Finset (Item m)) × ℕ
  emit_value : ∀ B, (emit B).1 = orderedBinarySets B
  collect : List (Finset (Fin n)) → Finset (Finset (Fin n)) × ℕ
  collect_value : ∀ L, (collect L).1 = L.toFinset

def chargedRelabelDecision (e : Item m ≃ Fin n) (ops : RelabelPointOperation e) :
    RecognitionOutput m → RawDecision n × ℕ
  | .invalid S => let t := ops.run S; (.invalid t.1,t.2+1)
  | .empty => (.empty,1)
  | .supported S d f => let t := ops.run S; (.supported t.1 d f,t.2+1)

theorem chargedRelabelDecision_value (e : Item m ≃ Fin n) (ops : RelabelPointOperation e)
    (out : RecognitionOutput m) :
    (chargedRelabelDecision e ops out).1 = relabelDecision e out := by
  cases out <;> simp [chargedRelabelDecision,relabelDecision,ops.value]

theorem chargedRelabelDecision_cost (e : Item m ≃ Fin n) (ops : RelabelPointOperation e)
    (C : ℕ) (hc : ∀ S, (ops.run S).2 ≤ C) (out : RecognitionOutput m) :
    (chargedRelabelDecision e ops out).2 ≤ C+1 := by
  cases out <;> simp only [chargedRelabelDecision]
  · exact Nat.add_le_add_right (hc _) 1
  · omega
  · exact Nat.add_le_add_right (hc _) 1

def chargedRelabelOutput (e : Item m ≃ Fin n) (point : RelabelPointOperation e)
    (basis : RelabelBasisOperations m n) (out : NormalizedOutput m) : RawOutput n × ℕ :=
  let decision := chargedRelabelDecision e point out.decision
  let listed := basis.emit out.basis
  let mapped := chargedMap point.run listed.1
  let collected := basis.collect mapped.1
  (⟨decision.1,collected.1⟩,decision.2+listed.2+mapped.2+collected.2+1)

theorem chargedRelabelOutput_value (e : Item m ≃ Fin n) (point : RelabelPointOperation e)
    (basis : RelabelBasisOperations m n) (out : NormalizedOutput m) :
    (chargedRelabelOutput e point basis out).1 = relabelOutput e out := by
  simp only [chargedRelabelOutput,chargedRelabelDecision_value,basis.collect_value,
    chargedMap_value,basis.emit_value,point.value,List.toFinset_map,
    relabelOutput,relabelBasis]
  congr 1
  ext S
  simp [List.mem_toFinset,orderedBinarySets_mem,Finset.mem_map,Equiv.finsetCongr]

structure RelabelLocalBounds (e : Item m ≃ Fin n) (point : RelabelPointOperation e)
    (basis : RelabelBasisOperations m n) (C E J : ℕ) : Prop where
  point : ∀ S, (point.run S).2 ≤ C
  emit : ∀ B, B.card ≤ n+1 → (basis.emit B).2 ≤ E
  collect : ∀ L, L.length ≤ n+1 → (basis.collect L).2 ≤ J

theorem chargedRelabelOutput_cost (e : Item m ≃ Fin n) (point : RelabelPointOperation e)
    (basis : RelabelBasisOperations m n) (C E J : ℕ)
    (h : RelabelLocalBounds e point basis C E J) (out : NormalizedOutput m)
    (hB : out.basis.card ≤ n+1) :
    (chargedRelabelOutput e point basis out).2 ≤ C+E+(n+1)*(C+1)+J+2 := by
  have hd := chargedRelabelDecision_cost e point C h.point out.decision
  have he := h.emit out.basis hB
  have hl : (basis.emit out.basis).1.length ≤ n+1 := by
    rw [basis.emit_value,orderedBinarySets_length]
    exact hB
  have hm := (chargedMap_cost point.run (basis.emit out.basis).1 C (fun S _ => h.point S)).trans
    (Nat.mul_le_mul_right (C+1) hl)
  have hc := h.collect (chargedMap point.run (basis.emit out.basis).1).1 (by
    simpa only [chargedMap_value,List.length_map] using hl)
  dsimp only [chargedRelabelOutput]
  omega

/-- The original item labeling is restored after the single retained normalized
execution. The full output (witness, dimension, facet flag and basis) is moved. -/
def RawNormalization.runCharged {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (R : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives N.model solve)
    (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
    (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n) :
    RawOutput n × ℕ :=
  let core := chargedNormalizedExecution N.model N.wellFormed R solve hs A ops ranker rankOps setOps
  let out := chargedRelabelOutput N.itemEquiv point basis core.1
  (out.1,core.2+out.2+1)

theorem chargedRawExecution_correct {a c : Fin n → ℤ} {b d : ℤ}
    (N : RawNormalization a c b d) (R : ℕ)
    (solve : List (DenseIntegerRow N.classes) → Option (IntegerRowSolution N.classes) × ℕ)
    (hs : DenseRowSolverSpec solve) (A : DenseCellPrimitives N.model solve)
    (ops : PointOperations N.sizes) (ranker : ExactIntegerRank N.sizes)
    (rankOps : BinaryRankOperations ranker) (setOps : BinaryCollectionOperations N.sizes)
    (point : RelabelPointOperation N.itemEquiv) (basis : RelabelBasisOperations N.sizes n) :
    (N.runCharged R solve hs A ops ranker rankOps setOps point basis).1.Correct a c b d := by
  have hh := relabelOutput_correct N.model N.itemEquiv a c N.weight_eq N.coefficient_eq _
    (chargedNormalizedExecution_correct N.model N.wellFormed R solve hs A ops ranker rankOps setOps)
  simpa only [RawNormalization.runCharged,chargedRelabelOutput_value,N.capacity_eq,N.rhs_eq] using hh

end MOR34
