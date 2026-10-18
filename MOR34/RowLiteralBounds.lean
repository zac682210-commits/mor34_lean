import MOR34.ExpressionBitEnvelope
import MOR34.CountConstructionCost

namespace MOR34

/-- Literal bounds refer to values actually read into the row's syntax tree. -/
def ConstructedIntegerRow.LiteralsBounded {q : ℕ} (row : ConstructedIntegerRow q) (M : ℕ) : Prop :=
  (∀ j, (row.counts j).LiteralsBounded M) ∧
  (∀ j, (row.costs j).LiteralsBounded M) ∧ row.bound.LiteralsBounded M

theorem sumConstruction_literals (L : List ℤ) (M : ℕ)
    (h : ∀ z ∈ L, z.natAbs ≤ M) : (sumConstruction L).LiteralsBounded M := by
  induction L with
  | nil => simp [sumConstruction,IntegerConstruction.LiteralsBounded]
  | cons z L ih =>
      exact ⟨h z (by simp), ih (fun a ha => h a (by simp [ha]))⟩

theorem prefixConstruction_literals {n : ℕ} (w : Fin n → ℤ) (z M : ℕ)
    (h : ∀ i, (w i).natAbs ≤ M) : (prefixConstruction w z).LiteralsBounded M := by
  apply sumConstruction_literals
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact h i

theorem integerPick_magnitude {q : ℕ} (j k : Fin q) (a : ℤ) (M : ℕ)
    (h : a.natAbs ≤ M) : (integerPick j a k).natAbs ≤ M := by
  simp only [integerPick]
  split_ifs
  · exact h
  · simp

theorem atomicIntegerRow_literals {q : ℕ} (a b : Fin q → ℤ) (d : ℤ) (M : ℕ)
    (ha : ∀ j, (a j).natAbs ≤ M) (hb : ∀ j, (b j).natAbs ≤ M) (hd : d.natAbs ≤ M) :
    (atomicIntegerRow a b d).LiteralsBounded M := ⟨ha,hb,hd⟩

variable {q r : ℕ} {m : Fin q → ℕ}

theorem prefixRowConstruction_literals (P : Model m) (j : Fin q) (t : Fin (m j))
    (M : ℕ) (hM : 1 ≤ M) (hm : m j ≤ M)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) :
    (prefixRowConstruction P j t).LiteralsBounded M := by
  refine ⟨?_,?_,?_⟩
  · intro k
    exact integerPick_magnitude j k _ M (hw _)
  · intro k
    exact integerPick_magnitude j k (-1) M (by simpa using hM)
  · change ((P.weight ⟨j,t⟩).natAbs ≤ M ∧ (t.val : ℤ).natAbs ≤ M) ∧
      (prefixConstruction (fun u => P.weight ⟨j,u⟩) t.val).LiteralsBounded M
    exact ⟨⟨hw _,by simp; omega⟩,prefixConstruction_literals _ _ M (fun i => hw _)⟩

theorem countRowConstruction_literals (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (M : ℕ) (hM : 1 ≤ M) (hm : ∀ j, m j ≤ M)
    (hw : ∀ i, (P.weight i).natAbs ≤ M)
    (ha : ∀ j, (P.coefficient j).natAbs ≤ M)
    (hb : P.rhs.natAbs ≤ M) (hc : P.capacity.natAbs ≤ M)
    (hA : ∀ i j, (A i j).natAbs ≤ M) (hB : ∀ i, (b i).natAbs ≤ M)
    (k : CountRow m r) : (countRowConstruction P A b k).LiteralsBounded M := by
  have hzero : ∀ j : Fin q, ((0 : Fin q → ℤ) j).natAbs ≤ M := fun _ => Nat.zero_le _
  rcases k with (j | j) | ((u | u) | (⟨j,t⟩ | (u | i)))
  · exact atomicIntegerRow_literals _ _ _ M
      (fun k => integerPick_magnitude j k (-1) M (by simpa using hM)) hzero (Nat.zero_le _)
  · exact atomicIntegerRow_literals _ _ _ M
      (fun k => integerPick_magnitude j k 1 M (by simpa using hM)) hzero (by simpa using hm j)
  · exact atomicIntegerRow_literals _ _ _ M ha hzero hb
  · exact ⟨ha,hzero,hb⟩
  · exact prefixRowConstruction_literals P j t M hM (hm j) hw
  · exact atomicIntegerRow_literals _ _ _ M hzero (fun _ => by simpa using hM) hc
  · exact atomicIntegerRow_literals _ _ _ M (hA i) hzero (hB i)

/-- The generic intermediate-value lemma applies to every expression actually
created by a count-row constructor, including prefixes and intermediate products. -/
theorem countRow_subterm_bits (P : Model m) (A : Fin r → Fin q → ℤ) (b : Fin r → ℤ)
    (M n : ℕ) (hmn : ∀ j, m j ≤ n) (hM : 1 ≤ M) (hm : ∀ j, m j ≤ M)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (ha : ∀ j, (P.coefficient j).natAbs ≤ M)
    (hb : P.rhs.natAbs ≤ M) (hc : P.capacity.natAbs ≤ M)
    (hA : ∀ i j, (A i j).natAbs ≤ M) (hB : ∀ i, (b i).natAbs ≤ M)
    (k : CountRow m r) (e : IntegerConstruction)
    (he : ConstructionSubterm e (countRowConstruction P A b k).bound) :
    signedIntegerBits e.value ≤ (4*q+2*n+6)*Nat.clog 2 (M+2)+2 := by
  have hl := countRowConstruction_literals P A b M hM hm hw ha hb hc hA hB k
  have hh := constructionSubterm_bits he M hl.2.2
  have ht : (countRowConstruction P A b k).bound.work ≤ (countRowConstruction P A b k).work := by
    unfold ConstructedIntegerRow.work; omega
  exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _
    (ht.trans (countRowConstruction_work P A b n hmn k))) 2)

end MOR34
