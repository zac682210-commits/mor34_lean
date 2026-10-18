import MOR34.WeightedParityEnvelope

namespace MOR34
variable {q r : ℕ} {m : Fin q → ℕ}

theorem parityOperandEnvelope_polynomial (q n L M : ℕ) (hq : q ≤ n) (hML : M ≤ 2^L) :
    (2*q+7)*(12*(n+L+2)*Nat.clog 2 (uniformRowRadius q (n+1) M+2)+2)+2 ≤
      2000*(n+L+2)^4 := by
  let S := n+L+2
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hl := (uniformRowRadius_clog q (n+1) M (by omega)).trans
    (uniformRowBits_polynomial q n M L hq hML)
  have hh := Nat.mul_le_mul_left (12*S) hl
  change 12*S*Nat.clog 2 (uniformRowRadius q (n+1) M+2) ≤ 12*S*(14*S^2) at hh
  have h3 : 1 ≤ S^3 := Nat.one_le_pow _ _ hS
  have h4 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have hi : 12*S*Nat.clog 2 (uniformRowRadius q (n+1) M+2)+2 ≤ 170*S^3 := by
    change Nat.clog 2 (uniformRowRadius q (n+1) M+2) ≤ 14*S^2 at hl
    nlinarith only [hh,h3]
  have hc : 2*q+7 ≤ 6*S := by dsimp [S]; omega
  have ht := Nat.mul_le_mul hc hi
  change (2*q+7)*(12*S*Nat.clog 2 (uniformRowRadius q (n+1) M+2)+2)+2 ≤ 2000*S^4
  nlinarith only [ht,h4]

/-- A complete count-row compilation price: retained constructor reads,
original expression evaluation, and the shared dense parity transform. -/
theorem weightedBuiltCountParity_polynomial (P : Model m) (Q : Fin r → Fin q → ℤ)
    (b : Fin r → ℤ) (R : ℕ) (ε : Parity q) (k : CountRow m r)
    (n L M H a : ℕ) (hq : q ≤ n) (hm : ∀ j, m j ≤ n)
    (hR : R ≤ 4*(n+1)^2) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (hc : ∀ j, (P.coefficient j).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (hQ : ∀ i j, (Q i j).natAbs ≤ uniformRowRadius q (n+1) M)
    (hb : ∀ i, (b i).natAbs ≤ uniformRowRadius q (n+1) M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (2000*(n+L+2)^4) (H*(2000*(n+L+2)^4)^a)) :
    (sharedWeightedCompileParityRow A (builtCountRow P Q b R k) ε).2 ≤
      (24*H*2000^a+200)*(n+L+2)^(4*a+3) := by
  let S := n+L+2
  let K := H*(2000*S^4)^a
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hrad := uniformRowRadius_dominates q (n+1) M (by omega) hM
  have hMR : M ≤ uniformRowRadius q (n+1) M := by omega
  have hl : (builtCountRow P Q b R k).1.LiteralsBounded (uniformRowRadius q (n+1) M) := by
    rw [builtCountRow_value]
    exact countRowConstruction_literals P Q b _ (by omega)
      (fun j => by have hj := hm j; omega) (fun i => (hw i).trans hMR)
      (fun j => (hc j).trans hMR) (hr.trans hMR) (hcap.trans hMR) hQ hb k
  have hwork : (builtCountRow P Q b R k).1.work ≤ 12*S := by
    rw [builtCountRow_value]
    have hh := countRowConstruction_work P Q b n hm k
    dsimp [S]
    omega
  have he := sharedWeightedCompileParityRow_cost A (builtCountRow P Q b R k) ε
    (uniformRowRadius q (n+1) M) (12*S) K (by omega) hl hwork
    (IntegerArithmeticCharge.Bounded.mono A hA (parityOperandEnvelope_polynomial q n L M hq hML))
  have hbuild := builtCountRow_cost P Q b n R hq hm hR k
  have hN : n+1 ≤ S := by dsimp [S]; omega
  have hbuild' := hbuild.trans (Nat.mul_le_mul_left 128 (pow_le_pow_left' hN 3))
  have hcoef : 12*S+8*q+4 ≤ 24*S := by dsimp [S]; omega
  have hquad : q*(q+6)+7*q+7 ≤ 20*S^2 := by
    have hqS : q ≤ S := by dsimp [S]; omega
    nlinarith
  have hmul := Nat.mul_le_mul_right K hcoef
  have heq : 24*S*K = (24*H*2000^a)*S^(4*a+1) := by
    dsimp [K]
    rw [mul_pow,← pow_mul,pow_succ]
    ring
  rw [heq] at hmul
  have hp₁ : S^(4*a+1) ≤ S^(4*a+3) := pow_le_pow_right' hS (by omega)
  have hp₂ : S^3 ≤ S^(4*a+3) := pow_le_pow_right' hS (by omega)
  have hp₃ : S^2 ≤ S^(4*a+3) := pow_le_pow_right' hS (by omega)
  have hx := hmul.trans (Nat.mul_le_mul_left (24*H*2000^a) hp₁)
  change _ ≤ (24*H*2000^a+200)*S^(4*a+3)
  nlinarith only [he,hbuild',hquad,hx,hp₂,hp₃]

/-- Every row in the actual retained count request is compiled with the previous
bound; the tagged-row enumeration and dense-list assembly are charged too. -/
theorem weightedCompiledCountRequest_polynomial (P : Model m) (hWF : WellFormed P)
    (ε : Parity q) (Q : List (IntegerQuery q)) (R M L H a : ℕ)
    (hR : R ≤ 4*(Fintype.card (Item m)+1)^2) (hlen : Q.length ≤ 3*q+1)
    (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, (P.weight i).natAbs ≤ M) (hc : ∀ j, (P.coefficient j).natAbs ≤ M)
    (hr : P.rhs.natAbs ≤ M) (hcap : P.capacity.natAbs ≤ M)
    (hQ : ∀ t ∈ Q, (∀ j, (t.coefficient j).natAbs ≤
      uniformRowRadius q (Fintype.card (Item m)+1) M) ∧
      t.bound.natAbs ≤ uniformRowRadius q (Fintype.card (Item m)+1) M)
    (A : IntegerArithmeticCharge)
    (hA : A.Bounded (2000*(Fintype.card (Item m)+L+2)^4)
      (H*(2000*(Fintype.card (Item m)+L+2)^4)^a)) :
    (weightedCompiledCountRequest A P ε Q R).2 ≤
      (144*H*2000^a+1260)*(Fintype.card (Item m)+L+2)^(4*a+4) := by
  let n := Fintype.card (Item m)
  let S := n+L+2
  let V := (24*H*2000^a+200)*S^(4*a+3)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hrow (k : CountRow m Q.length) :
      (sharedWeightedCompileParityRow A
        (builtCountRow P (fun i j => (Q.get i).coefficient j) (fun i => (Q.get i).bound) R k) ε).2 ≤ V := by
    exact weightedBuiltCountParity_polynomial P _ _ R ε k n L M H a hq
      (fun j => class_size_le_items j) hR hM hML hw hc hr hcap
      (fun i => (hQ (Q.get i) (List.get_mem _ _)).1)
      (fun i => (hQ (Q.get i) (List.get_mem _ _)).2) A hA
  have hm := chargedMap_cost (fun k => sharedWeightedCompileParityRow A
    (builtCountRow P (fun i j => (Q.get i).coefficient j) (fun i => (Q.get i).bound) R k) ε)
    (countRowIndexList m Q.length) V (fun k _ => hrow k)
  have hi : (countRowIndexList m Q.length).length ≤ 6*S := by
    rw [countRowIndexList_length]
    dsimp [S,n] at *
    omega
  have hm' := hm.trans (Nat.mul_le_mul_right (V+1) hi)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S^(4*a+4) := le_self_pow₀ hS (by omega)
  have heq : 6*S*V = (144*H*2000^a+1200)*S^(4*a+4) := by
    dsimp [V]
    rw [show 4*a+4=(4*a+3)+1 by omega,pow_succ]
    ring
  have hqS : q ≤ S := by dsimp [S]; omega
  dsimp only [weightedCompiledCountRequest]
  change _ ≤ (144*H*2000^a+1260)*S^(4*a+4)
  nlinarith only [hm',hi,heq,hp,hqS,hS]

end MOR34
