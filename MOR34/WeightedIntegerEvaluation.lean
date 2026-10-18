import MOR34.ExpressionBitEnvelope

namespace MOR34

/-- Local bit-operation charges supplied by established integer arithmetic.
The interface makes no assumption on the whole MOR34 computation. -/
structure IntegerArithmeticCharge where
  atom : ℤ → ℕ
  add : ℤ → ℤ → ℕ
  mul : ℤ → ℤ → ℕ
  neg : ℤ → ℕ

def IntegerArithmeticCharge.Bounded (A : IntegerArithmeticCharge) (B K : ℕ) : Prop :=
  (∀ z, signedIntegerBits z ≤ B → A.atom z ≤ K) ∧
  (∀ x y, signedIntegerBits x ≤ B → signedIntegerBits y ≤ B → A.add x y ≤ K) ∧
  (∀ x y, signedIntegerBits x ≤ B → signedIntegerBits y ≤ B → A.mul x y ≤ K) ∧
  (∀ z, signedIntegerBits z ≤ B → A.neg z ≤ K)

/-- The same retained values drive the operation and its local bit charge. -/
def weightedEvaluateInteger (A : IntegerArithmeticCharge) : IntegerConstruction → ℤ × ℕ
  | .atom z => (z,A.atom z)
  | .add a b => let x := weightedEvaluateInteger A a; let y := weightedEvaluateInteger A b
      (x.1+y.1,x.2+y.2+A.add x.1 y.1)
  | .mul a b => let x := weightedEvaluateInteger A a; let y := weightedEvaluateInteger A b
      (x.1*y.1,x.2+y.2+A.mul x.1 y.1)
  | .neg a => let x := weightedEvaluateInteger A a; (-x.1,x.2+A.neg x.1)

theorem weightedEvaluateInteger_value (A : IntegerArithmeticCharge) (e : IntegerConstruction) :
    (weightedEvaluateInteger A e).1 = e.value := by
  induction e <;> simp_all [weightedEvaluateInteger,IntegerConstruction.value]

theorem weightedEvaluateInteger_cost (A : IntegerArithmeticCharge) (e : IntegerConstruction)
    (B K : ℕ) (hA : A.Bounded B K)
    (hb : ∀ t, ConstructionSubterm t e → signedIntegerBits t.value ≤ B) :
    (weightedEvaluateInteger A e).2 ≤ e.work*K := by
  induction e with
  | atom z =>
      simpa [weightedEvaluateInteger,IntegerConstruction.work] using hA.1 z (hb _ (.refl _))
  | add a b ia ib =>
      have ha := ia (fun t ht => hb t (.addLeft ht))
      have hc := ib (fun t ht => hb t (.addRight ht))
      have ho := hA.2.1 a.value b.value (hb a (.addLeft (.refl a))) (hb b (.addRight (.refl b)))
      simp only [weightedEvaluateInteger,weightedEvaluateInteger_value,IntegerConstruction.work]
      nlinarith
  | mul a b ia ib =>
      have ha := ia (fun t ht => hb t (.mulLeft ht))
      have hc := ib (fun t ht => hb t (.mulRight ht))
      have ho := hA.2.2.1 a.value b.value (hb a (.mulLeft (.refl a))) (hb b (.mulRight (.refl b)))
      simp only [weightedEvaluateInteger,weightedEvaluateInteger_value,IntegerConstruction.work]
      nlinarith
  | neg a ia =>
      have ha := ia (fun t ht => hb t (.neg ht))
      have ho := hA.2.2.2 a.value (hb a (.neg (.refl a)))
      simp only [weightedEvaluateInteger,weightedEvaluateInteger_value,IntegerConstruction.work]
      nlinarith

/-- The intermediate-value bound discharges all operand-size premises of the
local arithmetic contract. No final output-only magnitude estimate is used. -/
theorem weightedEvaluateInteger_cost_of_literals (A : IntegerArithmeticCharge)
    (e : IntegerConstruction) (M K : ℕ) (hM : e.LiteralsBounded M)
    (hA : A.Bounded (e.work*Nat.clog 2 (M+2)+2) K) :
    (weightedEvaluateInteger A e).2 ≤ e.work*K :=
  weightedEvaluateInteger_cost A e _ K hA
    (fun t ht => constructionSubterm_bits ht M hM)

end MOR34
