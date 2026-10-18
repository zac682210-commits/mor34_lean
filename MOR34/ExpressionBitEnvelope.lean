import MOR34.EvaluatedIntegerRows
import MOR34.UniformEncoding

namespace MOR34

/-- All literals in an expression obey a fixed input/stored-scalar bound. -/
def IntegerConstruction.LiteralsBounded (M : ℕ) : IntegerConstruction → Prop
  | .atom z => z.natAbs ≤ M
  | .add a b => a.LiteralsBounded M ∧ b.LiteralsBounded M
  | .mul a b => a.LiteralsBounded M ∧ b.LiteralsBounded M
  | .neg a => a.LiteralsBounded M

theorem expression_value_magnitude (e : IntegerConstruction) (M : ℕ)
    (h : e.LiteralsBounded M) : e.value.natAbs ≤ (M+2)^e.work := by
  induction e with
  | atom z =>
      change z.natAbs ≤ M at h
      simpa [IntegerConstruction.value, IntegerConstruction.work] using
        (h.trans (show M ≤ M+2 by omega))
  | add a b ia ib =>
      have ha := ia h.1
      have hb := ib h.2
      have hpa : (M+2)^a.work ≤ (M+2)^(a.work+b.work) :=
        pow_le_pow_right' (by omega) (by omega)
      have hpb : (M+2)^b.work ≤ (M+2)^(a.work+b.work) :=
        pow_le_pow_right' (by omega) (by omega)
      have hs := (Int.natAbs_add_le a.value b.value).trans (Nat.add_le_add ha hb)
      simp only [IntegerConstruction.value, IntegerConstruction.work, pow_succ]
      nlinarith
  | mul a b ia ib =>
      have hh := Nat.mul_le_mul (ia h.1) (ib h.2)
      simp only [IntegerConstruction.value, IntegerConstruction.work, Int.natAbs_mul]
      calc
        _ ≤ (M+2)^a.work*(M+2)^b.work := hh
        _ = (M+2)^(a.work+b.work) := (pow_add _ _ _).symm
        _ ≤ _ := pow_le_pow_right' (by omega) (by omega)
  | neg a ia =>
      simp only [IntegerConstruction.value, IntegerConstruction.work, Int.natAbs_neg]
      exact (ia h).trans (pow_le_pow_right' (by omega) (by omega))

/-- A syntactic subtree, including the expression itself. -/
inductive ConstructionSubterm : IntegerConstruction → IntegerConstruction → Prop
  | refl (e) : ConstructionSubterm e e
  | addLeft {e a b} : ConstructionSubterm e a → ConstructionSubterm e (.add a b)
  | addRight {e a b} : ConstructionSubterm e b → ConstructionSubterm e (.add a b)
  | mulLeft {e a b} : ConstructionSubterm e a → ConstructionSubterm e (.mul a b)
  | mulRight {e a b} : ConstructionSubterm e b → ConstructionSubterm e (.mul a b)
  | neg {e a} : ConstructionSubterm e a → ConstructionSubterm e (.neg a)

theorem constructionSubterm_work {e t : IntegerConstruction} (h : ConstructionSubterm e t) :
    e.work ≤ t.work := by
  induction h <;> simp_all [IntegerConstruction.work] <;> omega

theorem constructionSubterm_literals {e t : IntegerConstruction} (h : ConstructionSubterm e t)
    (M : ℕ) (hM : t.LiteralsBounded M) : e.LiteralsBounded M := by
  induction h with
  | refl => exact hM
  | addLeft h ih => exact ih hM.1
  | addRight h ih => exact ih hM.2
  | mulLeft h ih => exact ih hM.1
  | mulRight h ih => exact ih hM.2
  | neg h ih => exact ih hM

/-- Every intermediate value, including rejected/unused parent computations,
is bounded, not just the final emitted coefficient. -/
theorem constructionSubterm_bits {e t : IntegerConstruction} (h : ConstructionSubterm e t)
    (M : ℕ) (hM : t.LiteralsBounded M) :
    signedIntegerBits e.value ≤ t.work*Nat.clog 2 (M+2)+2 := by
  have he := expression_value_magnitude e M (constructionSubterm_literals h M hM)
  have hm : M+2 ≤ 2^(Nat.clog 2 (M+2)) :=
    (Nat.le_pow_iff_clog_le (by decide)).mpr le_rfl
  have hp : e.value.natAbs ≤ 2^(t.work*Nat.clog 2 (M+2)) := by
    calc
      _ ≤ (M+2)^e.work := he
      _ ≤ (M+2)^t.work := pow_le_pow_right' (by omega) (constructionSubterm_work h)
      _ ≤ (2^(Nat.clog 2 (M+2)))^t.work := pow_le_pow_left' hm _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hh := magnitudeBits_le_of_power_bound e.value _ hp
  unfold signedIntegerBits
  omega

/-- Fixed-degree operation and literal-bit envelopes give fixed-degree bit
sizes throughout evaluation; the parameter need not enter that degree. -/
theorem constructionSubterm_bits_polynomial {e t : IntegerConstruction}
    (h : ConstructionSubterm e t) (M N C D a b : ℕ)
    (hM : t.LiteralsBounded M) (hwork : t.work ≤ C*(N+1)^a)
    (hbits : Nat.clog 2 (M+2) ≤ D*(N+1)^b) :
    signedIntegerBits e.value ≤ (C*D+2)*(N+1)^(a+b) := by
  have hh := (constructionSubterm_bits h M hM).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hwork hbits) 2)
  have hp : 1 ≤ (N+1)^(a+b) := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ (C*(N+1)^a)*(D*(N+1)^b)+2 := hh
    _ = (C*D)*(N+1)^(a+b)+2 := by rw [pow_add]; ring
    _ ≤ _ := by nlinarith

end MOR34
