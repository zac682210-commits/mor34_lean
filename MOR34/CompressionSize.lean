import MOR34.CompressionParameter
import MOR34.UniformEncoding

namespace MOR34

/-- The numerical coefficient bound in the cited Frank--Tardos theorem,
with r=n+1 and N=n+2. This does not assert an implementation of that theorem. -/
def compressionRadius (n : ℕ) : ℕ :=
  2^(4*(n+1)^3) * (n+2)^((n+1)*((n+1)+2))

theorem compressionRadius_power_bound (n : ℕ) : compressionRadius n ≤ 2^(7*(n+1)^3) := by
  let r := n+1
  have hr : 1 ≤ r := by omega
  have hp : r+1 ≤ 2^r := Nat.lt_two_pow_self r
  have he : 4*r^3+r*(r*(r+2)) ≤ 7*r^3 := by
    have hh := Nat.mul_le_mul_left (r*r) hr
    nlinarith
  calc
    compressionRadius n = 2^(4*r^3)*(r+1)^(r*(r+2)) := rfl
    _ ≤ 2^(4*r^3)*(2^r)^(r*(r+2)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _)
    _ = 2^(4*r^3+r*(r*(r+2))) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2^(7*r^3) := Nat.pow_le_pow_right (by decide) he

theorem compressed_integer_bits (n : ℕ) (z : ℤ) (h : z.natAbs ≤ compressionRadius n) :
    signedIntegerBits z ≤ 7*(n+1)^3+2 := by
  have hh := magnitudeBits_le_of_power_bound z _ (h.trans (compressionRadius_power_bound n))
  unfold signedIntegerBits
  omega

def rawIntegerPayload {n : ℕ} (a c : Fin n → ℤ) (b d : ℤ) : ℕ :=
  (∑ i : Option (Fin n), signedIntegerBits (augmentedWeights a b i)) +
  ∑ i : Option (Fin n), signedIntegerBits (augmentedWeights c d i)

/-- An explicit fourth-degree bound for the two compressed coefficient vectors.
It counts signed integer payload, not a self-delimiting byte format. -/
theorem compressed_payload_bound {n : ℕ} (a c : Fin n → ℤ) (b d : ℤ)
    (ha : ∀ i, (augmentedWeights a b i).natAbs ≤ compressionRadius n)
    (hc : ∀ i, (augmentedWeights c d i).natAbs ≤ compressionRadius n) :
    rawIntegerPayload a c b d ≤ 18*(n+1)^4 := by
  have hs (w : Option (Fin n) → ℤ) (hw : ∀ i, (w i).natAbs ≤ compressionRadius n) :
      (∑ i, signedIntegerBits (w i)) ≤ (n+1)*(7*(n+1)^3+2) := by
    calc
      _ ≤ ∑ _i : Option (Fin n), (7*(n+1)^3+2) :=
        Finset.sum_le_sum (fun i _ => compressed_integer_bits n (w i) (hw i))
      _ = _ := by simp
  have h1 := hs (augmentedWeights a b) ha
  have h2 := hs (augmentedWeights c d) hc
  have hn : 1 ≤ (n+1)^3 := by positivity
  have hmul := Nat.mul_le_mul_left (4*(n+1)) hn
  unfold rawIntegerPayload
  nlinarith [show (n+1)^4 = (n+1)*(n+1)^3 by ring]

/-- The polynomial exponent remains independent of the parameter after compression.
The hypothesis is a bound on a supplied algorithm's cost; its proof is a separate obligation. -/
theorem compression_cost_substitution (n L F c cost : ℕ)
    (hL : L ≤ 18*(n+1)^4) (hcost : cost ≤ F*(n+L+1)^c) :
    cost ≤ (F*19^c)*(n+1)^(4*c) := by
  have hn : n+1 ≤ (n+1)^4 := by
    exact le_self_pow₀ (by omega) (by decide)
  have hh : n+L+1 ≤ 19*(n+1)^4 := by omega
  calc
    cost ≤ F*(n+L+1)^c := hcost
    _ ≤ F*(19*(n+1)^4)^c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _)
    _ = (F*19^c)*(n+1)^(4*c) := by rw [mul_pow, ← pow_mul]; ring

end MOR34
