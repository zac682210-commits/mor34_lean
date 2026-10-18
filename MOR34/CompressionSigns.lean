import MOR34.RawOutput
import Mathlib.Data.Sign

namespace MOR34
open SignType

/-- Semantic contract supplied by Frank--Tardos with radius N+1.
The external compression algorithm and its complexity are not asserted here. -/
def PreservesSmallSigns {ι : Type*} [Fintype ι] (N : ℕ) (w v : ι → ℤ) : Prop :=
  ∀ u : ι → ℤ, (∑ i, |u i|) ≤ (N : ℤ) →
    sign (∑ i, w i * u i) = sign (∑ i, v i * u i)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem smallSigns_coordinate {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 1 ≤ N) (j : ι) :
    sign (w j) = sign (v j) := by
  have hu : (∑ i : ι, |(if i = j then 1 else 0 : ℤ)|) ≤ (N : ℤ) := by
    simp only [abs_ite, abs_one, abs_zero]
    simpa using (show (1 : ℤ) ≤ N by exact_mod_cast hN)
  simpa [mul_ite] using h (fun i => if i = j then 1 else 0) hu

theorem smallSigns_difference {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 2 ≤ N) (j k : ι) :
    sign (w j - w k) = sign (v j - v k) := by
  let u : ι → ℤ := fun i => (if i = j then 1 else 0) - (if i = k then 1 else 0)
  have hu : (∑ i, |u i|) ≤ (N : ℤ) := by
    calc
      _ ≤ ∑ i : ι, (|(if i = j then 1 else 0 : ℤ)| + |(if i = k then 1 else 0 : ℤ)|) :=
        Finset.sum_le_sum (fun i _ => abs_sub _ _)
      _ = 2 := by simp [Finset.sum_add_distrib, abs_ite]
      _ ≤ N := by exact_mod_cast hN
  simpa [u, mul_sub, mul_ite, Finset.sum_sub_distrib] using h u hu

theorem smallSigns_positive {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 1 ≤ N) (j : ι) :
    0 < w j ↔ 0 < v j := by
  rw [← sign_eq_one_iff, smallSigns_coordinate h hN j, sign_eq_one_iff]

theorem smallSigns_nonnegative {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 1 ≤ N) (j : ι) :
    0 ≤ w j ↔ 0 ≤ v j := by
  rw [← sign_nonneg_iff, smallSigns_coordinate h hN j, sign_nonneg_iff]

theorem smallSigns_zero {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 1 ≤ N) (j : ι) :
    w j = 0 ↔ v j = 0 := by
  rw [← sign_eq_zero_iff, smallSigns_coordinate h hN j, sign_eq_zero_iff]

theorem smallSigns_order {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 2 ≤ N) (j k : ι) :
    w j ≤ w k ↔ v j ≤ v k := by
  have he := congrArg (fun s : SignType => s ≤ 0) (smallSigns_difference h hN j k)
  simpa only [sign_nonpos_iff, sub_nonpos] using Iff.of_eq he

theorem smallSigns_equal {N : ℕ} {w v : ι → ℤ}
    (h : PreservesSmallSigns N w v) (hN : 2 ≤ N) (j k : ι) :
    w j = w k ↔ v j = v k := by
  have he := congrArg (fun s : SignType => s = 0) (smallSigns_difference h hN j k)
  simpa only [sign_eq_zero_iff, sub_eq_zero] using Iff.of_eq he

variable {n : ℕ}

def augmentedWeights (a : Fin n → ℤ) (b : ℤ) : Option (Fin n) → ℤ
  | none => b
  | some i => a i

def binarySignTest (S : Finset (Fin n)) : Option (Fin n) → ℤ
  | none => -1
  | some i => if i ∈ S then 1 else 0

theorem binarySignTest_norm (S : Finset (Fin n)) :
    (∑ i, |binarySignTest S i|) ≤ (n+1 : ℤ) := by
  have hc : S.card ≤ n := by simpa using Finset.card_le_univ S
  have he : (∑ i, |binarySignTest S i|) = (S.card : ℤ)+1 := by
    simp [binarySignTest, Fintype.sum_option, abs_ite, add_comm]
  rw [he]
  exact_mod_cast Nat.add_le_add_right hc 1

theorem binarySignTest_dot (a : Fin n → ℤ) (b : ℤ) (S : Finset (Fin n)) :
    (∑ i, augmentedWeights a b i * binarySignTest S i) = (∑ i ∈ S, a i)-b := by
  simp [augmentedWeights, binarySignTest, Fintype.sum_option, mul_ite, sub_eq_add_neg, add_comm]

theorem compression_subset_sign {a a' : Fin n → ℤ} {b b' : ℤ}
    (h : PreservesSmallSigns (n+1) (augmentedWeights a b) (augmentedWeights a' b'))
    (S : Finset (Fin n)) :
    sign ((∑ i ∈ S, a i)-b) = sign ((∑ i ∈ S, a' i)-b') := by
  simpa only [binarySignTest_dot] using h (binarySignTest S) (binarySignTest_norm S)

theorem compression_subset_le {a a' : Fin n → ℤ} {b b' : ℤ}
    (h : PreservesSmallSigns (n+1) (augmentedWeights a b) (augmentedWeights a' b'))
    (S : Finset (Fin n)) :
    (∑ i ∈ S, a i) ≤ b ↔ (∑ i ∈ S, a' i) ≤ b' := by
  have he := congrArg (fun s : SignType => s ≤ 0) (compression_subset_sign h S)
  simpa only [sign_nonpos_iff, sub_nonpos] using Iff.of_eq he

theorem compression_subset_eq {a a' : Fin n → ℤ} {b b' : ℤ}
    (h : PreservesSmallSigns (n+1) (augmentedWeights a b) (augmentedWeights a' b'))
    (S : Finset (Fin n)) :
    (∑ i ∈ S, a i) = b ↔ (∑ i ∈ S, a' i) = b' := by
  have he := congrArg (fun s : SignType => s = 0) (compression_subset_sign h S)
  simpa only [sign_eq_zero_iff, sub_eq_zero] using Iff.of_eq he

end MOR34
