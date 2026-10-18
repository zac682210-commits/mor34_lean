import MOR34.TracedFunctionEnumeration
import MOR34.NormalArithmeticCost

namespace MOR34

/-- Row/column maps are retained once for this rank. The product loop charges
key records, list cells, and copied append blocks, including unused keys. -/
def chargedRankKeys (s d : ℕ) (r : Fin (d+1)) : List (NormalSearchKey s d) × ℕ :=
  let rows := chargedFinFunctions r.val s
  let cols := chargedFinFunctions r.val d
  let out := chargedFlatMap (fun a => chargedMap
    (fun c => ((⟨r,a,c⟩ : NormalSearchKey s d),1)) cols.1) rows.1
  (out.1, rows.2+cols.2+out.2+2)

theorem chargedRankKeys_value (s d : ℕ) (r : Fin (d+1)) :
    (chargedRankKeys s d r).1 = (allFinFunctions r.val s).flatMap (fun a =>
      (allFinFunctions r.val d).map (fun c => (⟨r,a,c⟩ : NormalSearchKey s d))) := by
  simp [chargedRankKeys, chargedFlatMap_value, chargedMap_value, chargedFinFunctions_value]

def rankKeyBuildBudget (d : ℕ) : ℕ :=
  2*((d+3)^2*(d+1)^(d+1)) + 4*((d+1)^d)*((d+1)^d)+2

theorem rankKey_length_bound (s d : ℕ) (hs : s ≤ d) (r : Fin (d+1)) :
    (chargedRankKeys s d r).1.length ≤ ((d+1)^d)*((d+1)^d) := by
  have hr : r.val ≤ d := by omega
  have ha : s^r.val ≤ (d+1)^d :=
    (pow_le_pow_left' (by omega) _).trans (pow_le_pow_right' (by omega) hr)
  have hc : d^r.val ≤ (d+1)^d :=
    (pow_le_pow_left' (by omega) _).trans (pow_le_pow_right' (by omega) hr)
  rw [chargedRankKeys_value]
  simp only [List.length_flatMap, List.length_map, allFinFunctions_length]
  simpa using Nat.mul_le_mul ha hc

theorem chargedRankKeys_cost (s d : ℕ) (hs : s ≤ d) (r : Fin (d+1)) :
    (chargedRankKeys s d r).2 ≤ rankKeyBuildBudget d := by
  let D := (d+1)^d
  let E := (d+3)^2*(d+1)^(d+1)
  have hr : r.val ≤ d := by omega
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by omega)
  have hc : (chargedFinFunctions r.val d).1.length ≤ D := by
    rw [chargedFinFunctions_value, allFinFunctions_length]
    exact (pow_le_pow_left' (by omega) _).trans (pow_le_pow_right' (by omega) hr)
  have ha : (chargedFinFunctions r.val s).1.length ≤ D := by
    rw [chargedFinFunctions_value, allFinFunctions_length]
    exact (pow_le_pow_left' (by omega) _).trans (pow_le_pow_right' (by omega) hr)
  have cost (t : ℕ) (ht : t ≤ d) : (chargedFinFunctions r.val t).2 ≤ E := by
    apply (chargedFinFunctions_parameter_cost r.val t).trans
    apply Nat.mul_le_mul (pow_le_pow_left' (by omega) 2)
    exact (pow_le_pow_left' (by omega) _).trans (pow_le_pow_right' (by omega) (by omega))
  have hm (a : Fin r.val → Fin s) :
      (chargedMap (fun c => ((⟨r,a,c⟩ : NormalSearchKey s d),1))
        (chargedFinFunctions r.val d).1).2 ≤ 2*D := by
    exact (chargedMap_cost _ _ 1 (fun _ _ => le_rfl)).trans (by nlinarith)
  have hf := chargedFlatMap_cost
    (fun a => chargedMap (fun c => ((⟨r,a,c⟩ : NormalSearchKey s d),1))
      (chargedFinFunctions r.val d).1) (chargedFinFunctions r.val s).1 (2*D) D
    (fun a _ => hm a) (by intro a _; simpa [chargedMap_value] using hc)
  have hp := hf.trans (Nat.mul_le_mul_right (2*D+D+1) ha)
  have hrow := cost s hs
  have hcol := cost d le_rfl
  unfold chargedRankKeys rankKeyBuildBudget
  change (chargedFinFunctions r.val s).2 + (chargedFinFunctions r.val d).2 + _ + 2 ≤
    2*E+4*D*D+2
  nlinarith

def chargedNormalKeys (s d : ℕ) : List (NormalSearchKey s d) × ℕ :=
  let out := chargedFlatMap (chargedRankKeys s d) (List.finRange (d+1))
  (out.1,out.2+d+2)

theorem chargedNormalKeys_value (s d : ℕ) :
    (chargedNormalKeys s d).1 = normalSearchKeys s d := by
  simp [chargedNormalKeys, chargedFlatMap_value, chargedRankKeys_value, normalSearchKeys]

def normalKeyBuildBudget (d : ℕ) : ℕ :=
  (d+1)*(rankKeyBuildBudget d+((d+1)^d)*((d+1)^d)+2)+1

theorem chargedNormalKeys_cost (s d : ℕ) (hs : s ≤ d) :
    (chargedNormalKeys s d).2 ≤ normalKeyBuildBudget d := by
  have hh := chargedFlatMap_cost (chargedRankKeys s d) (List.finRange (d+1))
    (rankKeyBuildBudget d) (((d+1)^d)*((d+1)^d))
    (fun r _ => chargedRankKeys_cost s d hs r) (fun r _ => rankKey_length_bound s d hs r)
  simp only [List.length_finRange] at hh
  unfold chargedNormalKeys normalKeyBuildBudget
  nlinarith

/-- Candidate construction is now part of the same reference search, even if
the successful candidate occurs at the beginning of the list. -/
def matrixNormalSearchBuilt {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    Option (Fin d → Fin d → ℤ) × ℕ :=
  let keys := chargedNormalKeys s d
  (firstWitness (tryNormalKey M) keys.1,
    keys.2+firstWitnessCharge (tryNormalKey M) (normalKeyCharge M) keys.1)

theorem matrixNormalSearchBuilt_value {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ) :
    (matrixNormalSearchBuilt M).1 = matrixNormalSearch M := by
  simp [matrixNormalSearchBuilt, chargedNormalKeys_value, matrixNormalSearch]

theorem matrixNormalSearchBuilt_cost {s d : ℕ} (M : Matrix (Fin s) (Fin d) ℤ)
    (hd : 1 ≤ d) (hs : s ≤ d) :
    (matrixNormalSearchBuilt M).2 ≤
      normalKeyBuildBudget d+((d+1)*d^(2*d))*normalKeyBudget d := by
  have hk := chargedNormalKeys_cost s d hs
  have hm := matrixNormalArithmeticCharge_bound M hd hs
  simpa only [matrixNormalSearchBuilt, chargedNormalKeys_value, matrixNormalArithmeticCharge]
    using Nat.add_le_add hk hm

end MOR34
