import MOR34.PrefixEpigraph

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

def encodeCounts (z : Counts q) : Fin q → ℤ := fun j => z j

def decodeCounts (z : Fin q → ℤ) : Counts q := fun j => (z j).toNat

def IntegerCountBounds (z : Fin q → ℤ) : Prop :=
  ∀ j, 0 ≤ z j ∧ z j ≤ (m j : ℤ)

theorem integerCountBounds_encode (z : Counts q) :
    IntegerCountBounds (m := m) (encodeCounts z) ↔ BoundedCounts (m := m) z := by
  simp [IntegerCountBounds, encodeCounts, BoundedCounts]

theorem decodeCounts_bounded (z : Fin q → ℤ) (hz : IntegerCountBounds (m := m) z) :
    BoundedCounts (m := m) (decodeCounts z) := by
  intro j
  have h := hz j
  dsimp [decodeCounts]
  omega

theorem encode_decodeCounts (z : Fin q → ℤ) (hz : IntegerCountBounds (m := m) z) :
    encodeCounts (decodeCounts z) = z := by
  funext j
  exact Int.toNat_of_nonneg (hz j).1

theorem decode_encodeCounts (z : Counts q) : decodeCounts (encodeCounts z) = z := by
  funext j
  simp [decodeCounts, encodeCounts]

/-- The actual linear inequalities and equality, in integer count and epigraph variables. -/
def CountEpigraph (P : Model m) (z y : Fin q → ℤ) : Prop :=
  IntegerCountBounds (m := m) z ∧
  (∑ j, P.coefficient j * z j) = P.rhs ∧
  (∀ j (t : Fin (m j)), prefixLine (fun u => P.weight ⟨j, u⟩) t (z j) ≤ y j) ∧
  (∑ j, y j) ≤ P.capacity

theorem tight_prefix_epigraph (P : Model m) (hWF : WellFormed P)
    (z : Counts q) (hz : BoundedCounts (m := m) z) :
    Tight P (prefixSet z) ↔ ∃ y, CountEpigraph P (encodeCounts z) y := by
  have hval : candidateValue P (prefixSet z) = ∑ j, P.coefficient j * (z j : ℤ) := by
    rw [candidateValue_counts, counts_prefixSet z hz]
    simp only [mul_comm]
  constructor
  · rintro ⟨hf, he⟩
    obtain ⟨y, hy, hb⟩ := (prefix_feasible_epigraph P hWF z hz).mp hf
    exact ⟨y, (integerCountBounds_encode z).mpr hz, hval ▸ he, hy, hb⟩
  · rintro ⟨y, _, he, hy, hb⟩
    exact ⟨(prefix_feasible_epigraph P hWF z hz).mpr ⟨y, hy, hb⟩, hval.symm ▸ he⟩

/-- Arbitrary additional restrictions are preserved, with no relaxation to real counts. -/
theorem restricted_count_epigraph (P : Model m) (hWF : WellFormed P)
    (R : (Fin q → ℤ) → Prop) :
    (∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧ R (encodeCounts z)) ↔
      ∃ z y : Fin q → ℤ, CountEpigraph P z y ∧ R z := by
  constructor
  · rintro ⟨z, hz, ht, hr⟩
    obtain ⟨y, hy⟩ := (tight_prefix_epigraph P hWF z hz).mp ht
    exact ⟨encodeCounts z, y, hy, hr⟩
  · rintro ⟨z, y, he, hr⟩
    have hb := decodeCounts_bounded z he.1
    have hid := encode_decodeCounts z he.1
    refine ⟨decodeCounts z, hb, ?_, ?_⟩
    · apply (tight_prefix_epigraph P hWF _ hb).mpr
      exact ⟨y, hid.symm ▸ he⟩
    · exact hid.symm ▸ hr

/-- A finite rational linear restriction on the original count coordinates. -/
def RationalRestrictions {r : ℕ} (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ)
    (z : Fin q → ℤ) : Prop := ∀ i, (∑ j, A i j * (z j : ℚ)) ≤ b i

theorem restricted_linear_epigraph {r : ℕ} (P : Model m) (hWF : WellFormed P)
    (A : Fin r → Fin q → ℚ) (b : Fin r → ℚ) :
    (∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧
      RationalRestrictions A b (encodeCounts z)) ↔
    ∃ z y : Fin q → ℤ, CountEpigraph P z y ∧ RationalRestrictions A b z :=
  restricted_count_epigraph P hWF (RationalRestrictions A b)

def paritySubstitution (ε : Fin q → Fin 2) (v : Fin q → ℤ) : Fin q → ℤ :=
  fun j => 2 * v j + ((ε j).val : ℤ)

theorem count_parity_substitution (z : Counts q) (ε : Fin q → Fin 2) :
    (∀ j, z j % 2 = (ε j).val) ↔ ∃ v, encodeCounts z = paritySubstitution ε v := by
  constructor
  · intro he
    refine ⟨fun j => (z j / 2 : ℕ), ?_⟩
    funext j
    have h := Nat.mod_add_div (z j) 2
    have hp := he j
    dsimp [encodeCounts, paritySubstitution]
    omega
  · rintro ⟨v, hv⟩ j
    have h := congrFun hv j
    have hε := (ε j).isLt
    dsimp [encodeCounts, paritySubstitution] at h
    omega

/-- Parity replaces the count coordinates; it introduces no new integer coordinates. -/
theorem parity_restricted_epigraph (P : Model m) (hWF : WellFormed P)
    (ε : Fin q → Fin 2) (R : (Fin q → ℤ) → Prop) :
    (∃ z : Counts q, BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧
      (∀ j, z j % 2 = (ε j).val) ∧ R (encodeCounts z)) ↔
    ∃ v y : Fin q → ℤ, CountEpigraph P (paritySubstitution ε v) y ∧
      R (paritySubstitution ε v) := by
  constructor
  · rintro ⟨z, hb, ht, hp, hr⟩
    obtain ⟨v, hv⟩ := (count_parity_substitution z ε).mp hp
    obtain ⟨y, hy⟩ := (tight_prefix_epigraph P hWF z hb).mp ht
    exact ⟨v, y, hv ▸ hy, hv ▸ hr⟩
  · rintro ⟨v, y, he, hr⟩
    let z := decodeCounts (paritySubstitution ε v)
    have hb := decodeCounts_bounded (paritySubstitution ε v) he.1
    have hz := encode_decodeCounts (paritySubstitution ε v) he.1
    refine ⟨z, hb, ?_, ?_, ?_⟩
    · apply (tight_prefix_epigraph P hWF z hb).mpr
      exact ⟨y, hz.symm ▸ he⟩
    · exact (count_parity_substitution z ε).mpr ⟨v, hz⟩
    · exact hz.symm ▸ hr

theorem epigraph_variable_count (q : ℕ) : Fintype.card (Fin q ⊕ Fin q) = 2 * q := by
  simp; omega

end MOR34
