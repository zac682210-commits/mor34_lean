import MOR34.ComputedSearchPayload
import MOR34.BasicRowPayload

namespace MOR34

/-- A deliberately coarse bound used only to exhibit a parameter-independent degree. -/
theorem clog_two_le_input (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.le_pow_iff_clog_le (by decide)).mp (Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))

theorem uniformRowBits_polynomial (q n M L : ℕ) (hq : q ≤ n) (hM : M ≤ 2^L) :
    uniformRowBits q (n+1) M ≤ 14*(n+L+2)^2 := by
  have hlog : Nat.clog 2 (M+1) ≤ L+1 := by
    apply (Nat.le_pow_iff_clog_le (by decide)).mp
    have hp : 1 ≤ 2^L := Nat.one_le_pow L 2 (by decide)
    rw [pow_succ]
    omega
  have hn := clog_two_le_input (n+1)
  have hq' := clog_two_le_input (q+1)
  have hx : (Nat.clog 2 (q+1)+Nat.clog 2 (n+1))*(q+1) ≤ 2*(n+1)^2 := by
    calc
      _ ≤ (2*(n+1))*(n+1) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  unfold uniformRowBits
  nlinarith

/-- Dense integer systems for all three query families have degree at most four. -/
theorem dense_query_payload_polynomial (q n M L rows : ℕ)
    (hq : q ≤ n) (hM : M ≤ 2^L) (hr : rows ≤ 6*(n+L+2)) :
    rows*((2*q+1)*uniformRowBits q (n+1) M) ≤ 168*(n+L+2)^4 := by
  have hb := uniformRowBits_polynomial q n M L hq hM
  have hc : 2*q+1 ≤ 2*(n+L+2) := by omega
  calc
    _ ≤ (6*(n+L+2))*((2*(n+L+2))*(14*(n+L+2)^2)) :=
      Nat.mul_le_mul hr (Nat.mul_le_mul hc hb)
    _ = _ := by ring

theorem cell_payload_polynomial (q n M L : ℕ) (hq : q ≤ n) (hM : M ≤ 2^L) :
    (n+5*q+4)*((2*q+1)*uniformRowBits q (n+1) M) ≤ 168*(n+L+2)^4 :=
  dense_query_payload_polynomial q n M L _ hq hM (by omega)

theorem forced_payload_polynomial (q n M L k : ℕ) (hq : q ≤ n) (hk : k ≤ n)
    (hM : M ≤ 2^L) :
    (n+2*q+k+6)*((2*q+1)*uniformRowBits q (n+1) M) ≤ 168*(n+L+2)^4 :=
  dense_query_payload_polynomial q n M L _ hq hM (by omega)

theorem violation_payload_polynomial (q n M L : ℕ) (hq : q ≤ n) (hM : M ≤ 2^L) :
    (n+2*q+2)*((2*q+1)*uniformRowBits q (n+1) M) ≤ 168*(n+L+2)^4 :=
  dense_query_payload_polynomial q n M L _ hq hM (by omega)

theorem searchStates_mono {α : Type*} [DecidableEq α]
    (oracle : Finset α → Option α) (I J : Finset α → Prop)
    (h : ∀ B, I B → J B) (fuel : ℕ) (B : Finset α) :
    SearchStates oracle I fuel B → SearchStates oracle J fuel B := by
  induction fuel generalizing B with
  | zero => intro _; trivial
  | succ r ih =>
    intro hh
    refine ⟨h B hh.1, ?_⟩
    cases he : oracle B with
    | none => simp [he]
    | some z =>
      simp only [he]
      apply ih
      simpa only [he] using hh.2

variable {q : ℕ} {m : Fin q → ℕ}

def PolynomialCellSearchPayload (P : Model m) (ε : Parity q) (e : ParityExtrema P ε)
    (mode : CellMode q) (L : ℕ) (B : Finset (Counts q)) : Prop :=
  ∀ t ∈ outsideQueries (computedCountForms B),
    ∃ a b : CountRow m (t :: cellQueries e.low e.high mode).length → Fin q → ℤ,
      ∃ d : CountRow m (t :: cellQueries e.low e.high mode).length → ℤ,
      (∀ k, (countRow P (queryCoefficients (t :: cellQueries e.low e.high mode))
        (queryBounds (t :: cellQueries e.low e.high mode)) k).withParity ε = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤ 168*(Fintype.card (Item m)+L+2)^4

/-- This bound follows the actual recursive normal-search states, not an arbitrary oracle input. -/
theorem computedPipeline_polynomial_payload (P : Model m) (hWF : WellFormed P)
    (solve : Parity q → List (IntegerQuery q) → Option (IntegerRowSolution q))
    (hs : ParityRowSolverSpec P solve) (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (ε : Parity q) (hn : ∃ z, TightParity P ε z) (mode : CellMode q) :
    SearchStates
      (linearSpanOracle (rowCellOracle solve ε (rowSearchedExtrema P hWF solve hs ε hn) mode) computedCountForms)
      (PolynomialCellSearchPayload P ε (rowSearchedExtrema P hWF solve hs ε hn) mode L) (q+1) ∅ := by
  apply searchStates_mono _
    (ComputedCellSearchPayload P ε (rowSearchedExtrema P hWF solve hs ε hn) mode
      (Fintype.card (Item m)+1) M) _ ?_ _ _
    (computedNormalPipeline_payload_states P hWF solve hs M hM hw hc hb hd ε hn mode)
  intro B hB t ht
  obtain ⟨a,b,d,he,hbits⟩ := hB t ht
  exact ⟨a,b,d,he,hbits.trans (cell_payload_polynomial q _ M L (coefficient_classes_le_items P hWF) hML)⟩

/-- Actual forced-exchange rows, with witnesses retained in the encoding statement. -/
theorem forcedSystem_polynomial_payload (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (j : Fin q) (u v : Fin (m j)) :
    ∃ a b : ForcedRow m j u v → Fin q → ℤ, ∃ d : ForcedRow m j u v → ℤ,
      (∀ k, forcedRow P j u v k = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤ 168*(Fintype.card (Item m)+L+2)^4 := by
  have hm : ∀ j, m j ≤ Fintype.card (Item m)+1 :=
    fun j => (class_size_le_items j).trans (Nat.le_succ _)
  obtain ⟨a,b,d,he,hbits⟩ := forced_system_payload P (Fintype.card (Item m)+1) M
    (by omega) hM hm hw hc hb hd j u v
  have hk : (pairAllowed u v).card ≤ Fintype.card (Item m) := by
    have hh := Finset.card_le_univ (pairAllowed u v)
    simp only [Fintype.card_fin] at hh
    exact hh.trans (class_size_le_items j)
  exact ⟨a,b,d,he,hbits.trans (forced_payload_polynomial q _ M L _
    (coefficient_classes_le_items P hWF) hk hML)⟩

theorem violationSystem_polynomial_payload (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) :
    ∃ a b : ViolationRow m → Fin q → ℤ, ∃ d : ViolationRow m → ℤ,
      (∀ k, violationRow P k = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤ 168*(Fintype.card (Item m)+L+2)^4 := by
  have hm : ∀ j, m j ≤ Fintype.card (Item m)+1 :=
    fun j => (class_size_le_items j).trans (Nat.le_succ _)
  obtain ⟨a,b,d,he,hbits⟩ := violation_system_payload P (Fintype.card (Item m)+1) M
    (by omega) hM hm hw hc hb hd
  exact ⟨a,b,d,he,hbits.trans (violation_payload_polynomial q _ M L
    (coefficient_classes_le_items P hWF) hML)⟩

end MOR34
