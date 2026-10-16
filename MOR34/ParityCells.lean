import MOR34.PrefixAffine
import Mathlib.Data.Finset.Max

namespace MOR34

variable {q : ℕ} {m : Fin q → ℕ}
abbrev Parity (q : ℕ) := Fin q → Fin 2
abbrev CellMode (q : ℕ) := Fin q → Fin 3
abbrev BoundedProfile (m : Fin q → ℕ) := (j : Fin q) → Fin (m j + 1)
def profileCounts (x : BoundedProfile m) : Counts q := fun j => (x j).val

def TightParity (P : Model m) (ε : Parity q) (z : Counts q) : Prop :=
  BoundedCounts (m := m) z ∧ Tight P (prefixSet z) ∧ ∀ j, z j % 2 = (ε j).val

noncomputable def parityProfiles (P : Model m) (ε : Parity q) : Finset (BoundedProfile m) := by
  classical
  exact Finset.univ.filter fun x => TightParity P ε (profileCounts x)

theorem tightParity_profile (P : Model m) (ε : Parity q) {z : Counts q}
    (hz : TightParity P ε z) : ∃ x ∈ parityProfiles P ε, profileCounts x = z := by
  classical
  let x : BoundedProfile m := fun j => ⟨z j, by have := hz.1 j; omega⟩
  have hx : profileCounts x = z := rfl
  exact ⟨x, by simpa [parityProfiles, hx] using hz, hx⟩

structure ParityExtrema (P : Model m) (ε : Parity q) where
  low : Counts q
  high : Counts q
  lowerWitness : Fin q → Counts q
  upperWitness : Fin q → Counts q
  lower_mem : ∀ j, TightParity P ε (lowerWitness j)
  upper_mem : ∀ j, TightParity P ε (upperWitness j)
  lower_eq : ∀ j, lowerWitness j j = low j
  upper_eq : ∀ j, upperWitness j j = high j
  bounds : ∀ z, TightParity P ε z → ∀ j, low j ≤ z j ∧ z j ≤ high j

theorem parityExtrema_exists (P : Model m) (ε : Parity q)
    (hne : ∃ z, TightParity P ε z) : Nonempty (ParityExtrema P ε) := by
  classical
  have hlocal : ∀ j : Fin q, ∃ l h zl zh,
      TightParity P ε zl ∧ TightParity P ε zh ∧ zl j = l ∧ zh j = h ∧
      ∀ z, TightParity P ε z → l ≤ z j ∧ z j ≤ h := by
    intro j
    let values := (parityProfiles P ε).image (fun x => profileCounts x j)
    have hv : values.Nonempty := by
      obtain ⟨z, hz⟩ := hne
      obtain ⟨x, hx, he⟩ := tightParity_profile P ε hz
      exact ⟨profileCounts x j, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    obtain ⟨xl, hxl, hel⟩ := Finset.mem_image.mp (values.min'_mem hv)
    obtain ⟨xh, hxh, heh⟩ := Finset.mem_image.mp (values.max'_mem hv)
    refine ⟨values.min' hv, values.max' hv, profileCounts xl, profileCounts xh,
      ?_, ?_, hel, heh, ?_⟩
    · exact (Finset.mem_filter.mp hxl).2
    · exact (Finset.mem_filter.mp hxh).2
    · intro z hz
      obtain ⟨x, hx, he⟩ := tightParity_profile P ε hz
      have hval : z j ∈ values := Finset.mem_image.mpr ⟨x, hx, congrFun he j⟩
      exact ⟨values.min'_le _ hval, values.le_max' _ hval⟩
  choose l h zl zh hzl hzh hel heh hb using hlocal
  exact ⟨⟨l, h, zl, zh, hzl, hzh, hel, heh, fun z hz j => hb j z hz⟩⟩

def CellCondition (l h : Counts q) (mode : CellMode q) (z : Counts q) : Prop :=
  ∀ j, if mode j = 0 then z j = l j else
    if mode j = 1 then l j + 2 ≤ z j ∧ z j + 2 ≤ h j else z j = h j

def cellLow (l h : Counts q) (mode : CellMode q) : Counts q :=
  fun j => if mode j = 0 then l j else if mode j = 1 then l j + 2 else h j

def cellHigh (l h : Counts q) (mode : CellMode q) : Counts q :=
  fun j => if mode j = 0 then l j else if mode j = 1 then h j - 2 else h j

theorem cell_bounds {l h z : Counts q} {mode : CellMode q} (hc : CellCondition l h mode z) :
    (∀ j, cellLow l h mode j ≤ z j) ∧ (∀ j, z j ≤ cellHigh l h mode j) := by
  constructor <;> intro j <;> have hj := hc j
  all_goals
    by_cases h0 : mode j = 0
    · simp [cellLow, cellHigh, h0] at hj ⊢
      omega
    · by_cases h1 : mode j = 1
      · simp [cellLow, cellHigh, h0, h1] at hj ⊢
        omega
      · simp [cellLow, cellHigh, h0, h1] at hj ⊢
        omega

theorem actual_cell_slopes (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (e : ParityExtrema P ε) (mode : CellMode q) :
    ∃ s : Fin q → (ExchangeComponent P → ℝ), ∀ j (u : Fin (m j)),
      cellLow e.low e.high mode j ≤ u.val → u.val < cellHigh e.low e.high mode j →
      unitVector (componentLabel P ⟨j, u⟩) = s j := by
  classical
  have hl : ∀ j, ∃ s : ExchangeComponent P → ℝ, ∀ u : Fin (m j),
      cellLow e.low e.high mode j ≤ u.val → u.val < cellHigh e.low e.high mode j →
      unitVector (componentLabel P ⟨j, u⟩) = s := by
    intro j
    by_cases hn : ∃ a : Fin (m j), cellLow e.low e.high mode j ≤ a.val ∧
        a.val < cellHigh e.low e.high mode j
    · obtain ⟨a, hal, hah⟩ := hn
      have hm : mode j = 1 := by
        by_cases h0 : mode j = 0
        · simp [cellLow, cellHigh, h0] at hal hah
          omega
        · by_contra h1
          simp [cellLow, cellHigh, h0, h1] at hal hah
          omega
      have h0 : mode j ≠ 0 := by rw [hm]; decide
      simp [cellLow, cellHigh, h0, hm] at hal hah
      refine ⟨unitVector (componentLabel P ⟨j, a⟩), ?_⟩
      intro u hul huh
      simp [cellLow, cellHigh, h0, hm] at hul huh
      have hpar : SameParity (e.lowerWitness j) (e.upperWitness j) :=
        fun k => ((e.lower_mem j).2.2 k).trans ((e.upper_mem j).2.2 k).symm
      have hc := parity_interior_connected P hWF (e.lowerWitness j) (e.upperWitness j)
        (e.lower_mem j).1 (e.upper_mem j).1 (e.lower_mem j).2.1 (e.upper_mem j).2.1
        hpar j u a
        (by rw [e.lower_eq]; omega) (by rw [e.upper_eq]; omega)
        (by rw [e.lower_eq]; omega) (by rw [e.upper_eq]; omega)
      exact congrArg unitVector ((componentLabel_eq_iff_class_connected P j u a).mpr hc)
    · exact ⟨0, fun u hu hv => False.elim (hn ⟨u, hu, hv⟩)⟩
  choose s hs using hl
  exact ⟨s, hs⟩

/-- Actual parity cells admit an affine map; label constancy is proved, not assumed. -/
theorem actual_cell_affine (P : Model m) (hWF : WellFormed P) (ε : Parity q)
    (e : ParityExtrema P ε) (mode : CellMode q) :
    ∃ f : (Fin q → ℝ) →ᵃ[ℝ] (ExchangeComponent P → ℝ), ∀ z,
      TightParity P ε z → CellCondition e.low e.high mode z →
      f (countReal z) = componentCountMap P (pointVector (prefixSet z)) := by
  obtain ⟨s, hs⟩ := actual_cell_slopes P hWF ε e mode
  refine ⟨affineBoxMap (componentCountMap P (pointVector (prefixSet (cellLow e.low e.high mode))))
    (cellLow e.low e.high mode) s, ?_⟩
  intro z hz hc
  exact prefix_affine_on_box P _ _ s hs z hz.1 (cell_bounds hc).1 (cell_bounds hc).2

end MOR34
