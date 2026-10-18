import MOR34.ParityComponentSupport

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

noncomputable def oneParityComponentGenerators (P : Model m) (ε : Parity q) :
    Finset (ℝ × (ExchangeComponent P → ℝ)) := by
  classical
  exact if hn : ∃ z, TightParity P ε z then
    parityComponentGenerators P (Classical.choice (parityExtrema_exists P ε hn)) else ∅

noncomputable def allParityComponentGenerators (P : Model m) :
    Finset (ℝ × (ExchangeComponent P → ℝ)) := by
  classical
  exact Finset.univ.biUnion (oneParityComponentGenerators P)

theorem oneParityComponentGenerators_card (P : Model m) (hWF : WellFormed P) (ε : Parity q) :
    (oneParityComponentGenerators P ε).card ≤ 3*q+1 := by
  classical
  unfold oneParityComponentGenerators
  split_ifs with hn
  · exact parityComponentGenerators_card P hWF _
  · simp

theorem allParityComponentGenerators_card (P : Model m) (hWF : WellFormed P) :
    (allParityComponentGenerators P).card ≤ (3*q+1)*2^q := by
  classical
  calc
    _ ≤ ∑ ε, (oneParityComponentGenerators P ε).card := Finset.card_biUnion_le
    _ ≤ ∑ _ε : Parity q, (3*q+1) :=
      Finset.sum_le_sum (fun ε _ => oneParityComponentGenerators_card P hWF ε)
    _ = (3*q+1)*2^q := by simp [Parity, Nat.mul_comm]

theorem quotient_prefix_mem_component_generators (P : Model m) (ε : Parity q)
    (z : Counts q) (hz : TightParity P ε z) :
    pointAugment (componentCountMap P (pointVector (prefixSet z))) ∈
      Submodule.span ℝ (↑(allParityComponentGenerators P) : Set (ℝ × (ExchangeComponent P → ℝ))) := by
  classical
  have hn : ∃ z, TightParity P ε z := ⟨z,hz⟩
  let e := Classical.choice (parityExtrema_exists P ε hn)
  have hs : (↑(parityComponentGenerators P e) : Set (ℝ × (ExchangeComponent P → ℝ))) ⊆
      (↑(allParityComponentGenerators P) : Set (ℝ × (ExchangeComponent P → ℝ))) := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨ε, Finset.mem_univ _, ?_⟩
    simpa only [oneParityComponentGenerators, dif_pos hn] using hx
  exact (Submodule.span_mono hs) (parityComponentGenerators_span P e z hz)

theorem quotient_augmented_span_le_component_generators (P : Model m) (hWF : WellFormed P) :
    augmentedSpan ((componentCountMap P) '' tightPointSet P) ≤
      Submodule.span ℝ (↑(allParityComponentGenerators P) : Set (ℝ × (ExchangeComponent P → ℝ))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨_, ⟨S,hS,rfl⟩,rfl⟩,rfl⟩
  have hp := prefix_tight P hWF hS
  obtain ⟨ε,hε⟩ := tight_has_parity P (counts_bounded S) hp
  have hm := quotient_prefix_mem_component_generators P ε (counts S) hε
  rwa [componentCountMap_prefix P hS] at hm

theorem quotient_augmented_dimension_bound (P : Model m) (hWF : WellFormed P) :
    Module.finrank ℝ (augmentedSpan ((componentCountMap P) '' tightPointSet P)) ≤ (3*q+1)*2^q := by
  classical
  calc
    _ ≤ Module.finrank ℝ (Submodule.span ℝ
      (↑(allParityComponentGenerators P) : Set (ℝ × (ExchangeComponent P → ℝ)))) :=
      Submodule.finrank_mono (quotient_augmented_span_le_component_generators P hWF)
    _ ≤ (allParityComponentGenerators P).card := finrank_span_finset_le_card _
    _ ≤ (3*q+1)*2^q := allParityComponentGenerators_card P hWF

/-- Corollary 6 of the manuscript, for the actual global exchange components. -/
theorem facet_component_bound (P : Model m) (hWF : WellFormed P) (hf : DefinesFacet P) :
    Fintype.card (ExchangeComponent P) ≤ (3*q+1)*2^q := by
  obtain ⟨hT,hd⟩ := (candidate_facet_iff_dimension P hWF hf.1).mp hf.2
  have hq := tight_dimension_quotient P hWF hT
  have hc := exchangeDirectionSpan_finrank P
  have ha := augmentedSpan_finrank (hT.image (componentCountMap P))
  have hb := quotient_augmented_dimension_bound P hWF
  omega

end MOR34
