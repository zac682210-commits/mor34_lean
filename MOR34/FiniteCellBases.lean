import MOR34.SelectedSpan
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

theorem countReal_injective : Function.Injective (@countReal q) := by
  intro z w h
  funext j
  have hj : (z j : ℝ) = (w j : ℝ) := congrFun h j
  exact_mod_cast hj

/-- Finite-dimensional existence, not an algorithm or an ILP complexity claim. -/
theorem finite_count_affine_basis (C : Set (Counts q)) :
    ∃ B : Finset (Counts q), (↑B : Set (Counts q)) ⊆ C ∧ B.card ≤ q + 1 ∧
      ∀ z ∈ C, countReal z ∈ affineSpan ℝ (countReal '' (↑B : Set (Counts q))) := by
  classical
  obtain ⟨T, hT, heq, hi⟩ := exists_affineIndependent ℝ (Fin q → ℝ) (countReal '' C)
  have htfin := finite_set_of_fin_dim_affineIndependent ℝ hi
  letI : Fintype T := htfin.fintype
  have hbfin : (countReal ⁻¹' T).Finite := Set.Finite.preimage countReal_injective.injOn htfin
  let B := hbfin.toFinset
  have hb (z : Counts q) : z ∈ B ↔ countReal z ∈ T := by simp [B]
  have hBC : (↑B : Set (Counts q)) ⊆ C := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hT ((hb z).mp hz)
    have hwz : w = z := countReal_injective he
    simpa [hwz] using hw
  have himage : countReal '' (↑B : Set (Counts q)) = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hb z).mp hz
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hT hy
      exact ⟨z, (hb z).mpr hy, rfl⟩
  have hcard : B.card ≤ Fintype.card T := by
    let f : B → T := fun z => ⟨countReal z.val, (hb z.val).mp z.property⟩
    have hinj : Function.Injective f := by
      intro z w he
      apply Subtype.ext
      exact countReal_injective (congrArg Subtype.val he)
    simpa using Fintype.card_le_of_injective f hinj
  have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : T → (Fin q → ℝ)))) ≤ q := by
    simpa using (vectorSpan ℝ (Set.range ((↑) : T → (Fin q → ℝ)))).finrank_le
  refine ⟨B, hBC, le_trans hcard (le_trans hi.card_le_finrank_succ (Nat.add_le_add_right hd 1)), ?_⟩
  intro z hz
  rw [himage, heq]
  exact subset_affineSpan ℝ _ ⟨z, hz, rfl⟩

/-- The basis contract used by the span theorem is inhabited for every model. -/
theorem small_cellBasisSelection_exists (P : Model m) :
    ∃ S : CellBasisSelection P, ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1 := by
  classical
  let ex : (ε : Parity q) → (∃ z, TightParity P ε z) → ParityExtrema P ε :=
    fun ε hn => Classical.choice (parityExtrema_exists P ε hn)
  have hb : ∀ ε hn mode, ∃ B : Finset (Counts q),
      (↑B : Set (Counts q)) ⊆ parityCellSet P ε (ex ε hn) mode ∧ B.card ≤ q + 1 ∧
      ∀ z ∈ parityCellSet P ε (ex ε hn) mode,
        countReal z ∈ affineSpan ℝ (countReal '' (↑B : Set (Counts q))) :=
    fun ε hn mode => finite_count_affine_basis _
  choose B hmem hcard hspan using hb
  exact ⟨⟨ex, B, hmem, hspan⟩, hcard⟩

theorem cellBasisSelection_exists (P : Model m) : Nonempty (CellBasisSelection P) := by
  obtain ⟨S, _⟩ := small_cellBasisSelection_exists P
  exact ⟨S⟩

noncomputable def selectionCell (P : Model m) (S : CellBasisSelection P)
    (i : CellIndex q) : Finset (Counts q) := by
  classical
  exact if hn : ∃ z, TightParity P i.1 z then S.basis i.1 hn i.2 else ∅

noncomputable def selectionFinset (P : Model m) (S : CellBasisSelection P) : Finset (Counts q) := by
  classical
  exact Finset.univ.biUnion (selectionCell P S)

theorem selectionFinset_coe (P : Model m) (S : CellBasisSelection P) :
    (↑(selectionFinset P S) : Set (Counts q)) = selectedCounts P S := by
  classical
  ext z
  simp only [selectionFinset, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hn : ∃ w, TightParity P i.1 w
    · exact ⟨i.1, hn, i.2, by simpa [selectionCell, hn] using hi⟩
    · simp [selectionCell, hn] at hi
  · rintro ⟨ε, hn, mode, hz⟩
    exact ⟨(ε, mode), by simpa [selectionCell, hn] using hz⟩

theorem selectionFinset_card (P : Model m) (S : CellBasisSelection P)
    (hsmall : ∀ ε hn mode, (S.basis ε hn mode).card ≤ q + 1) :
    (selectionFinset P S).card ≤ (q + 1) * 6 ^ q := by
  classical
  have hc : ∀ i : CellIndex q, (selectionCell P S i).card ≤ q + 1 := by
    intro i
    by_cases hn : ∃ z, TightParity P i.1 z
    · simpa [selectionCell, hn] using hsmall i.1 hn i.2
    · simp [selectionCell, hn]
  calc
    (selectionFinset P S).card ≤ ∑ i : CellIndex q, (selectionCell P S i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : CellIndex q, q + 1 := Finset.sum_le_sum (fun i _ => hc i)
    _ = (q + 1) * 6 ^ q := by simp [cell_index_card, mul_comm]

/-- Parameter-bounded retained prefixes exist and, with adjacent directions, recover all tight rows. -/
theorem small_selected_span (P : Model m) (hWF : WellFormed P) :
    ∃ S : CellBasisSelection P,
      (selectionFinset P S).card ≤ (q + 1) * 6 ^ q ∧
      augmentedSpan (tightPointSet P) = augmentedSpan (selectedPoints P S) ⊔
        (adjacentDirectionSpan P).map zeroAugment := by
  obtain ⟨S, hs⟩ := small_cellBasisSelection_exists P
  exact ⟨S, selectionFinset_card P S hs, selected_augmented_span P hWF S⟩

end MOR34
