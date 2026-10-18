import MOR34.CompressionTransport

namespace MOR34

/-- Equal fibers give equal image cardinalities, without requiring either map injective. -/
theorem image_card_of_equal_fibers {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ) (h : ∀ i j, f i = f j ↔ g i = g j) :
    (S.image f).card = (S.image g).card := by
  classical
  let rep (v : β) (hv : v ∈ S.image f) : α := (Finset.mem_image.mp hv).choose
  have hr (v : β) (hv : v ∈ S.image f) : rep v hv ∈ S ∧ f (rep v hv) = v :=
    (Finset.mem_image.mp hv).choose_spec
  apply Finset.card_bij (fun v hv => g (rep v hv))
  · intro v hv
    exact Finset.mem_image.mpr ⟨rep v hv, (hr v hv).1, rfl⟩
  · intro v hv w hw he
    exact (hr v hv).2.symm.trans (((h _ _).mpr he).trans (hr w hw).2)
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    have hv : f i ∈ S.image f := Finset.mem_image.mpr ⟨i,hi,rfl⟩
    exact ⟨f i, hv, (h _ _).mp (hr (f i) hv).2⟩

variable {n : ℕ}

theorem positive_values_as_image (c : Fin n → ℤ) :
    ((Finset.univ.image c).filter (fun v => 0 < v)) =
      (Finset.univ.filter (fun i => 0 < c i)).image c := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩; exact ⟨i,hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,rfl⟩,hi⟩

theorem compression_positive_parameter {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}
    (hn : 0 < n) (h : RawCompression a c a' c' b d b' d') :
    ((Finset.univ.image c).filter (fun v => 0 < v)).card =
      ((Finset.univ.image c').filter (fun v => 0 < v)).card := by
  have hp : ∀ i, 0 < c i ↔ 0 < c' i :=
    fun i => smallSigns_positive h.candidateSigns (by omega) (some i)
  have he : ∀ i j, c i = c j ↔ c' i = c' j :=
    fun i j => smallSigns_equal h.candidateSigns (by omega) (some i) (some j)
  rw [positive_values_as_image, positive_values_as_image]
  have hs : Finset.univ.filter (fun i => 0 < c i) = Finset.univ.filter (fun i => 0 < c' i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp]
  rw [← hs]
  exact image_card_of_equal_fibers _ c c' he

theorem compression_all_classes {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}
    (hn : 0 < n) (h : RawCompression a c a' c' b d b' d') :
    (Finset.univ.image c).card = (Finset.univ.image c').card :=
  image_card_of_equal_fibers _ c c'
    (fun i j => smallSigns_equal h.candidateSigns (by omega) (some i) (some j))

theorem compression_coefficient_order {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}
    (hn : 0 < n) (h : RawCompression a c a' c' b d b' d') (i j : Fin n) :
    c i ≤ c j ↔ c' i ≤ c' j :=
  smallSigns_order h.candidateSigns (by omega) (some i) (some j)

theorem compression_coefficient_zero {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}
    (h : RawCompression a c a' c' b d b' d') (i : Fin n) : c i = 0 ↔ c' i = 0 :=
  smallSigns_zero h.candidateSigns (by omega) (some i)

/-- Compression followed by the previously verified solver-relative algorithm returns
an output correct for the original instance, with its original coefficient parameter. -/
theorem compressed_original_output_contract {a c a' c' : Fin n → ℤ} {b d b' d' : ℤ}
    (hn : 0 < n) (h : RawCompression a c a' c' b d b' d')
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hab : ∀ i, a i ≤ b) (hc : ∀ i, 0 ≤ c i) :
    ∃ N : RawNormalization a' c' b' d',
      N.classes ≤ ((Finset.univ.image c).filter (fun v => 0 < v)).card + 1 ∧
      ∀ s : RowPrimitives N.model, (N.runExecutable s).Correct a c b d := by
  obtain ⟨ha',hb',hab',hc'⟩ := compression_hypotheses hn h ha hb hab hc
  let N := normalizeRawExecutable hn a' c' b' d' ha' hb' hab' hc'
  refine ⟨N, ?_, fun s => (compression_output h _).mpr (executableRawPipeline_correct N s)⟩
  rw [compression_positive_parameter hn h]
  exact rawNormalization_parameter N

end MOR34
