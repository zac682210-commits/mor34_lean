import MOR34.ClassPairing

namespace MOR34

theorem pairingAtCut {q : ℕ} {m : Fin q → ℕ} : PairingAtCutGoal (m := m) := by
  classical
  intro z w hz hw hpar j r hzr hrw
  have hlocal : ∀ i : Fin q, ∃ U V : Finset (Fin (m i)),
      ClassPairSpec (m i) (z i) (w i) U V ∧
        (i = j → ClassCross r U ∧ ClassCross r V) := by
    intro i
    by_cases hij : i = j
    · subst i
      obtain ⟨U, V, hs, hU, hV⟩ := class_pair_cross (hw j) (hpar j) hzr hrw
      exact ⟨U, V, hs, fun _ => ⟨hU, hV⟩⟩
    · obtain ⟨U, V, hs⟩ := class_pair (hz i) (hw i) (hpar i)
      exact ⟨U, V, hs, fun h => False.elim (hij h)⟩
  choose U V hs hc using hlocal
  refine ⟨assemble U, assemble V, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [indicator, prefixSet] using (hs i.1).1 i.2
  · intro i
    rw [counts_assemble, counts_assemble]
    exact (hs i).2
  · obtain ⟨u, v, hu, hv, hn, hy⟩ := (hc j rfl).1
    exact ⟨u, v, hu, hv, by simpa using hn, by simpa using hy⟩
  · obtain ⟨u, v, hu, hv, hn, hy⟩ := (hc j rfl).2
    exact ⟨u, v, hu, hv, by simpa using hn, by simpa using hy⟩

end MOR34
