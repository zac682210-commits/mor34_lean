import MOR34.InteriorExchange
import Mathlib.Logic.Relation

namespace MOR34

variable {q : ℕ} {m : Fin q → ℕ}

/-- Undirected adjacency of the exchange graph, restricted to one coefficient class. -/
def ExchangeAdj (P : Model m) (j : Fin q) (u v : Fin (m j)) : Prop :=
  Exchange P j u v ∨ Exchange P j v u

/-- Finite-path connectivity, including the length-zero path. -/
def ExchangeConnected (P : Model m) (j : Fin q) (u v : Fin (m j)) : Prop :=
  Relation.ReflTransGen (ExchangeAdj P j) u v

theorem exchangeConnected_refl (P : Model m) (j : Fin q) (u : Fin (m j)) :
    ExchangeConnected P j u u := .refl

theorem exchangeConnected_symm (P : Model m) (j : Fin q) {u v : Fin (m j)}
    (h : ExchangeConnected P j u v) : ExchangeConnected P j v u :=
  Relation.ReflTransGen.symmetric (fun _ _ h => h.symm) h

theorem exchangeConnected_trans (P : Model m) (j : Fin q) {u v w : Fin (m j)}
    (h : ExchangeConnected P j u v) (h' : ExchangeConnected P j v w) :
    ExchangeConnected P j u w := h.trans h'

/-- A path crossing a cut contains a step crossing the cut from left to right. -/
theorem path_crosses_cut {s : ℕ} {R : Fin s → Fin s → Prop} {a b : Fin s}
    (h : Relation.ReflTransGen R a b) (r : ℕ) (ha : a.val < r) (hb : r ≤ b.val) :
    ∃ u v : Fin s, R u v ∧ u.val < r ∧ r ≤ v.val := by
  induction h with
  | refl => omega
  | @tail b c hab hbc ih =>
    by_cases hbr : r ≤ b.val
    · exact ih hbr
    · exact ⟨b, c, hbc, by omega, hb⟩

/-- Every integer step in an interval gives a path through that interval. -/
theorem adjacent_chain {s : ℕ} {R : Fin s → Fin s → Prop} (a b : Fin s)
    (hab : a ≤ b)
    (hsteps : ∀ u v : Fin s, a ≤ u → u.val + 1 = v.val → v ≤ b → R u v) :
    Relation.ReflTransGen R a b := by
  have aux : ∀ k (v : Fin s), v.val = a.val + k →
      (∀ u w : Fin s, a ≤ u → u.val + 1 = w.val → w ≤ v → R u w) →
      Relation.ReflTransGen R a v := by
    intro k
    induction k with
    | zero =>
      intro v hv _
      have he : v = a := Fin.ext (by simpa using hv)
      subst v
      exact .refl
    | succ k ih =>
      intro v hv hs
      let w : Fin s := ⟨a.val + k, by omega⟩
      have hwv : w.val + 1 = v.val := by dsimp [w]; omega
      have hwle : w ≤ v := by change w.val ≤ v.val; omega
      have haw : a ≤ w := by change a.val ≤ a.val + k; omega
      have hp := ih w rfl (fun u t hau hut htw => hs u t hau hut (le_trans htw hwle))
      exact hp.tail (hs w v haw hwv le_rfl)
  apply aux (b.val - a.val) b
  · change a.val ≤ b.val at hab
    omega
  · exact hsteps

theorem connected_forces_cut (P : Model m) (hWF : WellFormed P) (j : Fin q)
    {a b : Fin (m j)} (h : ExchangeConnected P j a b) (r : ℕ)
    (ha : a.val < r) (hb : r ≤ b.val) : AdjacentExchangeCut P j r := by
  obtain ⟨u, v, huv, hur, hrv⟩ := path_crosses_cut h r ha hb
  rcases huv with huv | hvu
  · obtain ⟨_, S, hS, hnu, hyv⟩ := huv
    exact adjacent_of_crosses P hWF hS ⟨u, v, hur, hrv, hnu, hyv⟩
  · have hvu' := hvu.1
    change v.val < u.val at hvu'
    omega

theorem adjacent_cut_exchange (P : Model m) (j : Fin q) (u v : Fin (m j))
    (huv : u.val + 1 = v.val) (h : AdjacentExchangeCut P j v.val) :
    Exchange P j u v := by
  obtain ⟨u', v', hu', hv', he⟩ := h
  have h1 : u' = u := Fin.ext (by omega)
  have h2 : v' = v := Fin.ext hv'
  simpa [h1, h2] using he

theorem cuts_give_connected (P : Model m) (j : Fin q) (a b : Fin (m j))
    (hab : a ≤ b)
    (hcuts : ∀ r : ℕ, a.val < r → r ≤ b.val → AdjacentExchangeCut P j r) :
    ExchangeConnected P j a b := by
  apply adjacent_chain a b hab
  intro u v hau huv hvb
  have hcut : AdjacentExchangeCut P j v.val := hcuts v.val (by
    change a.val ≤ u.val at hau
    omega) hvb
  exact Or.inl (adjacent_cut_exchange P j u v huv hcut)

/-- Adjacent exchange cuts completely determine the component partition. -/
theorem connected_iff_cuts (P : Model m) (hWF : WellFormed P) (j : Fin q)
    (a b : Fin (m j)) (hab : a ≤ b) :
    ExchangeConnected P j a b ↔
      ∀ r : ℕ, a.val < r → r ≤ b.val → AdjacentExchangeCut P j r := by
  exact ⟨fun h r ha hb => connected_forces_cut P hWF j h r ha hb,
    cuts_give_connected P j a b hab⟩

/-- Every position between connected positions is in the same component. -/
theorem component_interval (P : Model m) (hWF : WellFormed P) (j : Fin q)
    {a b t : Fin (m j)} (h : ExchangeConnected P j a b)
    (hat : a ≤ t) (htb : t ≤ b) : ExchangeConnected P j a t := by
  apply cuts_give_connected P j a t hat
  intro r har hrt
  exact connected_forces_cut P hWF j h r har (le_trans hrt htb)

/-- The component consequence of the paper's parity-interior lemma. -/
theorem parity_interior_connected (P : Model m) (hWF : WellFormed P)
    (z w : Counts q) (hz : BoundedCounts (m := m) z) (hw : BoundedCounts (m := m) w)
    (htz : Tight P (prefixSet z)) (htw : Tight P (prefixSet w)) (hpar : SameParity z w)
    (j : Fin q) (u v : Fin (m j))
    (hu : z j + 1 ≤ u.val) (hu' : u.val + 1 < w j)
    (hv : z j + 1 ≤ v.val) (hv' : v.val + 1 < w j) :
    ExchangeConnected P j u v := by
  have ordered : ∀ a b : Fin (m j), a ≤ b → z j + 1 ≤ a.val → b.val + 1 < w j →
      ExchangeConnected P j a b := by
    intro a b hab ha hb
    apply cuts_give_connected P j a b hab
    intro r har hrb
    exact interiorExchange P hWF z w hz hw htz htw hpar j r (by omega) (by omega)
  rcases le_total u v with huv | hvu
  · exact ordered u v huv hu hv'
  · exact exchangeConnected_symm P j (ordered v u hvu hv hu')

end MOR34
