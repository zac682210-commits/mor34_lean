import MOR34.PairingAtCut
import MOR34.Exchange
import MOR34.Accounting

namespace MOR34

theorem adjacent_of_crosses {q : ℕ} {m : Fin q → ℕ}
    (P : Model m) (hWF : WellFormed P) {j : Fin q} {r : ℕ}
    {S : Finset (Item m)} (hS : Tight P S) (hc : Crosses j r S) :
    AdjacentExchangeCut P j r := by
  obtain ⟨u, v, hu, hv, hnu, hyv⟩ := hc
  have hrm : r < m j := lt_of_le_of_lt hv v.isLt
  let u' : Fin (m j) := ⟨r - 1, by omega⟩
  let v' : Fin (m j) := ⟨r, hrm⟩
  have hex : Exchange P j u v := by
    refine ⟨?_, S, hS, hnu, hyv⟩
    change u.val < v.val
    omega
  refine ⟨u', v', ?_, rfl, ?_⟩
  · dsimp [u']
    omega
  · apply intervalExchange P hWF j u v u' v' hex
    · change u.val ≤ r - 1
      omega
    · change r - 1 < r
      omega
    · exact hv

theorem interiorExchange {q : ℕ} {m : Fin q → ℕ} (P : Model m) :
    InteriorExchangeGoal P := by
  intro hWF z w hz hw htz htw hpar j r hzr hrw
  obtain ⟨U, V, hrep, hbal, hU, hV⟩ := pairingAtCut z w hz hw hpar j r hzr hrw
  rcases one_tight_of_repartition P htz htw hrep (fun i => (hbal i).1) with ht | ht
  · exact adjacent_of_crosses P hWF ht hU
  · exact adjacent_of_crosses P hWF ht hV

end MOR34
