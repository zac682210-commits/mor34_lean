import MOR34.FiniteTable
import MOR34.SearchedExtrema

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ} {P : Model m} {ε : Parity q}

/-- Store each attained witness once and obtain endpoints from those stored witnesses. -/
def storedParityExtrema (e : ParityExtrema P ε) : ParityExtrema P ε := by
  let lower := materializeFin (fun j => materializeFin (e.lowerWitness j))
  let upper := materializeFin (fun j => materializeFin (e.upperWitness j))
  have hl : lower = e.lowerWitness := by simp [lower]
  have hu : upper = e.upperWitness := by simp [upper]
  exact {
    low := fun j => lower j j
    high := fun j => upper j j
    lowerWitness := lower
    upperWitness := upper
    lower_mem := fun j => by simpa only [hl] using e.lower_mem j
    upper_mem := fun j => by simpa only [hu] using e.upper_mem j
    lower_eq := fun _ => rfl
    upper_eq := fun _ => rfl
    bounds := fun z hz j => by simpa only [hl, hu, e.lower_eq, e.upper_eq] using e.bounds z hz j
  }

theorem storedParityExtrema_eq (e : ParityExtrema P ε) : storedParityExtrema e = e := by
  have hl : (fun j => e.lowerWitness j j) = e.low := funext e.lower_eq
  have hu : (fun j => e.upperWitness j j) = e.high := funext e.upper_eq
  unfold storedParityExtrema
  simp only [materializeFin_eq]
  cases e
  dsimp at hl hu ⊢
  cases hl
  cases hu
  rfl

end MOR34
