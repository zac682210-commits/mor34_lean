import MOR34.Targets

/-!
Paper-facing OPEN specifications. No theorem proof is supplied by this module.
Review these types, including all implicit parameters, before proof development.
The full algorithm and complexity specifications remain in docs/source_map.json.
-/
namespace MOR34.PaperInterface
variable {q : ℕ} {m : Fin q → ℕ}

/-- Prefixes minimize weight among sets with the same class counts. -/
def PrefixMinimality (P : Model m) : Prop :=
  WellFormed P → ∀ S : Finset (Item m),
    weightSum P (prefixSet (counts S)) ≤ weightSum P S

/-- Paper Lemma 2, edge-closure assertion; component consequences are separate. -/
def IntervalExchange (P : Model m) : Prop :=
  WellFormed P → ∀ (j : Fin q) (r s u v : Fin (m j)),
    Exchange P j r s → r ≤ u → u < v → v ≤ s → Exchange P j u v

/-- Exact adjacent-cut target for paper Lemma 4. -/
def ParityInterior (P : Model m) : Prop := InteriorExchangeGoal P

end MOR34.PaperInterface
