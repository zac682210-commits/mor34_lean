import MOR34.EvaluatedIntegerRows

namespace MOR34
variable {q : ℕ} {m : Fin q → ℕ}

/-- Enumerate tagged row indices by finite ranges. No sorting or full pair
space is used. The class-size array is retained normalized input. -/
def forcedRowIndexList (j : Fin q) (u v : Fin (m j)) : List (ForcedRow m j u v) :=
  ((List.finRange q).map fun k => .inl (.inl (.inl k))) ++
  ((List.finRange q).map fun k => .inl (.inl (.inr k))) ++
  ((List.finRange 2).map fun k => .inl (.inr (.inl k))) ++
  ((List.finRange 2).map fun k => .inl (.inr (.inr k))) ++
  ((List.ofFn (fun k : Fin q => k)).flatMap fun k =>
    (List.finRange (m k)).map fun a => .inr (.inl ⟨k,a⟩)) ++
  ((List.finRange (pairAllowed u v).card).map fun a => .inr (.inr (.inl a))) ++
  [.inr (.inr (.inr (.inl ()))),.inr (.inr (.inr (.inr ())))]

theorem forcedRowIndexList_complete (j : Fin q) (u v : Fin (m j))
    (k : ForcedRow m j u v) : k ∈ forcedRowIndexList j u v := by
  rcases k with ((k | k) | (b | b)) | (⟨k,a⟩ | (a | (w | w)))
  all_goals simp [forcedRowIndexList, List.mem_flatMap]

theorem forcedRowIndexList_length (j : Fin q) (u v : Fin (m j)) :
    (forcedRowIndexList j u v).length =
      Fintype.card (Item m)+2*q+(pairAllowed u v).card+6 := by
  simp only [forcedRowIndexList, List.length_append, List.length_map,
    List.length_finRange, List.length_flatMap, List.map_ofFn, List.sum_ofFn,
    List.length_cons, List.length_nil]
  simp only [Item, Fintype.card_sigma, Fintype.card_fin]
  omega

def retainedForcedSystem (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ) : List (DenseIntegerRow q) × ℕ :=
  let indices := forcedRowIndexList j u v
  let out := chargedMap
    (fun k => compileRetainedRow (retainedForcedRow P j u v T vRead R k)) indices
  (out.1,out.2+8*indices.length+q+1)

theorem retainedForcedSystem_sized (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ) :
    ∀ row ∈ (retainedForcedSystem P j u v T vRead R).1, row.WellSized := by
  intro row hrow
  simp only [retainedForcedSystem, chargedMap_value, List.mem_map] at hrow
  obtain ⟨k,_,rfl⟩ := hrow
  exact evaluateConstructedRow_sized _

theorem retainedForcedSystem_iff (P : Model m) (j : Fin q) (u v : Fin (m j))
    (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ)
    (hT : T = (chargedResidualWeights P j u v R).1)
    (hv : vRead.1 = P.weight ⟨j,v⟩) (z y : Fin q → ℤ) :
    (∀ row ∈ (retainedForcedSystem P j u v T vRead R).1, row.value.Holds z y) ↔
      ∀ k : ForcedRow m j u v, (forcedRow P j u v k).Holds z y := by
  simp only [retainedForcedSystem, chargedMap_value, List.forall_mem_map,
    compileRetainedRow_value, retainedForcedRow_interpret P j u v T vRead R hT hv]
  exact ⟨fun h k => h k (forcedRowIndexList_complete j u v k),fun h k _ => h k⟩

theorem retainedForcedSystem_cost (P : Model m) (hWF : WellFormed P)
    (j : Fin q) (u v : Fin (m j)) (T : List ℤ) (vRead : ℤ × ℕ) (R : ℕ)
    (hT : T = (chargedResidualWeights P j u v R).1)
    (hv : vRead.1 = P.weight ⟨j,v⟩)
    (hR : R ≤ Fintype.card (Item m)+1) (hvc : vRead.2 ≤ Fintype.card (Item m)+1) :
    (retainedForcedSystem P j u v T vRead R).2 ≤ 512*(Fintype.card (Item m)+1)^3 := by
  let n := Fintype.card (Item m)
  have hq : q ≤ n := coefficient_classes_le_items P hWF
  have hm : ∀ k, m k ≤ n := fun k => class_size_le_items k
  have hc : (pairAllowed u v).card ≤ n :=
    (show (pairAllowed u v).card ≤ m j by simpa using Finset.card_le_univ (pairAllowed u v)).trans (hm j)
  have hlen : T.length ≤ n := by rw [hT,chargedResidualWeights_length]; exact hc
  have hrow (k : ForcedRow m j u v) :
      (compileRetainedRow (retainedForcedRow P j u v T vRead R k)).2 ≤ 64*(n+1)^2 := by
    rw [compileRetainedRow_cost, retainedForcedRow_value P j u v T vRead R hT hv]
    have hbuild := retainedForcedRow_cost P j u v T vRead n R hq hm hR hlen hvc k
    have heval := forcedRowConstruction_work P j u v n hm k
    nlinarith
  have hmap := chargedMap_cost
    (fun k => compileRetainedRow (retainedForcedRow P j u v T vRead R k))
    (forcedRowIndexList j u v) (64*(n+1)^2) (fun k _ => hrow k)
  have hi : (forcedRowIndexList j u v).length ≤ 6*(n+1) := by
    rw [forcedRowIndexList_length]; change n+2*q+(pairAllowed u v).card+6 ≤ _; omega
  have hmap' := hmap.trans (Nat.mul_le_mul_right (64*(n+1)^2+1) hi)
  dsimp only [retainedForcedSystem]
  change _ ≤ 512*(n+1)^3
  nlinarith

end MOR34
