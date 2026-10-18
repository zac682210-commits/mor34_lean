import MOR34.TracedListConstruction
import MOR34.StoredEdgeWitnesses

namespace MOR34

def chargedFilterMap {α β : Type*} (f : α → Option β × ℕ) : List α → List β × ℕ
  | [] => ([],0)
  | a::L => let x := f a; let y := chargedFilterMap f L
      (match x.1 with | none => y.1 | some b => b::y.1, x.2+y.2+1)

theorem chargedFilterMap_value {α β : Type*} (f : α → Option β × ℕ) (L : List α) :
    (chargedFilterMap f L).1 = L.filterMap (fun a => (f a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : (f a).1 <;> simp [chargedFilterMap, ih, h]

theorem chargedFilterMap_cost {α β : Type*} (f : α → Option β × ℕ) (L : List α)
    (C : ℕ) (hf : ∀ a ∈ L, (f a).2 ≤ C) :
    (chargedFilterMap f L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [chargedFilterMap]
  | cons a L ih =>
      have ha := hf a (by simp)
      have hL := ih (fun b hb => hf b (by simp [hb]))
      simp only [chargedFilterMap, List.length_cons]
      nlinarith

variable {q : ℕ} {m : Fin q → ℕ}

/-- Only the successor of each item is inspected; all ordered pairs need not
be enumerated. The proof field is erased from this executable constructor. -/
def adjacentAt (j : Fin q) (u : Fin (m j)) : Option (AdjacentPair m) :=
  if h : u.val+1 < m j then some ⟨⟨j,u,⟨u.val+1,h⟩⟩,rfl⟩ else none

theorem adjacentAt_complete (e : AdjacentPair m) :
    adjacentAt e.val.1 e.val.2.1 = some e := by
  rcases e with ⟨⟨j,u,v⟩,h⟩
  have hn : u.val+1 < m j := by rw [h]; exact v.isLt
  have hv : (⟨u.val+1,hn⟩ : Fin (m j)) = v := Fin.ext h
  simp [adjacentAt, hn, hv]

def chargedClassAdjacencies (j : Fin q) : List (AdjacentPair m) × ℕ :=
  let out := chargedFilterMap (fun u : Fin (m j) => (adjacentAt j u,2)) (List.finRange (m j))
  (out.1,out.2+m j+1)

theorem chargedClassAdjacencies_length (j : Fin q) :
    (chargedClassAdjacencies (m := m) j).1.length ≤ m j := by
  simp only [chargedClassAdjacencies, chargedFilterMap_value]
  exact (List.length_filterMap_le _ _).trans_eq List.length_finRange

theorem chargedClassAdjacencies_cost (j : Fin q) :
    (chargedClassAdjacencies (m := m) j).2 ≤ 4*m j+1 := by
  have hh := chargedFilterMap_cost (fun u : Fin (m j) => (adjacentAt j u,2))
    (List.finRange (m j)) 2 (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hh
  dsimp only [chargedClassAdjacencies]
  omega

def chargedAdjacentIndices (m : Fin q → ℕ) : List (AdjacentPair m) × ℕ :=
  let out := chargedFlatMap (chargedClassAdjacencies (m := m)) (List.ofFn (fun j : Fin q => j))
  (out.1,out.2+q+1)

theorem chargedAdjacentIndices_complete (e : AdjacentPair m) :
    e ∈ (chargedAdjacentIndices m).1 := by
  simp only [chargedAdjacentIndices, chargedFlatMap_value, List.mem_flatMap]
  refine ⟨e.val.1, by simp, ?_⟩
  simp only [chargedClassAdjacencies, chargedFilterMap_value, List.mem_filterMap]
  exact ⟨e.val.2.1,List.mem_finRange _,adjacentAt_complete e⟩

theorem chargedAdjacentIndices_length :
    (chargedAdjacentIndices m).1.length ≤ Fintype.card (Item m) := by
  simp only [chargedAdjacentIndices, chargedFlatMap_value, List.length_flatMap,
    List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ j : Fin q, m j := Finset.sum_le_sum (fun j _ => chargedClassAdjacencies_length (m := m) j)
    _ = _ := by simp [Item, Fintype.card_sigma]

theorem chargedAdjacentIndices_cost (n : ℕ) (hq : q ≤ n) (hm : ∀ j, m j ≤ n) :
    (chargedAdjacentIndices m).2 ≤ 8*(n+1)^2 := by
  have hh := chargedFlatMap_cost (chargedClassAdjacencies (m := m))
    (List.ofFn (fun j : Fin q => j)) (4*n+1) n
    (fun j _ => (chargedClassAdjacencies_cost (m := m) j).trans (by have h := hm j; omega))
    (fun j _ => (chargedClassAdjacencies_length (m := m) j).trans (hm j))
  simp only [List.length_ofFn] at hh
  have hmul := Nat.mul_le_mul_right (4*n+1+n+1) hq
  dsimp only [chargedAdjacentIndices]
  nlinarith

end MOR34
