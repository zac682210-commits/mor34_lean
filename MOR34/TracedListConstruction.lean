import MOR34.NormalSearchCost

namespace MOR34

/-- Reference list construction. Each emitted list cell is charged once; the
callback supplies its own cost, so no evaluation is hidden in a free map. -/
def chargedMap {α β : Type*} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([],0)
  | a::L => let x := f a; let y := chargedMap f L
      (x.1::y.1, x.2+y.2+1)

theorem chargedMap_value {α β : Type*} (f : α → β × ℕ) (L : List α) :
    (chargedMap f L).1 = L.map (fun a => (f a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [chargedMap, ih]

theorem chargedMap_cost {α β : Type*} (f : α → β × ℕ) (L : List α)
    (C : ℕ) (hf : ∀ a ∈ L, (f a).2 ≤ C) :
    (chargedMap f L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [chargedMap]
  | cons a L ih =>
      have ha := hf a (by simp)
      have hL := ih (fun b hb => hf b (by simp [hb]))
      simp only [chargedMap, List.length_cons]
      nlinarith

/-- Append copies the left block, hence its full length is charged. -/
def chargedFlatMap {α β : Type*} (f : α → List β × ℕ) : List α → List β × ℕ
  | [] => ([],0)
  | a::L => let x := f a; let y := chargedFlatMap f L
      (x.1++y.1, x.2+y.2+x.1.length+1)

theorem chargedFlatMap_value {α β : Type*} (f : α → List β × ℕ) (L : List α) :
    (chargedFlatMap f L).1 = L.flatMap (fun a => (f a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [chargedFlatMap, ih]

theorem chargedFlatMap_cost {α β : Type*} (f : α → List β × ℕ) (L : List α)
    (C M : ℕ) (hf : ∀ a ∈ L, (f a).2 ≤ C)
    (hlen : ∀ a ∈ L, (f a).1.length ≤ M) :
    (chargedFlatMap f L).2 ≤ L.length*(C+M+1) := by
  induction L with
  | nil => simp [chargedFlatMap]
  | cons a L ih =>
      have ha := hf a (by simp)
      have hm := hlen a (by simp)
      have hL := ih (fun b hb => hf b (by simp [hb])) (fun b hb => hlen b (by simp [hb]))
      simp only [chargedFlatMap, List.length_cons]
      nlinarith

/-- Both accepted and rejected entries are visited. A predicate evaluation and
a possible output cell are charged, with data-dependent predicate cost explicit. -/
def chargedFilter {α : Type*} (p : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([],0)
  | a::L => let x := p a; let y := chargedFilter p L
      (if x.1 then a::y.1 else y.1, x.2+y.2+1)

theorem chargedFilter_value {α : Type*} (p : α → Bool × ℕ) (L : List α) :
    (chargedFilter p L).1 = L.filter (fun a => (p a).1) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [chargedFilter, List.filter_cons, ih]; split <;> rfl

theorem chargedFilter_cost {α : Type*} (p : α → Bool × ℕ) (L : List α)
    (C : ℕ) (hp : ∀ a ∈ L, (p a).2 ≤ C) :
    (chargedFilter p L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [chargedFilter]
  | cons a L ih =>
      have ha := hp a (by simp)
      have hL := ih (fun b hb => hp b (by simp [hb]))
      simp only [chargedFilter, List.length_cons]
      nlinarith

end MOR34
