import MOR34.Components
import MOR34.PartitionKernel
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace MOR34

section GraphSpan
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def edgeDifferenceSpan (R : α → α → Prop) : Submodule ℝ (α → ℝ) :=
  Submodule.span ℝ {v | ∃ i j : α, R i j ∧ v = unitVector i - unitVector j}

theorem path_difference_mem (R : α → α → Prop) {i j : α}
    (h : Relation.ReflTransGen R i j) :
    unitVector i - unitVector j ∈ edgeDifferenceSpan R := by
  induction h with
  | refl => simp only [sub_self]; exact Submodule.zero_mem _
  | @tail b c hab hbc ih =>
    have he : unitVector b - unitVector c ∈ edgeDifferenceSpan R :=
      Submodule.subset_span ⟨b, c, hbc, rfl⟩
    have hs := Submodule.add_mem (edgeDifferenceSpan R) ih he
    have hid : unitVector i - unitVector c =
        (unitVector i - unitVector b) + (unitVector b - unitVector c) := by abel
    rw [hid]
    exact hs

theorem edgeDifferenceSpan_eq_ker (R : α → α → Prop) (f : α → β)
    (hf : Function.Surjective f)
    (hconn : ∀ i j, f i = f j ↔ Relation.ReflTransGen R i j) :
    edgeDifferenceSpan R = LinearMap.ker (fiberSumMap f) := by
  rw [← fiberDifferenceSpan_eq_ker f hf]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i, j, hij, rfl⟩
    exact Submodule.subset_span ⟨i, j, (hconn i j).mpr (.single hij), rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i, j, hij, rfl⟩
    exact path_difference_mem R ((hconn i j).mp hij)
end GraphSpan

variable {q : ℕ} {m : Fin q → ℕ}

/-- The exchange graph on all items; edges are confined to one coefficient class. -/
def GlobalExchangeAdj (P : Model m) (i k : Item m) : Prop :=
  ∃ (j : Fin q) (u v : Fin (m j)),
    i = ⟨j, u⟩ ∧ k = ⟨j, v⟩ ∧ ExchangeAdj P j u v

theorem globalExchangeAdj_symm (P : Model m) : Symmetric (GlobalExchangeAdj P) := by
  rintro i k ⟨j, u, v, rfl, rfl, h⟩
  exact ⟨j, v, u, rfl, rfl, h.symm⟩

def exchangeSetoid (P : Model m) : Setoid (Item m) where
  r := Relation.ReflTransGen (GlobalExchangeAdj P)
  iseqv := ⟨fun _ => .refl,
    fun h => Relation.ReflTransGen.symmetric (globalExchangeAdj_symm P) h,
    fun h h' => h.trans h'⟩

abbrev ExchangeComponent (P : Model m) := Quotient (exchangeSetoid P)

noncomputable instance componentDecidableEq (P : Model m) : DecidableEq (ExchangeComponent P) :=
  Classical.decEq _

noncomputable instance componentFintype (P : Model m) : Fintype (ExchangeComponent P) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (exchangeSetoid P)) Quotient.mk_surjective

def componentLabel (P : Model m) : Item m → ExchangeComponent P := Quotient.mk (exchangeSetoid P)

noncomputable def componentCountMap (P : Model m) :
    (Item m → ℝ) →ₗ[ℝ] (ExchangeComponent P → ℝ) := by
  classical
  exact fiberSumMap (componentLabel P)

/-- The span E in paper Lemma 3, using the original oriented exchange edges. -/
def exchangeDirectionSpan (P : Model m) : Submodule ℝ (Item m → ℝ) :=
  Submodule.span ℝ {x | ∃ (j : Fin q) (u v : Fin (m j)), Exchange P j u v ∧
    x = unitVector (⟨j, u⟩ : Item m) - unitVector (⟨j, v⟩ : Item m)}

theorem exchangeDirectionSpan_eq_global (P : Model m) :
    exchangeDirectionSpan P = edgeDifferenceSpan (GlobalExchangeAdj P) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, u, v, h, rfl⟩
    exact Submodule.subset_span ⟨⟨j, u⟩, ⟨j, v⟩, ⟨j, u, v, rfl, rfl, Or.inl h⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, k, ⟨j, u, v, rfl, rfl, h⟩, rfl⟩
    rcases h with h | h
    · exact Submodule.subset_span ⟨j, u, v, h, rfl⟩
    · have he : unitVector (⟨j, v⟩ : Item m) - unitVector (⟨j, u⟩ : Item m) ∈
          exchangeDirectionSpan P := Submodule.subset_span ⟨j, v, u, h, rfl⟩
      have hn := Submodule.neg_mem (exchangeDirectionSpan P) he
      simpa only [neg_sub] using hn

/-- The actual exchange-component map, not an assumed abstract partition, has kernel E. -/
theorem exchangeDirectionSpan_eq_ker (P : Model m) :
    exchangeDirectionSpan P = LinearMap.ker (componentCountMap P) := by
  classical
  rw [exchangeDirectionSpan_eq_global]
  apply edgeDifferenceSpan_eq_ker (GlobalExchangeAdj P) (componentLabel P)
  · exact Quotient.mk_surjective
  · intro i k
    constructor
    · intro h
      exact Quotient.exact h
    · intro h
      exact @Quotient.sound (Item m) (exchangeSetoid P) i k h

theorem global_connected_class_iff (P : Model m) (j : Fin q) (a b : Fin (m j)) :
    Relation.ReflTransGen (GlobalExchangeAdj P) (⟨j, a⟩ : Item m) ⟨j, b⟩ ↔
      ExchangeConnected P j a b := by
  classical
  constructor
  · intro h
    let project : Item m → Fin (m j) := fun i => if he : i.1 = j then he ▸ i.2 else a
    have step : ∀ i k, GlobalExchangeAdj P i k →
        Relation.ReflTransGen (ExchangeAdj P j) (project i) (project k) := by
      rintro i k ⟨c, u, v, rfl, rfl, he⟩
      by_cases hc : c = j
      · subst c
        simpa [project] using Relation.ReflTransGen.single he
      · simp only [project, dif_neg hc]
        exact .refl
    have hp := h.lift' project step
    simpa [project] using hp
  · intro h
    exact h.lift (fun u => (⟨j, u⟩ : Item m)) (fun u v he => ⟨j, u, v, rfl, rfl, he⟩)

theorem componentLabel_eq_iff_class_connected (P : Model m) (j : Fin q) (a b : Fin (m j)) :
    componentLabel P (⟨j, a⟩ : Item m) = componentLabel P (⟨j, b⟩ : Item m) ↔
      ExchangeConnected P j a b := by
  constructor
  · intro h
    exact (global_connected_class_iff P j a b).mp (Quotient.exact h)
  · intro h
    apply @Quotient.sound (Item m) (exchangeSetoid P)
    exact (global_connected_class_iff P j a b).mpr h

theorem componentLabel_interval (P : Model m) (hWF : WellFormed P) (j : Fin q)
    (a b t : Fin (m j))
    (h : componentLabel P (⟨j, a⟩ : Item m) = componentLabel P (⟨j, b⟩ : Item m))
    (hat : a ≤ t) (htb : t ≤ b) :
    componentLabel P (⟨j, a⟩ : Item m) = componentLabel P (⟨j, t⟩ : Item m) := by
  apply (componentLabel_eq_iff_class_connected P j a t).mpr
  exact component_interval P hWF j ((componentLabel_eq_iff_class_connected P j a b).mp h) hat htb

theorem componentCountMap_surjective (P : Model m) :
    Function.Surjective (componentCountMap P) := by
  classical
  exact fiberSumMap_surjective (componentLabel P) Quotient.mk_surjective

/-- The exchange-direction dimension is n minus the actual number of components. -/
theorem exchangeDirectionSpan_finrank (P : Model m) :
    Module.finrank ℝ (exchangeDirectionSpan P) + Fintype.card (ExchangeComponent P) =
      Fintype.card (Item m) := by
  have h := (componentCountMap P).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (componentCountMap_surjective P),
    finrank_top, ← exchangeDirectionSpan_eq_ker] at h
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.add_comm] using h

end MOR34
