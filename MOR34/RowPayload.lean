import MOR34.UniformEncoding
import MOR34.QueryAccounting

namespace MOR34
variable {q : ℕ}

theorem integerRowBits_uniform (a b : Fin q → ℤ) (d : ℤ) (B : ℕ)
    (ha : ∀ j, signedIntegerBits (a j) ≤ B) (hb : ∀ j, signedIntegerBits (b j) ≤ B)
    (hd : signedIntegerBits d ≤ B) : integerRowBits a b d ≤ (2*q+1)*B := by
  have h1 : (∑ j, signedIntegerBits (a j)) ≤ q*B := by
    calc
      _ ≤ ∑ _j : Fin q, B := Finset.sum_le_sum (fun j _ => ha j)
      _ = _ := by simp
  have h2 : (∑ j, signedIntegerBits (b j)) ≤ q*B := by
    calc
      _ ≤ ∑ _j : Fin q, B := Finset.sum_le_sum (fun j _ => hb j)
      _ = _ := by simp
  unfold integerRowBits
  nlinarith

theorem uniform_row_payload (L : CountInequality q) (N M : ℕ) (hN : 1 ≤ N)
    (h : L.IntegerBounded (uniformRowRadius q N M) (uniformRowRadius q N M) (uniformRowRadius q N M)) :
    ∃ a b : Fin q → ℤ, ∃ d : ℤ, L = integerRow a b d ∧
      integerRowBits a b d ≤ (2*q+1)*uniformRowBits q N M := by
  obtain ⟨a, b, d, he, ha, hb, hd⟩ := h
  exact ⟨a, b, d, he, integerRowBits_uniform a b d _
    (fun j => uniformRow_signed_bits q N M hN _ (ha j))
    (fun j => uniformRow_signed_bits q N M hN _ (hb j))
    (uniformRow_signed_bits q N M hN d hd)⟩

/-- Dense integer coefficient payload only. A self-delimiting wire format and its
row/dimension headers are not modeled by this sum. -/
theorem uniform_system_payload {ι : Type*} [Fintype ι] (L : ι → CountInequality q)
    (N M : ℕ) (hN : 1 ≤ N)
    (h : ∀ i, (L i).IntegerBounded (uniformRowRadius q N M) (uniformRowRadius q N M) (uniformRowRadius q N M)) :
    ∃ a b : ι → Fin q → ℤ, ∃ d : ι → ℤ, (∀ i, L i = integerRow (a i) (b i) (d i)) ∧
      (∑ i, integerRowBits (a i) (b i) (d i)) ≤ Fintype.card ι * ((2*q+1)*uniformRowBits q N M) := by
  classical
  choose a b d he hb using fun i => uniform_row_payload (L i) N M hN (h i)
  refine ⟨a, b, d, he, ?_⟩
  calc
    _ ≤ ∑ _i : ι, (2*q+1)*uniformRowBits q N M := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

/-- The row index and all coefficients are those of an actual scalar cell query. -/
theorem cell_system_payload {m : Fin q → ℕ} (P : Model m)
    (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hq : q ≤ N) (hm : ∀ j, m j ≤ N)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (l h : Counts q) (mode : CellMode q) (hl : ∀ j, l j ≤ N) (hh : ∀ j, h j ≤ N)
    (B : Finset (Counts q)) (hB : ∀ z ∈ B, ∀ j, z j ≤ N)
    (t : IntegerQuery q) (ht : t ∈ outsideQueries (boundedCountForms B)) (ε : Parity q) :
    ∃ a b : CountRow m (t :: cellQueries l h mode).length → Fin q → ℤ,
      ∃ d : CountRow m (t :: cellQueries l h mode).length → ℤ,
      (∀ k, (countRow P (queryCoefficients (t :: cellQueries l h mode))
        (queryBounds (t :: cellQueries l h mode)) k).withParity ε = integerRow (a k) (b k) (d k)) ∧
      (∑ k, integerRowBits (a k) (b k) (d k)) ≤
        (Fintype.card (Item m)+5*q+4)*((2*q+1)*uniformRowBits q N M) := by
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hh' := uniform_system_payload
    (fun k : CountRow m (t :: cellQueries l h mode).length =>
      (countRow P (queryCoefficients (t :: cellQueries l h mode))
        (queryBounds (t :: cellQueries l h mode)) k).withParity ε) N M hN
    (fun k => cellRow_uniform_bound _ N M hN hM hq
      (cell_normal_parity_rows_bounded P N M hN hM' hm hw hc hb hd l h mode hl hh B hB t ht ε k))
  simpa only [cell_solver_row_count] using hh'

end MOR34
