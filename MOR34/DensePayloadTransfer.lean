import MOR34.DenseRawPipeline

namespace MOR34

def DenseIntegerRow.payload {q : ℕ} (row : DenseIntegerRow q) : ℕ :=
  (row.counts.map signedIntegerBits).sum+(row.costs.map signedIntegerBits).sum+
    signedIntegerBits row.bound

theorem storedList_ofFn (L : List ℤ) (q : ℕ) (h : L.length=q) :
    List.ofFn (fun i : Fin q => L[i.val]?.getD 0) = L := by
  subst q
  calc
    _ = List.ofFn (fun i : Fin L.length => L[i.val]) := by congr 1; funext i; simp
    _ = L := List.ofFn_getElem L

/-- Equality of the rational inequalities uniquely identifies the actual stored
integer coefficients. Thus an existential encoding bound cannot hide a larger
integer array at the solver interface. -/
theorem densePayload_of_value {q : ℕ} (row : DenseIntegerRow q) (hs : row.WellSized)
    (a b : Fin q → ℤ) (d : ℤ) (he : row.value = integerRow a b d) :
    row.payload = integerRowBits a b d := by
  have ha : (fun j : Fin q => row.counts[j.val]?.getD 0) = a := by
    funext j
    have h := congrFun (congrArg CountInequality.counts he) j
    change ((row.counts[j.val]?.getD 0 : ℤ) : ℚ) = (a j : ℚ) at h
    exact_mod_cast h
  have hb : (fun j : Fin q => row.costs[j.val]?.getD 0) = b := by
    funext j
    have h := congrFun (congrArg CountInequality.costs he) j
    change ((row.costs[j.val]?.getD 0 : ℤ) : ℚ) = (b j : ℚ) at h
    exact_mod_cast h
  have hd : row.bound = d := by
    have h := congrArg CountInequality.bound he
    change (row.bound : ℚ) = (d : ℚ) at h
    exact_mod_cast h
  have hca : row.counts = List.ofFn a := by
    rw [← storedList_ofFn row.counts q hs.1,ha]
  have hcb : row.costs = List.ofFn b := by
    rw [← storedList_ofFn row.costs q hs.2,hb]
  simp only [DenseIntegerRow.payload,hca,hcb,hd,List.map_ofFn,Function.comp_def,
    List.sum_ofFn,integerRowBits]

/-- Completeness plus the exact cardinality excludes duplicated row indices. -/
theorem completeEnumeration_sum {α : Type*} [Fintype α] [DecidableEq α]
    (L : List α) (hc : ∀ a, a ∈ L) (hl : L.length = Fintype.card α) (f : α → ℕ) :
    (L.map f).sum = ∑ a, f a := by
  have ht : L.toFinset = Finset.univ := by ext a; simp [hc a]
  have hn : L.Nodup := by
    apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (L : Multiset α))).mp
    change L.toFinset.card = L.length
    rw [ht,hl,Finset.card_univ]
  have hh := List.sum_toFinset f hn
  simpa only [ht] using hh.symm

theorem denseCompiledList_payload {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (indices : List ι) (hc : ∀ i, i ∈ indices) (hl : indices.length = Fintype.card ι)
    (compile : ι → DenseIntegerRow q) (hs : ∀ i, (compile i).WellSized)
    (a b : ι → Fin q → ℤ) (d : ι → ℤ)
    (he : ∀ i, (compile i).value = integerRow (a i) (b i) (d i)) :
    ((indices.map compile).map DenseIntegerRow.payload).sum = ∑ i, integerRowBits (a i) (b i) (d i) := by
  simp only [List.map_map,Function.comp_def]
  have hfun : (fun i => (compile i).payload) = (fun i => integerRowBits (a i) (b i) (d i)) :=
    funext (fun i => densePayload_of_value _ (hs i) _ _ _ (he i))
  rw [hfun]
  exact completeEnumeration_sum indices hc hl _

variable {q : ℕ} {m : Fin q → ℕ}

theorem compiledForcedRequest_payload (P : Model m) (j : Fin q) (u v : Fin (m j)) (R : ℕ)
    (a b : ForcedRow m j u v → Fin q → ℤ) (d : ForcedRow m j u v → ℤ)
    (he : ∀ k, forcedRow P j u v k = integerRow (a k) (b k) (d k)) :
    (((compiledForcedRequest P j u v R).1).map DenseIntegerRow.payload).sum =
      ∑ k, integerRowBits (a k) (b k) (d k) := by
  simp only [compiledForcedRequest,retainedForcedSystem,chargedMap_value]
  apply denseCompiledList_payload _ (forcedRowIndexList_complete j u v)
    (by rw [forcedRowIndexList_length,forcedRow_card])
  · intro k; exact evaluateConstructedRow_sized _
  · intro k
    rw [compileRetainedRow_value,retainedForcedRow_interpret P j u v _ _ R rfl rfl]
    exact he k

theorem compiledCountRequest_payload (P : Model m) (ε : Parity q) (L : List (IntegerQuery q)) (R : ℕ)
    (a b : CountRow m L.length → Fin q → ℤ) (d : CountRow m L.length → ℤ)
    (he : ∀ k, (countRow P (queryCoefficients L) (queryBounds L) k).withParity ε =
      integerRow (a k) (b k) (d k)) :
    (((compiledCountRequest P ε L R).1).map DenseIntegerRow.payload).sum =
      ∑ k, integerRowBits (a k) (b k) (d k) := by
  simp only [compiledCountRequest,chargedMap_value]
  apply denseCompiledList_payload _ (fun k => countRowIndexList_complete k)
    (by rw [countRowIndexList_length,countRow_card])
  · intro k; exact compileParityRow_sized _ _
  · intro k
    rw [compileParityRow_value,builtCountRow_interpret]
    exact he k

theorem compiledViolationRequest_payload (P : Model m) (R : ℕ)
    (a b : ViolationRow m → Fin q → ℤ) (d : ViolationRow m → ℤ)
    (he : ∀ k, violationRow P k = integerRow (a k) (b k) (d k)) :
    (((compiledViolationRequest P R).1).map DenseIntegerRow.payload).sum =
      ∑ k, integerRowBits (a k) (b k) (d k) := by
  simp only [compiledViolationRequest,chargedMap_value]
  apply denseCompiledList_payload _ (fun k => violationRowIndexList_complete k)
    (by rw [violationRowIndexList_length,violationRow_card])
  · intro k; exact evaluateConstructedRow_sized _
  · intro k
    rw [compileRetainedRow_value,builtViolationRow_interpret]
    exact he k

/-- The actual array passed to the solver inherits the previously proved
fourth-degree bit bound; no choice of a smaller equivalent encoding is used. -/
theorem compiledForcedRequest_payload_polynomial (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ))
    (j : Fin q) (u v : Fin (m j)) (R : ℕ) :
    (((compiledForcedRequest P j u v R).1).map DenseIntegerRow.payload).sum ≤
      168*(Fintype.card (Item m)+L+2)^4 := by
  obtain ⟨a,b,d,he,hbits⟩ := forcedSystem_polynomial_payload P hWF M L hM hML hw hc hb hd j u v
  rw [compiledForcedRequest_payload P j u v R a b d he]
  exact hbits

theorem compiledViolationRequest_payload_polynomial (P : Model m) (hWF : WellFormed P)
    (M L : ℕ) (hM : 1 ≤ M) (hML : M ≤ 2^L)
    (hw : ∀ i, |P.weight i| ≤ (M : ℤ)) (hc : ∀ j, |P.coefficient j| ≤ (M : ℤ))
    (hb : |P.capacity| ≤ (M : ℤ)) (hd : |P.rhs| ≤ (M : ℤ)) (R : ℕ) :
    (((compiledViolationRequest P R).1).map DenseIntegerRow.payload).sum ≤
      168*(Fintype.card (Item m)+L+2)^4 := by
  obtain ⟨a,b,d,he,hbits⟩ := violationSystem_polynomial_payload P hWF M L hM hML hw hc hb hd
  rw [compiledViolationRequest_payload P R a b d he]
  exact hbits

end MOR34
