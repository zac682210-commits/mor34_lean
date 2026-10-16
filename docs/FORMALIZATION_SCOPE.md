# MOR34 formalization scope

The paper is *Fixed-Parameter Recognition of Knapsack Facets via Parity and Feasible Exchanges*, Zhiyan Lin, version 0.1, October 13, 2026.

The repository separates proposition specifications from proved theorems. A successful `lake build` of `Targets.lean` only checks that the target propositions are well formed; it does not prove them.

## First combinatorial obligation

`MOR34.balancedSplit` has the exact previously frozen type `MOR34.BalancedSplitGoal`. For a finite set D of size 2k and disjoint prescribed pairs P,N contained in D, with k >= 2, it produces disjoint U,V of size k whose union is D, with P contained in U and N contained in V.

Construction: extend P to a k-element subset U of D minus N, then take V = D minus U. The available set has 2k-2 elements, at least k. This uses Mathlib's existing `Finset.exists_subsuperset_card_eq`, not a new combinatorial discovery.

In paper Lemma 4, P and N each contain one chosen item on each side of an interior cut. Applying the split makes both outputs select a right-side item and omit a left-side item. The formal identification of those four positions and the independent splitting of all other coefficient classes remain to be proved.

## Acceptance

The build must succeed on the exact commit. `Check.lean` prints the transitive axioms of each claimed theorem; `scripts/audit_axioms.py` allows only `propext`, `Classical.choice`, and `Quot.sound`, and rejects missing output and `sorryAx`.

This does not yet formalize Lemma 4, the tight-face spanning theorem, the integer-programming oracle, or the FPT complexity theorem. A proof of an auxiliary finite-set lemma is not a formal solution of the entire problem.
