# User-approved scope: new proofs only

Authority: user instruction, 2026-10-18 16:15 Asia/Shanghai: formalize the newly contributed proofs; do not re-formalize results already established by others.

This supersedes earlier plans that treated implementing all primitive algorithms or verifying the Lean compiler's execution cost as necessary for this project. Existing checked modules are retained. No weaker substitute is introduced for a newly claimed mathematical conclusion.

## Required new material

1. Exchange-forcing pairing and interval/component consequences (manuscript Lemmas 2–4).
2. Affine parity-cell decomposition, its coverage and degeneracies (Lemma 5).
3. Lifting quotient spanning points and exchange directions to the full augmented span; deriving face dimension, facet decision and a tight-point affine basis (Theorem 8 correctness).
4. The additional facet-component bound C <= (3q+1)2^q (Corollary 6). Previously optional in the implementation roadmap, but it is an additional claimed proof and must be accounted for if the full new mathematical content is called complete.
5. Applications of external tools: validity of our integer encodings, parameter/dimension bounds, polynomial encoding length, and the mathematical combination of call counts with standard algorithm costs.
6. For the compression consequence, preserve feasible/tight binary points, validity, the actual output basis and original parameter K; derive the stated compressed size from the external coefficient bound. Do not replace these application checks by assuming the final conclusion.

## External results, with explicit boundaries

- Fixed-dimensional integer linear feasibility with witnesses and cost r^{O(r)} poly(B): Lenstra--Kannan framework, as stated in Bredereck et al., arXiv:1709.02850v2, Theorem 1. No implementation or internal proof of that framework is required. The application must still prove dimension and encoding bounds.
- Exact rational rank/affine-basis computation and elementary polynomial-time arithmetic/sorting: use standard external algorithmic results as explicitly stated contracts. Their output specifications must match the matrices used here. Do not count a contract as a verified implementation.
- Frank--Tardos compression: use its bounded-sign preservation, coefficient bound and strongly polynomial preprocessing cost as an external result. No new project axiom is introduced. Theorems quantify over compressed data satisfying the external conclusion.
- Ordinary Mathlib linear algebra, finite-set and order results are imported normally.

## What is outside the requested scope

Compiler correctness, a Lean-backend operational cost theorem, actual implementations of ILP/rank/Frank--Tardos, machine-level serialization and library-internal sorting costs are not prerequisites for checking the new manuscript proofs. A fully executable, solver-independent certified program is a larger separate deliverable.

## Claims that must remain separate

`new_core_proofs_complete`, `new_applications_complete`, `algorithm_level_FPT_derivation_complete`, `full_self_contained_formalization_complete`, and `compiled_runtime_model_verified` are distinct flags. Removing out-of-scope implementation obligations does not prove the mathematical FPT composition. Conditional cost substitution is not evidence that its runtime premise has been discharged.

A formal theorem about an explicit reference-algorithm budget can be sufficient for the manuscript-level derivation only once that budget has been justified phase by phase. An arbitrary function named cost with the desired upper bound assumed is not a proof of Theorem 8's time claim.
