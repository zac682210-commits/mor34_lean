# Compiler notes for the October 17 basis checkpoint

These notes describe proof-engineering failures and repairs, not changes to mathematical hypotheses. Successful evidence is the exact source/run recorded in ACCEPTANCE.json. Failed runs in the ledger are not accepted proofs.

- Integer matrix casts: the determinant of the rational image must be related to the integer determinant with `(Int.castRingHom ℚ).map_det`. Merely presenting a casted nonzero hypothesis can leave a different elaborated matrix expression. Give an explicit intermediate equality before `exact_mod_cast`.
- Mixed sum-index matrices: annotate the block matrix as `Matrix (Fin r) (Fin r ⊕ Fin f) ℚ` and the inner `Sum.elim` value as an integer before casting. This prevents elaboration from selecting inconsistent scalar types.
- Magnitude versus integer absolute value: the Cramer bound is over integers, whereas the bit bound uses natural `natAbs`. Introduce the inequality between the integer casts of natural magnitudes, rewrite with `Int.natCast_natAbs`, then use `exact_mod_cast`. A direct cast tactic on the original absolute-value inequality did not close the goal.
- Partition counts: rewrite the filter for `¬ 0 < coefficient` into the zero-coefficient filter before invoking generic simplification. Generic simp otherwise turns the negated inequality into `coefficient <= 0`, defeating the intended syntactic rewrite. Nonnegativity of coefficients is explicitly supplied by WellFormed.
- The complete build log is now printed when a readiness command fails. This reveals errors in independent early modules rather than only a truncated tail. The actual eight commands and their fail-closed exit behavior remain unchanged.

Do not bypass the local compiler startup restriction. The successful GitHub Actions logs and downloaded artifact are the compiler evidence for this round; local static source scans alone are not proof evidence.
