# Bounded normal integration: precise remaining bridge

This is a mathematical implementation plan, not a Lean-checked runtime theorem. The acceptance file determines which source lemmas have compiled.

## A small pivot suffices

Let Q=q+1 and let B be a reachable selection of r independent augmented count rows, each (1,z), with 0<=z_j<=n. Then r<=Q, the matrix has Q columns, and all entries have magnitude at most N=max(1,n). A full-row-rank column minor A can be chosen from the original columns; this retains the same entry bound. Write the remaining columns as C after a column permutation.

The new theorem independent_rows_pivot_minor proves this existence over the rationals, if accepted by the recorded compiler run. Its proof extracts a spanning independent subfamily of columns, proves its size equals r using equality of row and column rank, and reindexes that family by Fin r. It does not implement or bound a search.

Pinned Mathlib tools actually inspected for this route:

- LinearIndependent.rank_matrix, Data/Matrix/Rank.lean.
- Matrix.rank_eq_finrank_span_cols, same file.
- exists_linearIndependent', LinearAlgebra/LinearIndependent/Lemmas.lean.
- Matrix.linearIndependent_cols_iff_isUnit and Matrix.isUnit_iff_isUnit_det, LinearAlgebra/Matrix/NonsingularInverse.lean.

A rational nonzero determinant of an integer submatrix is a nonzero integer determinant because RingHom.map_det commutes with the integer embedding. This transport is still to be packaged for the actual count matrix.

## Finite pivot search and the target exponent

An implementation can enumerate column subsets of size r and select the first nonzero determinant. There are at most 2^Q subsets. Direct permutation expansion of a determinant uses at most Q! products, each of at most Q entries. Thus even this elementary choice uses at most O(2^Q Q Q!) arithmetic operations. Constructing the Q-r Cramer normals adds polynomially many determinants. All this is 2^{O(Q log(Q+1))}, within the theorem's parameter dependence.

If selecting independent rows as well is needed for a general FormsDescribe interface, there are at most 4^Q row/column subset pairs when both matrix dimensions are at most Q. A proof that a maximal nonzero minor determines the full row span is still required; this should not be silently assumed. The already-proved reachable-row independence avoids this extra step, at the price of carrying the invariant into the oracle correctness proof.

Every product has magnitude at most N^Q and every determinant partial sum at most Q! N^Q. Therefore the integer sizes involved remain O(Q log(Q+1)+Q log(N+1)) bits. This statement is an elementary bound for a prospective determinant-expansion implementation, not a certified cost semantics for Lean's determinant definition. Ordinary schoolbook integer arithmetic suffices once the operation-count and bit-size invariants have been formalized.

The cost multiplies the existing 6^q cell factor without changing the target 2^{O(q log(q+1))} parameter exponent. It must not be applied to the final rank matrix with n+1 columns.

## Converting kernel vectors into affine equations

For a chosen block [A C], the verified construction gives normals v_k with pivot coordinates -cramer(A,C_k) and free coordinates det(A)e_k. These normals span ker[A C]. What FormsDescribe needs is the converse annihilator statement: a vector y lies in the row span if and only if y dot v_k=0 for every k.

Two routes are available:

1. Transport kernel spanning through the standard dot-product duality, then use finite-dimensional double annihilation.
2. Avoid duality infrastructure by an explicit reconstruction. Set lambda=(A^T)^(-1)y_pivot. Then A^T lambda=y_pivot. The normal equation gives
   det(A)y_free,k = y_pivot dot cramer(A,C_k)
                  = lambda dot (A cramer(A,C_k))
                  = det(A) lambda dot C_k.
   Cancel det(A), giving y_free=C^T lambda. Hence y=[A C]^T lambda belongs to the row span. The reverse implication is the already established row-normal annihilation.

The second calculation provides a concrete proof target and may reduce reindexing overhead. It is recorded as a plan, not as an additional formalized theorem.

After transporting columns back to Option(Fin q), let the none coordinate be the IntegerForm constant and the some j coordinates be its coefficients. Evaluating at (1,z) then gives exactly the affine form. Check the sign convention against IntegerForm.eval, retain the coefficient bound under permutation, and replace the actual forms chooser. Only then can the bit bound be attributed to the pipeline itself.

## Boundary cases

Empty B has r=0 and is described by all standard coordinate normals on augmented space; its intersection with vectors (1,z) is empty, as required. A full Q-row independent selection has no free columns and spans the entire augmented space, so the normal list is empty. The existing given-pivot results include both cases.

## Useful API for the explicit converse

Matrix.dotProduct_mulVec in Data/Matrix/Mul.lean states the exact scalar associativity identity needed to replace y_pivot dot cramer(A,C_k) by lambda dot (A cramer(A,C_k)). Matrix.vecMul_surjective_iff_isUnit in NonsingularInverse.lean can supply lambda directly from invertibility, without introducing inverse coordinates into the theorem statement. If an explicit lambda is preferred, Matrix.mul_nonsing_inv and its cancellation lemmas support the formula y_pivot vecMul A^(-1). This affects the proof of correctness only; the normal vectors themselves already have explicit integer Cramer coordinates.

For column reindexing, the pinned Mathlib provides Equiv.Set.sumCompl (Logic/Equiv/Set.lean) and Fintype.card_compl_set (Data/Fintype/Card.lean). Apply these to the image of the column embedding, identify its image with Fin r and its complement with Fin(Q-r), and compose the sum equivalence. This preserves the original columns without introducing linear combinations. The cardinality and coordinate-transport proofs remain to be implemented.
