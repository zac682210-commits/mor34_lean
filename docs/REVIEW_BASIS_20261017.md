# Review of returned bases, supporting faces and normalized output

This is a same-session statement review. Only the source commit and run recorded in ACCEPTANCE.json are accepted compiler evidence. New source drafts are not proof evidence until all gates pass.

## Original mathematical objects

Model.lean, Targets.lean and PaperInterface.lean remain unchanged. The grouped input still has positive sorted weights, feasible singletons, nonempty coefficient classes, and nonnegative distinct class coefficients. None of the new geometric statements assumes the desired dimension or the desired facet classification.

## Returned actual points

ReturnedPoints forms a finite union of selected binary prefixes and both members of every actual solver-returned adjacent exchange. All members satisfy the original Tight predicate. The cardinal bound is (q+1)6^q+2n; duplicate sets can only lower the count.

The original selected augmented-span theorem proves that this family spans all tight points. A direction row is replaced by the difference of its two augmented point rows, so the first coordinate cancels. The proof does not identify direction vectors themselves with binary points. Equality of affine spans follows from the already proved augmentation/affine-span bridge and works also for an empty tight set.

Classical independent-subset existence is recorded separately from the finite extraction procedure. FiniteBasisSearch scans the supplied list using rank growth to detect a new direction. BinaryPointBasis proves that exact rational ranks of augmented integer 0/1 matrices give the real augmented-span ranks used by that procedure. The searched basis consists of original tight binary sets, is affinely independent, and spans the original tight affine space. In the nonempty case its cardinality is exactly the affine dimension plus one. A facet therefore has exactly n basis points.

The exact rank evaluator remains a primitive with an explicit correctness contract. These results do not prove Gaussian elimination or its bit complexity. The call counter charges two rank evaluations per scanned candidate, without assuming caching. Its upper bound is 2(n+1)((q+1)6^q+2n). This is a rank-call bound, not a total runtime bound.

## Supporting face and geometric facet convention

SupportingHull proves for any real linear functional bounded above by b on a generating set S that the b-level in conv(S) is conv(S intersect {f=b}). The proof treats zero combination weights separately; for positive weights it proves that equality cannot hide slack. It does not assume the generators are vertices or use the desired hull identity as a hypothesis.

FacetBridge applies this to the original candidate functional. It proves convexity and extremeness of the equality face in the actual knapsack convex hull, and equality of its affine and vector spans with those of the tight binary generators. The facet convention is a nonempty convex extreme subset of affine codimension one. This is the standard codimension-one-face convention used in the paper. It is not a definition equating facetness to a matrix rank. The subsequent equivalence to computed rank n uses the separately proved full dimension of the knapsack polytope and rank/affine-dimension identity. Equivalence with an alternative definition using maximal proper faces has not been separately formalized.

Validity remains part of the candidate inequality's facet predicate. A zero candidate with zero right-hand side has the entire polytope as its face and is rejected. Empty equality levels are excluded explicitly. No unsigned natural dimension is assigned to the empty face. SignedDimension additionally exposes the paper convention explicitly: invalid candidates return no dimension, empty faces return -1, and supported faces return their nonnegative real affine dimension.

## Control flow and output

ExecutedCells uses the actual optional parity solver result. It hoists one parity nonemptiness check and its attained extrema outside the mode loop. Its finite union is proved equal to the structural selection for the same forms and same row solver. It does not invoke a decision procedure for the proposition that an arbitrary parity set is nonempty.

RecognitionCertificate handles invalid, valid-empty and supported branches. Invalidity returns an original feasible binary witness violating the proposed inequality. The supported branch reports the natural dimension and the facet Boolean using the computed integer matrix. NormalizedPipeline packages this decision and a searched binary affine basis in one record. The basis is empty in the invalid and empty branches; its size is dimension+1 in the supported branch.

The normal-form family and BuiltSelection are still classically chosen using an already proved existence theorem. This preserves the dependency on actual row-solver searches but does not make the whole pipeline executable. The complete output contract is relative to the three exact ILP interfaces and an exact rational-rank evaluator. No new project axiom is added. Complete algorithm execution and the paper's full FPT theorem remain open.

## Bounded normal construction

CramerBounds and BoundedPivotNormals start a replacement for the unrestricted classical normal choice. Given an r-by-r nonsingular integer pivot block A and free columns C, each normal has pivot coordinates -cramer(A,C_k), free coordinate det(A) at k, and zero at other free coordinates. These normals annihilate the pivot rows and are independent over Q. Their coefficients are bounded by r! N^r when the entries are bounded by N. The determinant/Cramer bounds are standard linear algebra and are not claimed as new mathematical research.

PivotNormalSpan addresses completeness for this given pivot block: kernel vectors are determined by their free coordinates, and the constructed normals span the entire rational kernel. This still does not select a bounded pivot block from an arbitrary count selection or transport the normals into FormsDescribe. The old classical normals have not acquired a size bound merely because a different bounded family has been constructed. PivotNormalBits separately bounds the magnitude-bit function ceil(log2(|z|+1)) by r(ceil(log2 r)+ceil(log2 N))+1 for this constructed family. A costed construction and a bound for the actual normal generator must retain that distinction.

## Remaining proof boundary

1. Extract an appropriate pivot row/column block for every bounded selected count matrix, transport the constructed normal family into the original IntegerForm/FormsDescribe interface, and replace classical normal choice.
2. Formalize original-input normalization. ParameterCount now proves q<=K+1 inside the normalized model, where K is the cardinality of the distinct positive values occurring on actual items. Constructing this model from the original input and proving preservation remain open.
3. Supply executable, verified exact-rank and fixed-dimensional ILP implementations or explicitly state them as imported algorithmic foundations, with an encoding and cost model.
4. Prove polynomial coefficient/bit lengths for every row transformation and the total FPT running time. Frank–Tardos compression remains a separate foundation.

The number of named lemmas is not a completion percentage. All evidence is from this session; no independent review or independent kernel replay is claimed.

## Boundary checks for the pivot construction

The determinant and kernel statements include r=0: the empty pivot determinant is one and the constructed free-coordinate normals are standard coordinate vectors. If there are no free columns, the family is empty and nonsingularity makes the kernel zero. A coefficient magnitude of exactly 2^e needs e+1 magnitude bits; the explicit bit estimate retains that extra one. Its definition uses zero magnitude bits for zero and treats a sign bit separately. These boundary conditions are part of the general Lean statements, not only finite numerical examples.

ParameterCount uses nonnegativity and injectivity of class coefficients plus nonempty classes. The bound is about actual distinct positive item values, rather than simply renaming q-1 as K. It does not formalize sorting/grouping or preservation under the resulting item permutation. The paper theorem already assumes positive weights and feasible singletons, so eliminating infeasible items is outside its stated scope.

## Dependency audit of the return theorem

- BuiltSelection is inhabited by row_solver_cell_selection, whose real cell-spanning theorem is derived from the recursive basis search and the explicit parity row solver. It does not assume the final tight-space conclusion in the input model.
- Each exchange point is obtained by Option.get from the actual forced solver answer. Its partner is the explicit sorted same-class swap. Their difference, rather than either point alone, represents the retained direction.
- The binary basis scan uses exact rational ranks of finite augmented 0/1 matrices. The rational-to-real rank identity is proved before these ranks are used to infer real affine independence.
- The reported rank minus one is used only in the supported branch. The original tight witness ensures nonemptiness and augmented rank at least one, so natural subtraction cannot silently truncate a negative dimension.
- DefinesFacet includes Valid. A rejected invalid inequality need not be argued to have no geometrically interesting equality slice; it fails the validity requirement for defining a supporting facet.
- The all-zero candidate case is covered semantically: its nonempty face has dimension n and basis size n+1, whereas a facet requires dimension n-1 and basis size n. No positive-right-hand-side assumption was added.
- Integer normal magnitude and bit bounds apply only to the new pivot family under entry bounds. They do not imply an operation bound, denominator bound for arbitrary bases, or a replacement theorem for the old forms chooser.

## Parameter-bounded pivot-search opportunity

The pending pivot selector need not use a general polynomial Gaussian-elimination implementation in the count subroutine. Its reachable selected matrices have at most q+1 rows and q+1 columns, so direct minor enumeration can preserve the 2^{O(q log(q+1))} target. This is a proposed implementation improvement supported by the existing size/independence invariants, not a newly checked total-cost theorem. It does not apply to final rank computations whose width grows with n.

## Direct paper-statement comparison

The source manuscript Section 2 assumes n>=1, positive integer weights, positive capacity, every singleton feasible, and a nonnegative integer candidate vector. The Lean model keeps those substantive assumptions (and can also cover empty index types in several lemmas). The unformalized conversion needed for the stated theorem is finite grouping by coefficient and within-class sorting, with transport by an item equivalence. A general fixed-variable or infeasible-item preprocessing theorem is optional and must not inflate the estimate for the paper's stated target.

The main theorem explicitly promises validity/facet recognition, signed empty-face dimension -1 and an affine basis of actual tight binary points. The new normalized output theorem checks these three mathematical outputs. The main theorem also promises a bit-operation bound; that portion is still separate and unproved. The optional arithmetic-operation corollary additionally uses Frank–Tardos compression.

## Original-column minor existence

PivotMinorExistence takes an independent rational row family and extracts a subset of the original columns whose square determinant is nonzero. It uses the standard equality of row and column rank and selection of an independent spanning column subfamily. No new matrix entries are introduced; retaining the original entry bound is therefore possible after integer transport. This is an existence lemma, not the finite first-success selector or its cost bound. Its compilation and axiom status must be read from the accepted checkpoint.
