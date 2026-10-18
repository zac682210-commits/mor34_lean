# Same-session review: newly contributed proofs and external applications

This is a mathematical source review, not independent peer review. Compiler and
axiom evidence belongs in newproofs_verified_metadata.json once the exact source
head passes. The frozen Model, Targets and PaperInterface files are unchanged.

## Corollary 6: actual exchange-component bound

The proof uses actual global ExchangeComponent labels, not an arbitrary partition.
For a nonempty parity class, the variable positions in class j range from low_j
to high_j-1. Divide them into its first position, last position and strict interior.
The lower and upper witnesses for j are in the same full coordinatewise parity
class. The previously proved interior exchange theorem puts every two strict
interior positions in the same global component. Endpoints contribute at most
one label each. Thus at most three component labels vary per coefficient class.
A finite-bucket injection proves the cardinality statement, including empty
interiors and coinciding endpoints; these cases are not excluded by assumption.

The vector at the coordinatewise lower endpoint is an anchor. Importantly, the
coordinatewise lower endpoint need not itself be a tight count vector. Nothing
in the new proof assumes it is tight: a containing linear span may use this
anchor. Every actual quotient prefix differs from it by unit directions in the
at-most-3q varying components. Augmentation therefore requires at most 3q+1
generators per nonempty parity class, and at most (3q+1)2^q overall.

The original quotient dimension identity, dim(exchange span)+C=n, and the facet
dimension condition give C=dim(augmented quotient tight span). This yields the
bound for the actual components. A further wrapper substitutes q<=K+1 for the
original raw input, including its possible zero-coefficient class.

## Frank--Tardos application

CompressionSigns uses signed coordinate tests and two-coordinate differences.
The binary test has entries (x,-1), norm <=n+1, and dot product sum_S a-b.
Thus equality and inequality of every original binary test are preserved. Unit
tests preserve positivity/nonnegativity/zeros; differences preserve equality and
ordering of coefficients. Equality of fibers, not injectivity of a coefficient
map, proves preservation of the number K of distinct positive values.

CompressionTransport proves validity and tight-point preservation even before
assuming candidate validity. Equality of geometric faces additionally assumes
validity and uses the convex hull of tight vertices. It never asserts that an
arbitrary intersecting hyperplane is unchanged. The output transport includes
invalid witnesses, empty faces, dimensions, facet flags, independence, span and
cardinality of the same returned tight-point basis.

With r=n+1, the external radius is 2^(4r^3)(r+1)^(r(r+2)). Since r+1<=2^r,
it is <=2^(7r^3). Each signed coefficient takes at most 7r^3+2 payload bits;
the two r-entry vectors together take at most 18r^4 bits. This is dense signed
integer payload, not a claim about an arbitrary serialization format.
external_compression_application accepts only the external compressor's sign
and coefficient-bound conclusions. It constructs a normalized compressed
instance, transfers its verified solver-relative output to the original input,
and proves the payload and original-parameter bounds.

## Polynomial encoding and counted costs

PolynomialPayload uses M<=2^L, q<=n and N=n+1. It bounds uniformRowBits by
14(n+L+2)^2 and the three row-family budgets by 168(n+L+2)^4. The cell statement
is carried through SearchStates, so it applies to queries generated along the
actual computed-normal recursive search, including unsuccessful queries.
The four is an explicit degree independent of q, not an optimized exponent.
The forced and violation statements are instantiated with their actual integer
row witnesses; these are not just arithmetic bounds on placeholder row counts.

OracleCostComposition absorbs the earlier support/extrema/cell call expression
into rowCallFactor(q)(n+1), with rowCallFactor(q)=1+6*2^q+2(q+1)^2*6^q.
Substituting a supplied per-call solver bound gives the corresponding total
counted ILP cost. The theorem deliberately excludes edge discovery, input
construction and rank. The global normal-candidate charge sums the actual
per-cell recurrences over the at-most-6^q cells. ParameterFactors bounds this
normal-search factor by (q+2)^(5q+4), and rowCallFactor by (q+2)^(3q+5).
The original-parameter wrapper gives (K+3)^(5K+9) for normal candidate tests.
These explicit inequalities have the required q^{O(q)} shape without assuming
a joint total-runtime conclusion.

ComputedRankPayload connects the rank-call count to orderedBinarySets of the
actual computedReturnedSets. A binary augmented matrix entry has at most two
signed payload bits. Every state of the n+1-step extraction uses at most n+1
retained rows; even after inserting an arbitrary rejected candidate, the two
rank inputs have at most 2(n+2)^2 bits. Exact rank remains an external primitive.
The call bound is also factored as 2((q+1)6^q+2)(n+1)^2. Substituting a
per-call bound R[2(n+2)^2]^c yields parameter factor
2((q+1)6^q+2)R2^c times (n+2)^(2c+2). The fixed polynomial degree is
explicit; the theorem still charges only the rank phase.

## Remaining mathematical boundary

The whole-program mathematical FPT cost theorem is not obtained merely by
assuming a cost bound and performing compression substitution. The counted
phases above must still be assembled with edge-witness construction, finite
representation work and standard primitive costs in one reference-algorithm
budget. Under the user's new scope this is a mathematical algorithm analysis,
not an obligation to verify Lean backend caching or to implement ILP/rank/FT.
The illustrative six-item example is not a separate kernel-checked facet
certificate in this checkpoint. It is not needed by the general theorem proofs.
