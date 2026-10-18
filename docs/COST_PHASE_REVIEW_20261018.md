# Cost-phase review, 18 October 2026

This note records the proof boundary of the accepted cost checkpoint.
The accepted source and CI run are specified in ACCEPTANCE.json. Exact accepted source: 239faa04a024e92e159ce60a70ac26c1b9c900af; CI run: 39121830829.

## What was missing at the previous checkpoint

The 662-theorem checkpoint established mathematical correctness, the component
bound, compression semantics, integer sizes, and several oracle-call budgets.
It did not establish full running time. In particular, merely multiplying the
number of successful normals by an arithmetic cost would miss unsuccessful
candidate tests. Similarly, a functional definition of an exchange witness could
be evaluated several times; an implementation must retain its answers to use the
one-query-per-adjacent-pair budget.

## New connections being checked in this round

1. StoredEdgeWitnesses defines an explicit, ordered list of adjacent-pair solver
   answers. Its downstream point list uses those retained answers. The resulting
   finite set equals the previous two exchange-witness images, exactly. The complete
   normalized and original-input pipelines are also proved equal. The proof
   is stronger than equality of spans. The list has at most n solver entries and
   at most 2n output points. Enumeration and sorting of the index list are separate
   from the n external solver calls.
2. NormalArithmeticCost follows the branch decisions of tryNormalKey. Its charge
   includes rejected candidates, recursive determinant arithmetic, all computed
   Cramer entries, and annihilation comparisons. The search charge follows the
   actual early-stopping path and the actual basis recursion.
3. AggregateArithmeticCost sums these charges over nonempty parities and all cells.
   The derived normal arithmetic/comparison budget is (q+4)^(6q+13). The combined
   solver, rank, and normal-arithmetic polynomial exponent is independent of q.
   The ILP and rank unit costs remain explicit external primitive contracts.
4. NormalBitCost puts Laplace partial sums and annihilation partial sums in the
   signed-bit envelope

       (clog_2(q+2)+clog_2(n+1))(q+2)+3 <= 3(n+2)^2.

   This is an intermediate-value bound, not just a bound on accepted answers.
   The counted normal bit-cost statement explicitly receives a uniform integer
   operation cost at that envelope. It is not a verification of machine code.
5. IntegerConstructionTrace, CountConstructionCost, ForcedConstructionCost, and
   ViolationConstructionCost give integer expression constructors. Their semantic
   values equal the original rational row definitions. The arithmetic/read node
   counts of all three query families have a coarse quadratic upper bound
   144(n+L+2)^2. Prefix sums are explicitly traversed, even when recomputed.
   For forced rows, residual weights are input reads through the sorted deleted-
   pair table; making that table and indexing it are not charged by the AST.
6. ReturnedFamilyCost counts the actual number of coordinates in the binary point
   encoding and bounds the work of a prescribed all-pairs comparison schedule.
   It does not assert that the Lean backend executes its sorting routine with
   exactly this schedule or cost.

## What is deliberately NOT concluded

These statements do not yet prove a full reference-program bit-cost theorem.
A faithful final assembly must still identify and charge:

- preprocessing/grouping, construction of the deleted-pair index tables, and
  finite-key enumeration (including keys constructed but never tested);
- row dispatch, AST creation/storage, copying, index lookup, and query emission;
- materialization and ordering of the selected count and binary-point families;
- compression preprocessing plus substitution into that completed total cost.

Standard sorting, arithmetic, fixed-dimensional ILP, exact rational rank, and
Frank--Tardos theorems can be imported as explicitly scoped primitive contracts.
There is no reason, under the user's current scope, to re-prove those algorithms
or the Lean compiler backend. But a hypothesis asserting the final FPT bound, or
asserting an unproved total phase cost, is not a replacement for the new proof.

## Useful simplifications for the next assembly

Use a slow but plainly polynomial list representation, with retained solver
answers and normal tables. Adjacent-pair type enumeration may inspect O(n^2)
pairs before retaining the at most n adjacent ones; that is harmless for FPT but
must not be reported as n total elementary operations. Ordinary and forced row
constructors can recompute prefixes; the quadratic arithmetic bound already
allows this. The point-ordering phase may use all-pairs comparisons; no optimized
sorting theorem for the current pure implementation is required. The final
polynomial degree need not match the manuscript's sharper oracle-count formula.

The frozen input model, targets, and paper interface are unchanged. No external
result has been added as a project axiom. All new theorems must appear in both
Check.lean and the fail-closed transitive axiom allowlist.

## Proposed final substitution (not yet a coverage theorem)

Let t=n+L+2, A(q)=(q+1)6^q, and F(q)=rowCallFactor(q)+1.
If the external ILP primitive costs I(q)B^c on a B-bit input and exact rank costs
R B^e, the checked solver/rank contributions are respectively

    F(q) I(q) 168^c t^(4c+1),
    2(A(q)+2) R 2^e t^(2e+2).

The normal arithmetic/comparison contribution, under a standard per-operation
bound H B^a at the certified bit envelope, is

    (q+4)^(6q+13) H 3^a t^(2a).

The new row ASTs allow at most 144t^2 reads/arithmetic nodes per query, hence
144 F(q)t^3 such nodes across the entire retained query schedule. If those reads
and operations can be implemented with a uniform H(14t^2)^a bound, their
contribution is at most

    144 F(q) H 14^a t^(2a+3).

This last premise must be instantiated using the chosen storage representation;
in particular an AST atom cannot hide an unbounded computation. The source
already distinguishes literal values from the cost of obtaining those values.
The certified point comparison schedule contributes at most (A(q)+2)^2(n+1)^3
coordinate visits. Enumeration of all candidate keys, including untested ones,
must use the bound on the complete key-list length, not firstWitnessCalls.

This does not require operational semantics for every Lean list routine. A
standard finite-table construction/traversal/sorting primitive may carry its
known size-polynomial contract. The new obligation is to identify all calls,
prove their sizes and multiplicities, and preserve the already certified output.
Do not expand this checkpoint into a verification of general-purpose libraries.

After the representation overhead is established with any fixed polynomial
exponent h, the final exponent can be max(h,4c+1,2e+2,2a+3). The coefficient is
a sum/product of parameter-only factors and the external primitive constants.
The previously proved q<=K+1 translates it to the original K. The compression
substitution then multiplies this fixed input exponent by four and
adds the external compression preprocessing cost. Mind the offset: the current
phase bound uses n+L+2, while compression_cost_substitution is stated for
n+L+1. With L <= 18(n+1)^4, use n+L+2 <= 20(n+1)^4, giving 20^c
rather than 19^c. A wrapper for this offset still has to be proved; do not invoke
the existing lemma with a mismatched premise. None of these algebraic
steps requires re-proving the known primitive algorithms.
