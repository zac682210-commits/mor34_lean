# Construction coverage review — 18 October 2026

This checkpoint continues the user-approved new-proof-only scope. The established
ILP, exact-rank, Frank–Tardos, arithmetic and sorting algorithms remain external
primitives. No compiler-runtime verification is claimed. Read ACCEPTANCE.json
for the accepted source commit and CI evidence; the source draft alone does not
establish acceptance.

## New representation choices and semantic connections

1. `chargedMap`, `chargedFlatMap`, `chargedFilter`, and `chargedFilterMap` record
   callback work and list-cell construction/traversal. Flat-map also charges the
   copied left block. Rejected filter entries are visited and charged.
2. `chargedFinFunctions` constructs each smaller-rank layer once, then retains
   it while constructing dense finite functions. `chargedNormalKeys` charges
   the complete generated key list, even if search stops on its first candidate.
   Its value is the original `normalSearchKeys` list, in the same order.
3. `matrixNormalSearchBuilt` uses that list in the actual candidate search.
   `builtCountForms` retains its answer, and `builtNormalBasisSearch` consumes
   the returned forms once at each visited basis state. The basis result is
   proved equal to the existing `basisSearch`, including early termination.
   Its charge covers normals and dense form records, not ILP or set insertion.
4. `chargedAdjacentIndices` inspects each class item's successor, so it generates
   adjacent pairs without enumerating all ordered pairs. Every adjacent pair is
   present, and list length is at most the total number n of items.
   `constructedWitnessTable` consumes this list. Its tight-point finite set is
   exactly the old stored witness set. `constructedNormalizedPipeline_correct`
   transports the full dimension/facet/basis output contract.
5. `chargedResidualWeights` filters out the two forced indices and reads the
   remaining weights. The constructed index list equals the old sorted allowed
   set. Every indexed weight equals `forcedResidualWeights`; the ordering is
   part of the theorem, not only a multiset equality.
6. `chargedAllResidualTables` builds and retains all such tables. `chargedListRead`
   explicitly traverses stored cells. A read from a supplied retained residual
   table returns the old residual weight and visits at most m_j+1 cells.
   The read theorem assumes equality to the already built table; it does not
   rebuild a residual table at each access.
7. `chargedPrefixConstruction` creates prefix indices by filtering a finite range,
   reads the retained weights, and creates the integer-expression nodes. Its
   expression equals `prefixConstruction`, and its interpreted value is
   `prefixCost`. No ordering/sorting cost is hidden in the prefix constructor.
8. `builtPrefixRow`, `builtForcedSlope`, `builtForcedRow`, `builtCountRow`, and
   `builtViolationRow` use these explicit prefix constructors. Their output ASTs
   equal the earlier constructors, whose interpretation equals the intended
   rational inequalities. Dense coefficient/constant access has an explicit
   scalar-read budget R.

## Bounds (n = number of items, q = number of classes)

All bounds below concern the specified reference charges. Integer bit costs and
external solver costs are not silently included in a unit structural charge.

| Operation | Checked bound | Conditions |
|---|---:|---|
| Finite functions of arity r into d | `(r+3)^2 (d+1)^(r+1)` | all nonnegative r,d |
| Normal-key generation, s rows/d columns | `normalKeyBuildBudget d` | `s <= d` |
| Normal-key parameter factor | `(d+4)^(2d+7)` | all d |
| Aggregate normal arithmetic plus key generation | `(q+5)^(6q+14)` | actual cell-search charges |
| Construct all adjacent indices | `8(n+1)^2` | `q <= n`, `m_j <= n` |
| Construct all residual tables | `18(n+1)^3` | one input read `R <= n+1` |
| Read a retained residual table | `m_j+1` | no rebuilding |
| Construct one prefix expression | `m_j(R+8)+2` | stored weight read budget R |
| Construct one complete forced-row system | `192(n+1)^3` | `R <= n+1` |
| Construct one count-row system | `768(n+1)^4` | `r <= 3q+1`, `R <= 4(n+1)^2` |
| Construct the violation-row system | `768(n+1)^4` | `R <= 4(n+1)^2` |

The count-row read budget allows a flattened table of up to 3q+1 inequalities:
`r(q+1)+1 <= 4(n+1)^2`. Thus the quadratic-read premise is tied to a concrete
size estimate, rather than assuming constant access to arbitrary expressions.
The normal-entry charges use standard dense finite-table operations; the exact
cost of a particular Lean backend's list representation is outside this scope.

The normal parameter factor has exponent linear in q. Consequently this added
work preserves `2^{O(q log(q+1))}`, rather than merely an unspecified FPT factor.
The envelope is intentionally coarse and is not presented as the paper's sharp
oracle-count formula.

## Compression offset

The current phase bounds use `n+L+2`. From `L <= 18(n+1)^4`, the new theorem proves
`n+L+2 <= 20(n+1)^4`. Substitution yields

    cost <= F(n+L+2)^c  ==>  cost <= F 20^c (n+1)^(4c).

A further theorem combines this with an explicitly supplied preprocessing bound.
This implication is useful, but its premise is still a core-cost premise; it is
not a proof that the entire algorithm is covered by that core cost.

## Remaining coverage obligations

The preceding source establishes substantial local construction bounds and
several exact implementation substitutions. It does not yet establish the full
reference-program time theorem. Keep `complete_FPT_complexity = false`.

1. Assemble the actual request schedule with row construction, parity substitution,
   integer-expression evaluation, query emission, and all solver calls. The old
   quadratic AST arithmetic bound and the new construction bounds cover different
   operations; both must be included. Do not infer total bit cost from AST counts.
2. Account for preprocessing/grouping/order construction and selected-point/set
   storage, including the finite parity/cell index families and rank matrices.
   Existing cardinality, coordinate and pairwise comparison bounds should be
   instantiated using standard finite-collection/sorting contracts. Do not prove
   those established algorithms internally or assume a final aggregate bound.
3. Put the local charges into one phase-complete reference execution, prove its
   total bound, and apply the now checked compression substitution. Preserve the
   existing output equality; no new geometric or exchange proof is missing.

In particular, the stored residual table must be passed into its row constructor
once, and the already charged normal-form result must be retained. Re-evaluating
an opaque old pure function can invalidate the intended one-construction budget.
The charge projection is an instrumented mathematical trace; computing that
projection for diagnostics is not an extra step in the target algorithm.

## Local review

The finite-function/key bounds include empty arities and empty domains. Matrix
search uses positive d=q+1. Adjacency completeness uses the actual successor and
therefore handles singleton classes by producing no entries. Prefix filtering
allows z beyond a class size and still agrees with `classPrefix`; indexed residual
reads require a valid Fin index. All row-cost hypotheses derive q and class-size
bounds from WellFormed. No change was made to Model, Targets or PaperInterface.

No performance benchmark or additional theorem is inferred from runtime smoke
checks. The CI artifact, source hashes and transitive axiom audit are the
acceptance evidence for the stated Lean results.

## Concrete next assembly, after inspecting the callers

`normalizeRawExecutable` computes the distinct coefficient set, its ordered
fibers, and the within-fiber weight ordering. Its output functions must be exposed
as retained scalar tables before applying the new R-bound. A standard finite
array/list preprocessing contract is sufficient; claiming that an arbitrary
function `P.weight` is a unit read is not. The proof of the raw normalization's
semantic correspondence is already present and need not be repeated.

The supported branch has the following finite schedule:

- retain a normalized input and one adjacent-index/residual table family;
- retain the parity support answer and its 2q attained extrema witnesses;
- enumerate each of the at most 3^q modes in every supported parity;
- at each of at most q+1 basis stages, retain the generated forms and issue the
  at most 2(q+1) outside tests; use the existing early-stop charge;
- map the selected count points to binary prefixes and append both endpoints
  for every successful adjacent exchange, using the retained solver answers;
- order/deduplicate that point family once, and follow the actual rank-basis
  search, including its two rank calls per tested candidate;
- relabel the at most n+1 retained binary points through the stored item map.

The new constructor budgets do not include repeated evaluation of the expression
ASTs. Their arithmetic/read node bounds are in the previous checkpoint and can
be added once per emitted row before invoking the existing bit envelopes. The
normal-form constructor's dense-record allocation charge is likewise separate
from any set insertion or outside-query construction.

`constructionPhase_budget` is now a proved subtotal:

    residual table charge + all-row construction allowance
       + normal arithmetic/key charge
       <= (18 + 768(rowCallFactor(q)+1) + builtNormalParameter(q)) (n+1)^5.

It deliberately uses the already checked all-solver-call upper budget; it does
not identify this subtotal with full runtime. For output ordering, reuse the
existing coordinate and pairwise comparison bounds instead of proving sorting
internals. This caller inspection narrows the next task to schedule/primitive
composition and avoids reopening any structural lemma.

## Distinction between construction trace and primitive implementation

The row builders return exact expression data and a reference construction charge.
Their read-cost premise must be realized by the retained table at the call site.
In particular, `forcedResidualWeights` denotes the old mathematical function;
`storedResidualRead_value` is the theorem permitting replacement by the new table
reader. It does not make every occurrence of that pure function a cheap read
automatically. The residual length/empty flag must likewise be retained metadata.
The row-building subtotal remains conditional on these local read contracts until
that caller substitution is made. This is why the full-phase flags remain false.
