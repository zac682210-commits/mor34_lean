# Remaining row-encoding proof: checked expressions and target bounds

This is a mathematical continuation plan, not an additional Lean-checked full encoding theorem. The existing kernel-checked helper theorems are identified separately. The intended input bound is an integer M>=1 dominating |weight_i|, |coefficient_j|, |capacity| and |rhs|. Put n=card(Item m)>=1, q<=n and N=n+1.

## Bounds directly supported by the definitions

- An ordinary slope intercept is w_t t - prefixCost(w,t). PrefixEncodingBounds gives magnitude <=2sM<=2nM.
- A forced slope intercept is (t+1) w_t - prefixCost(w,t) - w_v. The new helper gives <=(2s+2)M<=(2n+2)M, where s is the residual class size. The residual weights are selected original weights; no new magnitude assumption is needed.
- The empty-residual forced row has constant -w_v, hence magnitude <=M.
- Candidate equality rows have coefficients +/-c_j and constants +/-rhs, bounded by M.
- Strict invalidity uses -rhs-1, so M+1 is needed; do not forget this offset.
- Count upper bounds are at most n. Forced count upper bounds are m_j-1 and lower bound is 1.
- Each cell coordinate contributes THREE actual rows: lower, upper, and a guard. This is important for a source-aligned row count. cellQueries_length proves 3q, and the scalar-oracle call row count is exactly n+5q+4. The guard can be 0<=-1, encoding an empty cell; it must not be omitted.
- Cell endpoints/shifted bounds have magnitudes at most n+2 when low/high are attained bounded extrema. Coordinate coefficients have magnitude <=1.
- The actual added normal has H=2(q+1)!N^(q+1). Strict-side rows have coefficient bound H, right-side bound H+1.

A convenient deliberately loose common bound before parity substitution is

C=M+H+1,
R=(2n+2)M+(n+2)+(H+1).

Every count coefficient is bounded by C, every cost coefficient by 1, and every right side by R for the actual ordinary/forced/invalidity/cell/normal row families after instantiating the finite extra-query list. Prove the finite constructor cases; do not claim the generic countRow theorem for arbitrary rational A,b without assumptions on those extra rows.

## Parity and encoding

The implemented substitution only changes count coefficients and right side. It sends the bounds (C,R) to (2C,R+qC), leaving the cost block unchanged. NormalQueryBounds already proves this for IntegerQuery and connects it to withParity. Generalize that elementary bound to a CountInequality whose coefficients are explicit integer casts; all actual rows have integer data even though the shared row record stores rationals.

Thus each row can be encoded with 2q integer coefficients and one integer right side, whose signed bit length is bounded by a function of log(M+1), log(n+1), and q(log(q+1)+log(n+1)). The determinant term contributes no dependence exponential in the INPUT BIT LENGTH. The exact coefficient-value bound may be large in q; its logarithm is the relevant quantity.

The next formal step should define one concrete signed-integer encoding length, prove a monotone bound for an entire row family, then combine the already checked row-count identities. The count bounds alone are not a proof of a primitive ILP runtime, exact-rank runtime or the full FPT statement.

## Cost caveat

For the small normal matrices, d=q+1 and r<=d. The d^r pivot candidate count is compatible with 2^{O(q log(q+1))}, but checking injectivity, evaluating determinant expansions, selecting independent rows and constructing all normals still need an explicit arithmetic-cost accounting. The final rank matrix has n+1 columns; parameter-sized exhaustive determinant enumeration must not be used there.
