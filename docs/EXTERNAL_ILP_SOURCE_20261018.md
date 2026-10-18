# External integer-programming result and application boundary

Primary source re-read on 2026-10-18:
Robert Bredereck, Piotr Faliszewski, Rolf Niedermeier, Piotr Skowron,
Nimrod Talmon, *Mixed Integer Programming with Convex/Concave Constraints:
Fixed-Parameter Tractability and Applications to Multicovering and Voting*,
arXiv:1709.02850v2, 2017-11-20.
https://arxiv.org/pdf/1709.02850 (the retrieved PDF identifies itself as v2).

Theorem 1, PDF page 7, attributes the fixed-integer-dimension algorithm to
Lenstra, Frank--Tardos and Kannan. It states a running time of
O(r^(2.5r+o(r)) |I|), where r counts integer variables and |I| is the input
bit length. The preceding discussion concerns finding a feasible solution,
not merely a Boolean decision. We only need the weaker r^{O(r)} poly(|I|)
form. The nonlinear-extension Theorem 2 is unnecessary for our explicit
linear epigraph rows.

Our obligation is to supply the actual integer row system, witness decoding,
variable bound and polynomial payload. These are represented by the encoding,
row-solver bridge and payload modules. PolynomialPayload now gives a coarse
168(n+L+2)^4 payload bound when input magnitudes are at most 2^L.
The supplied solver's runtime remains an external contract. Theorem 1 is not
implemented or introduced as a new Lean axiom.

Free signed auxiliary variables can be handled by the usual positive-minus-negative
conversion if the chosen external statement uses nonnegative variables. This
can double the number of integer variables and retains O(q); do not identify
the implementation's signed 2q variables with a nonnegative 2q formulation
without that conversion. In this knapsack model the selected counts and their
prefix-cost witnesses can alternatively be chosen nonnegative.
