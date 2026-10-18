# Next: phase-complete reference cost

Read ACCEPTANCE.json and CONSTRUCTION_COVERAGE_20261018.md first. Do not restart
core geometry, residual table construction, finite-key generation or compression
offset proofs. The new-proof-only scope remains in force.

Most local representation obligations now have explicit constructors and value
preservation. Still open: full schedule composition, preprocessing/point-family
storage and ordering, and total bit-cost substitution. The existing AST
arithmetic count is separate from new AST/list creation charges. Reuse all
existing local size/count bounds with standard primitive contracts; do not
expand into verification of ILP/rank/FT/sorting internals or compiler runtime.

Prioritize one complete reference execution and its phase coverage. Simply
defining a sum of plausible budgets or assuming a total cost premise does not
close the remaining application proof. Preserve full output equality and the
explicit q-log-q parameter factor. Keep the full-FPT flags false until this is
finished. The six-item example remains outside the general theorem acceptance.
