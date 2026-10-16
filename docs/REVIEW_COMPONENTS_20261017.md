# Statement correspondence review: components and quotient

Manual correspondence review by the same assistant that developed the proofs; not independent review.

| Paper object or assertion | Lean representation | Scope check |
| --- | --- | --- |
| Binary item vector | `pointVector S` for a finite set of grouped items | Exactly 0 or 1 in every coordinate; no fractional points substituted |
| Tight binary set T | `tightPointSet P` | Feasibility and candidate equality retained |
| Exchange edges | `Exchange P j u v` | Ordered u<v and an actual tight witness with u absent and v present |
| Exchange components | `ExchangeComponent P` | Quotient by finite paths in `GlobalExchangeAdj P`; no assumed partition |
| Component-count map A | `componentCountMap P` | Sum of real coordinates over each quotient fiber |
| Direction span E | `exchangeDirectionSpan P` | Span of actual oriented feasible exchange differences |
| E = ker A | `exchangeDirectionSpan_eq_ker` | Generic partition helper is instantiated with actual graph quotient and proved path equivalence |
| dim E = n-C | `exchangeDirectionSpan_finrank` | Rank-nullity and surjectivity; isolates included as components |
| dim aff(T) = n-C+dim aff(A(T)) | `tight_dimension_quotient` | `Real` vector spans; nonempty T explicitly required; empty dimension -1 is not claimed |
| Prefix has the same counts | `counts_prefixSet`, `counts_bounded` | Actual class counts, including zero and full class cardinalities |
| Prefix has no greater weight | `prefixMinimality` | Exact frozen paper-facing contract, with nondecreasing weights; ties allowed |
| Prefix of a tight point remains tight | `prefix_tight` | Both feasibility and equality are proved |
| Local component interval property | `component_interval`, `connected_iff_cuts` | Same cut indexing as manuscript: cut r corresponds to Lean positions r-1,r |
| Parity interior component | `parity_interior_connected` | Paper positions l+2 through h-1 correspond to Lean values l+1 through h-2 |

The local/global component bridge and tight-prefix image identity also passed in final CI run 38931568115, commit 1ab49f5e6de4be6ad59dd31c2f34f09ebdbc6211. All 73 named theorem dependencies contain only the three allowed standard axioms. The image identity is `tight_image_eq_prefix_image`; its proof compares equally sized symmetric differences within each coefficient class. Every missing-prefix/extra-selected pair is an actual exchange witnessed by the original tight point, so the component sums agree without an iterative sorting algorithm.

The numeric count of audited theorem declarations includes small helpers and is not a percentage of the complete formalization. The full recognition algorithm, affine-cell lemma, rank field bridge and complexity bounds remain outstanding at this review checkpoint.
