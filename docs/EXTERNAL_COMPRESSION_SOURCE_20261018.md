# External compression source and checked application

Checked primary source: Michael Etscheid, Stefan Kratsch, Matthias Mnich and Heiko Röglin, *Polynomial Kernels for Weighted Problems*, arXiv:1507.03439v1, July 13, 2015, Section 3.1, Theorem 1 and Example 1, PDF page 4.

https://arxiv.org/pdf/1507.03439v1

Theorem 1 attributes the transformation to Frank and Tardos. Its output bound is 2^(4 r^3) N^(r(r+2)); integer test vectors with l1 norm at most N-1 retain their dot-product sign. The paragraph immediately following states strongly polynomial running time. Example 1 applies the augmented test (x,-1) and derives fourth-degree total encoding size.

Our interface uses an arbitrary finite index type and integer inputs, a special case of rational inputs. `PreservesSmallSigns M` denotes preservation for l1 norm <= M. For an n-item instance, the cited theorem is used with r=n+1, N=n+2, so our M=n+1. Option(Fin n) is only a reindexing of the r coordinates.

The formalized application tests binary comparison vectors, coordinate units and differences of two units. These give output transport and exact parameter preservation. The coefficient bound is a separate premise used by CompressionSize; it is not implied by sign preservation alone.

No external result is installed as a custom Lean axiom. Compression existence and its algorithmic complexity remain cited external inputs, by the user's scope decision.
