# Finite order inverse rate audit

2026-10-06. Author audit of the mathematical proof in `finite-order-rate.md`. The selected finite rank theorem is additionally Lean checked; the whole inverse theorem has no formal or independent referee verification claim.

| Requirement | Evidence and disposition |
| --- | --- |
| Only abstract orders observed | A_n enumerates label-based realizers; all grid coordinates and witnesses occur only in the proof. |
| Arbitrary realizer, global swap | Every realizer gives a transitive incomparability orientation. The single AB choice fixes all separated interior edges through four forcing steps. Local ambiguous edges are counted rather than assumed absent. |
| Grid witness existence | Gap >=3r contains a grid interval; its first-column cell gives z. A,B,W are in distinct occupied cells and all required strict inequalities have margins. |
| Boundary degeneracy | At most 20r boundary fraction is discarded in the CDF comparison. No metric identification of the two empty-profile corners is needed. |
| Rank bound | Remaining comparisons are bounded by boundary count 20rn plus vertical strip count 10rn. Rank differences are differences of predecessor counts, bounded by the number of disagreements. |
| Uniform probability | Density floor supplies cell-mass bound; independent event rectangle indicators supply Hoeffding. No independence of overlapping pairs or rectangles is assumed. |
| Fixed constants and all N | n>=65536 gives failure <=12/m^2<1/10. Reconstruction error <=174n^(-1/4); interpolation gives alpha=1/12. Smaller n uses d_conf<=1. |
| Identifiability in K | The quantitative result with Delta_N=0 tends to zero, so the kernel-theory bridge is unnecessary for K. |
| Physical distance | Density coefficient is the specified metric; no curvature or carrying-capacity consequence is inferred. |
| Selected Lean target | `lean-target.md` fixes the finite rank theorem and six required components; `Bridges.lean` now proves them, including the exact original specialization. Final build and `checks/Audit.lean` both exit zero. |
| Labels and proper time | `observable-and-time-audit.md` gives exchangeable labeled/unlabeled TV equivalence and the coefficient-to-time-separation bound. These are prose proofs. |

Reproducible falsification checks:

- `python checks/check_grid_witnesses.py`: exact integer coordinates, 36 grids with random-like and corner-near placements, all qualifying edges checked. Result: 865445 separated edges passed; numerical constants passed.
- `python checks/check_small_realizers.py`: exhaustive five-event permutation orders and valid two-order realizers, testing the orientation forcing rule. Result: all 120 latent permutation orders and 771 valid realizers passed every forcing triple. Neither script proves the universal theorem.

Source comparison: [Klavik and Zeman, section 3](https://arxiv.org/html/1506.05064v1) records the known two-orientation result for prime comparability graphs. Our proof does not assume a prime sample; it constructs explicit forcing paths and counts unforced comparisons. [Winkler, Random orders of dimension 2, publisher abstract](https://link.springer.com/article/10.1007/BF00383197) reports that limiting unique-realizability probabilities are strictly between zero and one in the random models studied. This supports retaining approximate rigidity instead of assuming exact uniqueness with probability tending to one; the full article was not inspected. [Hoeffding 1963, original paper](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf) is the concentration input. No inspected source was found to state this exact density-uniform forcing estimate and coefficient bound; the search does not certify novelty.

The constant 100 is extremely conservative: the bare N term becomes nontrivial only at enormous N. The result establishes a polynomial inverse modulus, not a practical estimator or a recommended experimental sample size. Optimization is separate research.

2026-10-06 final source comparison rechecked the prime-orientation statement in Klavik and Zeman section 3 and Braun's all-law reconstruction Theorem 1.4. Searches for partial-order/permuton reconstruction, random dimension-two orders, approximate permutation representations, and quantitative two-dimensional causal reconstruction located no inspected theorem stating our exact occupancy-to-rank bound or its coefficient inverse-rate specialization. Winkler remains an abstract-level comparison, not a full-paper exclusion. The inference is a provisional distinction, not a certification of originality. Do not claim event labels alone distinguish this result: for iid samples labeled and unlabeled order-law TV agree.

Remaining to-do list for the bounded derivation and selected formal target: none. Originality remains provisional and discovery claims require supporting evidence. The open-source workflow records actual informal feedback/use/testing; specialist review is not a publication gate.
