# Winkler full-text comparison

2026-10-07, Quantyra Space E002/S010. Both complete articles have now been read and compared with the finite realizer lemma and inverse bound. The author purchased these papers and supplied the published PDFs by email. They were retrieved with the authorized AIOS OAuth/Gmail API route. Purchased PDFs, extracted text and raw mail provenance are retained privately outside Git and are not redistributed here.

## Acquired sources

| Paper | Version and pagination | Bytes | SHA256 |
| --- | --- | ---: | --- |
| Peter Winkler, [Random orders](https://doi.org/10.1007/BF00582738) | Published article, Order 1 (1985), 317-331; 15 PDF pages | 837218 | `0726078c42118e5bfa8d7d588c1d4b8240cb8c90970686e952591840991f14bd` |
| Peter Winkler, [Random orders of dimension 2](https://doi.org/10.1007/BF00383197) | Published article, Order 7, 329-339; 11 PDF pages; the PDF prints 1991 | 584793 | `41f95b0cb224c8b709764826f418ad20c444297168cc46290030c69faaa52b47` |

Original attachment filenames encode the respective DOIs: `art_3A10.1007_2FBF00582738.pdf` and `art_3A10.1007_2FBF00383197.pdf`. Private provenance records the authenticated source mailbox, selected message/thread, sender, subject, date, original filename, retrieval timestamp, local path, size and hash. The custody root is `%USERPROFILE%/.quantyra/gmail/research/S010`; it is outside every Git checkout.

Both titles, first/last printed article pages and complete PDF page counts were verified. Neither PDF is encrypted; every page has nonempty extracted text (26/26 total). This verifies complete artifacts rather than abstract-only publisher pages. It does not establish that the proofs have been fully compared.

Year discrepancy: the dimension-two article's first page prints 1991, matching the author's bibliography; Springer's [article metadata](https://link.springer.com/article/10.1007/BF00383197) reports December 1990. Preserve both provenance facts in later citations instead of silently assuming the PDF and online metadata use the same year.

## Comparison contract

Compare exact statements and proof locations against the finite occupied-grid theorem controlling every two-order realizer up to one global swap, and against the coefficient inverse estimates for the positive Lipschitz/uniform-marginal density class. Trace orientation/realization references and relevant citing papers. Record stronger results or immediate implications, claim-by-claim dispositions and any necessary manuscript changes. General reconstruction aims, orientation forcing and infinite random-structure results are established background; acquisition alone supplies no novelty verdict.

The proof library and current published manuscript retain their existing verification and provisional-originality status. Review follows decentralized, informal open-source use and testing; specialist review is not a workflow or publication gate.

## Exact locations and implications

Page numbers below are printed journal pages. All 15 and 11 pages were read, including proofs and references; the critical formulas and arguments on 332, 334, 337 and 328-329 were also checked against page images rather than OCR alone.

### Random orders (1985)

Sections 1-2 (317-319) identify intersection of independent uniform coordinate orders with iid uniform points in a cube. This is our flat density special case, not the entire copula class K: uniform individual marginals do not imply independent coordinate rankings. Theorems 1-4 (320-326) concern minima, isolated points, height and width. Their geometric occupancy constructions are precedents for using dense samples; none states a realizer rank error or a density inverse modulus.

Section 6 is substantially closer. Theorem 5 (327) treats the box-density theory in the language retaining k coordinate orders. Theorem 6 (328) gives almost-sure isomorphism of countably infinite samples in that language. Theorem 7 and proof (328-329) use finite existential configurations in the weak poset language to force finite coordinate-order patterns up to a permutation of axes, in every augmentation. The corollary (329) asserts isomorphism of any two realizations of the infinite order as k-orders. This is an earlier coordinate-recovery/forcing method. Our finite geometric witnesses quantify related reasoning; coordinate recoverability is not a new objective or qualitative discovery.

For a positive full-support density, every rational coordinate box is almost surely eventually occupied (a countable union of zero-probability failures). Thus box-density reasoning is not confined to the flat density at the infinite level. A fixed finite pattern has the same orbit in every realizer by Theorem 7's witness proof; along increasing finite subsets, one axis permutation works on an unbounded subsequence since there are only k! choices. It therefore works on every finite subset. This is an inference from that proof, not a newly quoted numbered theorem. With sample enumeration retained, uniform marginal laws and the strong law then recover numerical coordinates from ranks. Those observations support qualitative identifiability, without a finite rate.

Theorem 6's universal *unmarked countable isomorphism type* does not assert equality of iid finite-order laws for different densities. An arbitrary countable isomorphism forgets the enumeration and sampling frequencies. It cannot be used to refute the coefficient inverse theorem. Theorem 8 (330) instead shows failure of a finite first-order zero-one law in dimension two, through reversible pairs; neither this nor the historical open problems establishes a quantitative density bound.

### Random orders of dimension 2 (PDF 1991; publisher 1990)

Section II uses P(n), the intersection of two independent uniform linear orders. Lemma 2.2 (330) relates unique transitive orientability to the absence of properly autonomous subsets, crediting Gallai/Kelly. Lemma 2.3 (331) gives the bijection between realizers of P and transitive orientations Q of its incomparability graph: the orders are P union Q and P union the reverse of Q. Lemma 2.4 (331) makes autonomous subsets convex in both original orders. These are structural ingredients underlying our forcing argument, not original mechanisms.

Lemma 2.5 (332) excludes properly autonomous subsets of size greater than two with probability tending to one. Its counting bound is C'_t(n)=(n-t+1)^2 t!(n-t)!/n!; the printed summation runs t=3,...,n-1, with endpoint C'_(n-1)=4/n. The middle bound and endpoint t=3 yield an O(1/n) bound for this particular event. Lemma 2.6 (333-334) gives Poisson(1) reversible-edge counts. Section II's closing argument (334), applied to the complementary realization P*, gives 2^(s+1) realizations when the remaining ambiguities are s disjoint twin pairs. Section III (334) defines those twins as adjacent in both coordinate orders, with opposite directions.

Theorem 4.3 and proof (336-337) show that, with probability tending to one, the realization count is twice the automorphism count. The proof explicitly uses the disjoint twins and excludes the rare involution exception that would identify an axis-swapped realization with an automorphism-generated one. Consequently, on the full typical event, **every realizer comes from disjoint twin transpositions and one global axis exchange**. After that exchange, each point's rank changes by at most one in each coordinate, since each transposition is adjacent and the pairs are disjoint. This rank-one statement is our immediate implication of the proof, not its verbatim theorem statement. It is stronger than our 30rn bound in the flat random model. We must not claim first recovery or first approximate rigidity of all realizers.

Lemma 2.5 alone is insufficient to justify that entire rank-one event or its failure rate: its definition excludes some degenerate configurations and Theorem 4.3 also removes another exception. We do not assign the whole rank-one event an explicit O(1/n) probability bound. Unique realizability is not necessary: Example 3.4 (335) gives its limiting probability 1/e in P(n), while twin ambiguities still permit rank-one recovery. Theorems 3.1 and 4.6 concern transfers between P(n), uniform labeled two-dimensional orders Q(n), and uniform isomorphism classes U(n). These are not exact finite labeled/unlabeled TV equality for two exchangeable density-generated laws.

Neither article gives a deterministic occupied-grid error bound, a uniform result over the nonconstant class K, a finite CDF-to-density estimate, or an explicit TV-law-to-supremum-density inverse estimate. Uniform-permutation counting does not transfer automatically to K: the coordinate permutations are dependent under a nonconstant copula. Bounded single-point densities produce exponential n-point likelihood ratios, which do not turn a flat-model o(1) statement into uniform control. An adaptation might yield a stronger result, but it is a research obligation, not a demonstrated immediate specialization.

## Claim dispositions

| Claim | Disposition | Effect on this paper |
| --- | --- | --- |
| Recovery of coordinates from order, up to axes | Established precedent: 1985 Theorem 7 and witnesses | Credit it; no general recovery novelty claim. |
| Every realizer is close to latent ranks for flat samples | Stronger implying precedent: 1991 typical-event proof gives rank error at most one | Explicitly acknowledge it; exact unique realizability is an unnecessary baseline. |
| Shared-vertex orientation forcing / realizer-orientation correspondence | Established structural methods: Gallai lineage and 1991 Lemma 2.3 | No novelty claim for these steps. |
| Deterministic occupied-grid bound with one global swap, 30rn for both ranks | Related finite geometric quantification; no identical theorem located | Candidate ingredient, narrower than first approximate rigidity. A structural adaptation could improve it. |
| Uniform CDF reconstruction 87/m with explicit failure bound over K | Quantitative consequence of the geometric lemma and standard concentration | Present as an explicit derivation; no novelty claim for concentration. |
| Original 100(N^(-1/12)+Delta_N), improved 130((log N/N)^(1/6)+Delta_N) | No matching or immediately implying uniform inverse bound found in inspected sources | Principal candidate contribution; bounded, provisional originality only. |
| All-law identifiability, exact label/unlabel TV, proper-time consequence | Qualitative precedent / general exchangeability algebra / direct consequence | Do not promote as separate discoveries. |
| Lean verification | Correctness evidence for encoded statements | Does not establish priority, significance or optimality. |

## Structural and forward tracing

See the dated [search supplement](novelty-search.md#full-text-and-citation-supplement--2026-10-07). Gallai's structural conclusions were checked through Winkler's explicit lemmas and Klavik-Zeman's Section 3; the original Gallai article and Kelly chapter were not read in full. McConnell-Spinrad's algorithm and the certifying permutation-graph paper supply a constructive route for the finite-data scope. The closest unavailable structural/counting texts remain a priority queue, not exclusions.

The bounded verdict is that the inspected literature supplies stronger flat-model realizer recovery and earlier qualitative forcing, but no established implication covering our entire nonconstant class with the stated finite inverse modulus. The working manuscript now acknowledges both Winkler papers and narrows its candidate contribution. Historical published version 0.3.0 remains immutable; the [literature revision](../manuscript/working/finite-causal-order-reconstruction.pdf) is unpublished and has no new DOI.

Remaining to-do list: none for this bounded full-text comparison. Broader priority assurance remains provisional, with the explicitly recorded literature queue; publishing the working revision is a separate action.
