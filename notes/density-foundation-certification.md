# Actual density cell and histogram foundations: partial S024

2026-10-07 local date (2026-10-08 UTC). Actual original-K cell restrictions, all-point expansion and conditional rounded-histogram error are now Lean proved. The executable LP matrix and full density-report probability bridges remain open.

`DensityCells.lean` defines a cell mean as actual density-measure mass divided by square area. It derives the product-volume area, integral representation, [1/2,3/2] bounds and four-corner CDF identity. Integrability comes from original-K continuity on the square; a feasible vector or target cell bound is not assumed.

`DensityCellBias.lean` proves the affine chord majorant of distance to any point of an interval and its exact average. Euclidean distance is bounded by coordinate distances; actual Lipschitz constant two and the integrated chord yield `|cellMean-rho(p)|<=2*w`. The point may lie anywhere in the closed cell, including corners and grid boundaries. This proves the all-point 2/k expansion, not merely a center estimate.

`DensityCellTranslations.lean` proves the translated integral identity and derives adjacent mean difference at most 2*w from the true Euclidean translation distance w. Transpose transport supplies the vertical result. No adjacency restriction is an input assumption.

`DensityCellGrid.lean` specializes to width 1/k, proves the box restrictions and telescopes actual cell masses into exact population-CDF prefixes. The zero-boundary CDF identities are derived from actual uniform marginals and nonnegative measure. `DensityCellRestrictions.lean` derives row and column sums equal k, both adjacency restrictions, all-point bias and both scaled CDF-prefix inequalities.

`DensityFeasibility.lean` packages these facts in `DensityCellFeasible`. `grid_cell_feasible` takes original K, k>0 and CDF quality, and proves every semantic LP restriction for the actual cell means. It does not take primal feasibility, box restrictions, marginal sums or an adjacency bound as premises. CDF quality remains an explicit deterministic premise here; its probability has already been proved for accepted order-only CDF reports. The next campaign must connect both through the executable matrices and one common orientation.

`DensityHistogram.lean` defines the supplied histogram's actual prefix sums. Finite differences recover each coefficient exactly. If the order-only CDF radius is a and the histogram's corner excess is eta, four-corner differencing gives cell error `4*k^2*(2*a+eta)`. Combining this with the all-point cell bias proves

`|histogramCell-rho(p)| <= min(1, 8*a*k^2+4*eta*k^2+2/k)`.

Histogram coefficients only need to lie in [1/2,3/2]. Uniform histogram marginals, numerical solver success and histogram primal feasibility are not assumed. The cap of one follows from the true density and coefficient boxes. This includes rounded coefficients that violate numerical LP restrictions, provided their actual corner excess is supplied and checked. Full-range bands remain uninformative; formal verification does not change the practical negative result.

Authoritative acceptance: `space-density-foundation-acceptance-20261008T044259Z-178ba7`, GCP project `quantyra-lean-cert-20260915`, instance `quantyra-lean-builder-01`, zone `us-central1-a`. Root build: 2947 jobs and 186 exact-type/axiom audits, exit zero with no warnings or added axioms. The [receipt](../evidence/gcp/space-density-foundation-acceptance-20261008T044259Z-178ba7/receipt.json), immutable source/dependency hashes and raw logs preserve exact accepted bytes. Lean 4.30.0 and all nine dependency pins remain unchanged. Local Lean invocations: zero.

The [development ledger](../evidence/gcp/density-foundation-development-index.json) retains nine captures: five failed attempts, three clean intermediate builds and the final clean root acceptance. The first capture also retains its boot-time SSH preflight failure and successful same-input submission. No remote work was restarted solely because observation expired. Manuscripts/DOI artifacts and the tested Python estimator remain preserved.

Remaining to-do list: faithful executable LP matrix and flattened-cell representation; instantiate rational dual checks with actual cell feasibility and one report orientation; density-band/fallback/histogram field checking and measurable full-report coverage; final S024 acceptance/delivery; S025.
