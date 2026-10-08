# Density matrix and report proof contract

S024 after [actual density foundations](density-foundation-certification.md). The following integration obligations are now discharged by [full density-report certification](density-report-certification.md); this contract preserves the selected target and claim boundary. Retain the original estimator and full-class guarantee; do not replace the main theorem by assumed primal feasibility or already-correct density bands.

## Actual matrix representation

The cell vector has k*k entries in row-major order i*k+j. `finProdFinEquiv` maps `(i,j)` to `j+k*i`, with inverse `(divNat,modNat)`, matching the runtime. Prove exact sum/indicator identities connecting this real vector of actual means to `DensityCellFeasible`.

The expected equality rows are the k row sums followed by the k column sums, all with right side k. The inequality rows are:

- For each p,q in 0..k, prefix indicator and its negative, in that order; right sides k*k*(count/n+radius) and k*k*(radius-count/n).
- For each cell (i,j), the valid neighbor (i+1,j) followed by (i,j+1). Each contributes the difference row and its negative, with right side 2/k. Invalid neighbors contribute no rows.

Use typed corner/adjacency descriptors or an exact list enumeration matching these loops. Derive each matrix inequality/equality from actual cell restrictions. A representation checker may reject supplied matrices that differ from the expected rational model. Prove its soundness, not a generic theorem whose main inputs merely assert that the actual primal vector is feasible.

Instantiate `rationalDual_checker_sound` with the actual real cell vector, lower box 1/2 and upper box 3/2. A supplied objective is exactly plus or minus one at its checked cell and zero elsewhere. Sign-valid rational y and free rational z, including nonzero residuals, must give the reported exact bound. Combine the two signs and box clipping to establish reported cell intervals. Expand by 2/k and clip to the original density range for every point of each closed cell. A contradictory interval triggers conservative fallback; solver success is not an input to any main conclusion.

## One orientation and histogram fields

Accepted CDF coverage provides one swap. Convert its `orientCDF` statement to ordinary CDF accuracy against `rho` or `transposeDensity rho`. Both are in original K. Use that same density for cell feasibility, every cell/point interval and histogram error. Do not choose separate orientations per field, cell or point.

Histogram coefficients are arbitrary rationals in [1/2,3/2], potentially rounded and without uniform margins. Prove the exact finite prefix sum/count representation. The checked corner excess eta is nonnegative and bounds every corner discrepancy beyond the CDF radius a. Apply `histogram_point_error` to get the reported cap `min(1,8*a*k*k+4*eta*k*k+2/k)` simultaneously for all closed-cell points. Solver/inconsistent-bound fallback requires all cell and point intervals to be [1/2,3/2] and histogram error one, with coefficients still box checked. The runtime verifier now checks all four interval fields, but this branch must still receive a formal report proof.

## Actual full-report probability

Keep q, both tolerances and their budgets fixed before sampling, as selected from n and requested delta. Data-dependent cutoff, estimator grid and checked solver certificates can be handled by the simultaneous all-threshold CDF event. Passing individual calibration checks does not authorize choosing calibration parameters from observed data without further probability control.

Define full-report success as a predicate of the finite observed `OrderCode`. It may quantify over every accepted decoded report, every cell and every real point; its pullback under `sampledOrder` is measurable because the code domain is finite. On the actual accuracy event, original-K support and injectivity hold almost everywhere and all accepted reports satisfy their fields under one orientation per report. Then derive the unconditional accepted-output failure bound, with the exact rounded failure and requested-delta/fallback branches. Do not claim conditional-on-acceptance coverage or whole-Python-runtime verification.

Retain matching Lean/Python representation fixtures, nonzero dual residual and adversarial/fallback tests as supplementary evidence. Complete fresh GCP root/type/axiom acceptance for the integrated main theorem, focused source/evidence pushes, supplementary CI and stopped-instance closeout before marking S024 complete. S025 remains a separate genuine 2+1 geometric/measure campaign.

Remaining to-do list: S025.
