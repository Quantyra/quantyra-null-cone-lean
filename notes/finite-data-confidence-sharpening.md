# Separate marginal and joint-CDF concentration

2026-10-07, E002/S020. Ordinary probability proof and Python certificates; no new Lean theorem. Full smooth K, iid points, directed order and one global transpose are unchanged. The [legacy method](finite-data-certified-method.md) and its [calibration limitation](finite-data-calibration-limit.md) remain valid historical results.

## Imported result and applicability

[Reeve (2024), Corollary 2](https://arxiv.org/html/2403.16651), with its Section 3 proof, gives a finite one-sided empirical-CDF tail no larger than exp(-2n epsilon^2) for every epsilon >=0. Reflection bounds the other side; continuity handles left limits. A union bound gives the usual two-sided DKW-Massart bound 2 exp(-2n epsilon^2). Apply this separately to both uniform margins. Coordinates may be dependent; independence is needed across sampled points.

We inspected [Naaman (2021), Theorem 3.2, equation (3.10)](https://www.researchgate.net/publication/349868346_On_the_tight_constant_in_the_multivariate_Dvoretzky-Kiefer-Wolfowitz_inequality), DOI [10.1016/j.spl.2021.109088](https://doi.org/10.1016/j.spl.2021.109088). Its stated multivariate constant applies above an unspecified distribution-dependent sample cutoff. It does not supply our explicit finite guarantee uniform over K. We retain finite grid Hoeffding for the joint CDF. This is an applicability decision, not a verdict on other results in that paper.

## Simultaneous event and reconstruction

Fix n, delta, q and positive budgets delta_m+delta_j=delta before observing the order. With probability at least 1 minus

    4 exp(-2n epsilon_m^2) + 2(q+1)^2 exp(-2n epsilon_j^2),

both latent marginal sup errors are <=epsilon_m and every joint-CDF vertex of the fixed q-grid has error <=epsilon_j. The second term follows from two-sided Hoeffding for iid rectangle indicators and a finite union bound. The events need not be independent.

Uniform marginals imply that changing both population thresholds by at most h costs <=2h after clipping. Sandwich an arbitrary threshold between adjacent grid corners to extend joint error to epsilon_j+2/q. Marginal error has no discretization penalty.

Use the existing original-graph forcing certificate: d_i bounds both rank disagreements after one common swap; b_j=#{i:d_i>j}/n. Inclusive latent ranks equal empirical marginal CDF values; ties have probability zero. On retained points, selected rank coordinates therefore differ from latent coordinates by <=h=j/n+epsilon_m. Both clipped orthant sandwiches lose at most b_j mass. Replacing the latent empirical joint CDF costs epsilon_j+2/q, and shifting population thresholds costs <=2h. Thus, on the same event, simultaneously for all realizers and all j,

    min_S ||A_P-C_(rho composed with S)||_infinity
        <= b_j+2j/n+2epsilon_m+epsilon_j+2/q.

Data-dependent trimming adds no penalty because this event already controls every j. The reported radius is a=min(1,B(P)+2epsilon_m+epsilon_j+2/q). The same global S applies to the CDF and downstream LP bands. Radius one is deterministic with failure zero. No occupied-grid event or distribution-dependent cutoff is assumed.

## Deterministic selection and exact rounding

`split-dkw` considers delta_m/delta in {1/8,...,7/8} and meshes that are powers of two from 1 through 4096, plus floor(sqrt(n)) clipped to that range. It minimizes 2epsilon_m+epsilon_j+2/q using only n and delta. Pre-sample selection incurs no union over candidates.

For each budget and prefactor (4 for margins, 2(q+1)^2 for the joint grid), binary search selects epsilon in multiples of 10^-6. The exact rational inequality exp(-t)<=(1+t/512)^(-512) certifies each failure term. Round upward to denominator 10^12 times the corresponding budget's denominator. Since the budget lies on that grid, rounding a value <=budget cannot exceed budget. Sum both rounded failures. If epsilon=1 cannot meet an extremely small budget, the resulting radius is already >=1 and uses the deterministic fallback.

Old `grid` reports, including schema-1 reports without a method field, retain their original interpretation. New estimates default to `split-dkw`; the independent standard-library verifier reconstructs the named calibration, allocations, epsilons and outward failures. Cached values are immutable; callers receive fresh dictionaries.

At delta=1/20 with zero rank budget:

| n | Legacy grid | Split DKW |
| --- | ---: | ---: |
| 512 | 0.376802 | 0.2698555 |
| 3072 | 0.1629395 | 0.11308625 |
| 4096 | 0.142155 | 0.098345125 |

The larger settings can cross the no-data flat-CDF prior 1/8 when B(P) is small enough. This supersedes the obstruction only for the new calibration. It does not establish useful density recovery, optimality or new priority. Experiments and density limitations are recorded separately.

The [delivery audit and observed-order comparison](finite-data-sharpening-audit.md) demonstrate the CDF improvement and retain the negative density-paper decision.

Remaining to-do list: none for this calibration derivation. Publication choice and density-specific research remain separate.
