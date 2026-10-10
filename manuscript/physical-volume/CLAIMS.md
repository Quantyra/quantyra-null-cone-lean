# Frozen manuscript scope

2026-10-10, S048, selected by Dan's goal **Prepare the manuscript**.
Working title: **Interval volume from thinned causal orders: finite confidence
and calibration limits**. Author: Daniel Eric Fredriksen, Quantyra Inc.
Version 0.1.0, unpublished preparation. Technical ownership remains in this
satellite; planning is in Quantyra-Space-Planning/S048.

## Experiment and contribution

The main target is v = integral over (0,1/2)^2 of rho on D=[0,1]^2.
The original class K consists of neighborhood-smooth densities bounded
between 1/2 and 3/2, Euclidean Lipschitz constant at most two and exact
uniform coordinate marginals. The density normalizes the total volume to
one. The metric convention is `-rho(du tensor dv + dv tensor du)`, with
future direction increasing both null coordinates. The target is a
dimensionless normalized volume, not an inferred absolute physical scale.

The unknown measurable detector is globally in [1/R,1], with known
deterministic R in [1,2] for the joint theorem. Observe all strict directed
relations among n retained events and the two fixed marked anchors (0,0),
(1/2,1/2), modulo sample permutations fixing anchor roles. Coordinates,
rejected locations, generated counts, detector values and clocks are not
part of this fixed-retained-count experiment. The stronger process
statements explicitly distinguish what a generated-count experiment records.
Lower bounds allow every measurable real-valued estimator and an arbitrary
common independent probability seed.

The contribution is the connected geometric and observation model, finite
upper/lower accuracy bounds, admissible full-law alternatives, executable
confidence certificate and formal/reproducible evidence. Generic thinning,
bounded-selection transforms and binomial confidence calibration are
established ingredients and receive explicit attribution.

## Claim outline and proof obligations

1. **Main finite joint result.** For n>=1, a=1/sqrt(n), b=(R-1)/(R+1),
   s=min(1,a+b), the observed membership fraction has failure probability
   at most 1/20 at strict radius 2s. Every eligible randomized full-order
   estimator has failure at least 1/4 at strict radius s/256 under some
   admitted model. Include R=1 and R depending on n. Explain the
   fixed-confidence minimax interpretation without optimal-constant claims.
2. **Thinning interpretation.** Prove the one-event product identity, the
   exact selected-pattern and retained-count/tuple law for finite generated
   N, independently mixed N, finite Poisson generation, its Laplace
   functional and the a.s.-terminating first-n retention experiment. Include
   zero retained events, Z=1 and zero-probability conditioning boundaries.
   The ordinary terminal combinatorial coefficient will be clearly
   distinguished from Lean's finite-pattern representation.
3. **Finite report.** Derive retention identification bounds and their
   monotone composition with exact binomial intervals. Prove the finite
   tail-p-value argument for arbitrary valid endpoint tables, rational
   integer certificates/recurrence and physical coverage. Include n=0 and
   the known geometric range [1/8,3/8]; empty intersections in the second
   study are empty reports, not fallback intervals. Attribute binary
   transforms to Aronow-Lee and confidence inversion to Clopper-Pearson.
4. **Complete lower constructions.** Prove K membership and target integrals
   for `rho_e=1+e(2u-1)(2v-1)`, its actual product likelihood and second
   moment, the finite divergence bound, full observation contraction and
   arbitrary-seed testing. Use the globally clamped compensating detector
   for exact full-law confounding and the uniform joint case split.
5. **Zero samples.** Prove the constant-estimator error <=1/8 and the
   randomized strict-radius 1/128 obstruction with failure >=1/2. Retain
   anchor relations in the actual empty observation law.
6. **Preserved numerical evidence.** Present the original generic-probability
   pilot and its four geometric checks separately from the S046 finite
   formula/report study. Distinguish exact and numerical full-law coverage,
   Monte Carlo proportions, expected width, realized width and memory
   metrics. Retain the original 187/200 coverage fluctuation and the failed
   dependency attempt. Keep the exact-binomial practical-method decision.
7. **Formal and literature scope.** Map every substantive mathematical
   statement to exact accepted types and source identities, or explicitly
   mark elementary prose packaging. Use the original 797-report S046 GCP
   acceptance at proof commit 354fa1f8dc8746328077041ef79d3621837f99e7.
   Verify the original archive and current mapped sources without rerunning
   Lean. A changed substantive endpoint would require GCP acceptance.

The paper may include one plot of the stated analytic scale s(n,R), clearly
labeled as a formula illustration, not a new simulation or observed error.
No new experiment or expanded theorem is needed for this preparation.

## Source editions and limitations

Reuse the completed full Clopper-Pearson and Aronow-Lee article/supplement
reviews. Related partial-identification context uses the actually inspected
Imbens-Manski 2003 working paper, Stoye's 2008 preprint and Tudball et al.'s
v4/journal-and-supplement comparison. Bibliographic metadata can be refreshed;
do not claim equality with unread journal editions or an exhaustive novelty
search. Purchased source PDFs remain private outside the repository/archive.

No shortest interval, sharp identified set within K, optimal constants,
monetary calibration optimum, physical detector validation, operational
resource gain, absolute-scale recovery, curvature, higher-dimensional
reconstruction or new quantum-method claim is included. S044's negative
application decision and S047's known-method transfer do not block this
methods/theory manuscript, nor do they supply new application evidence.

## Delivery criteria

A self-contained TeX manuscript with complete proofs, bibliography,
reproducible tables/optional analytic figure, exact formal map, build and
source-verification scripts, reviewed PDF, every-page visual review, and a
frozen unpublished PDF/source package. Preserve all existing manuscripts,
published DOI artifacts, accepted proofs and frozen studies. Verify focused
commits and pushes in both repositories. Record a publication handoff;
preparation creates no DOI and performs no deposit/publication action.

Remaining to-do list: complete the draft/proof map, build and review every
page, freeze/verify the package, and deliver S048 preparation.
