# Finite-data reconstruction: bounded feasibility study

Scope version 1, 2026-10-08, planning S030/E002; proposed execution S031. Owner: Quantyra Space under Daniel Eric Fredriksen's research direction. Baseline repository revision: `a7f12b6b898b3a5d9c3532883c3a99214dce0b56`. This specification is complete when its model, obligations, evaluation and decision rules are reviewable. The study itself has not run. The [evaluation protocol](finite-data-feasibility-protocol.json) fixes the initial numerical design; the [literature matrix](finite-data-feasibility-literature.md) distinguishes inspected evidence from the pending comparison.

The research question is whether one finite causal order admits materially better density reconstruction guarantees than our present certificates, and how much uncertainty is unavoidable. The two published papers and their accepted proofs remain intact. This project concerns the original 1+1 model, with uniform null-coordinate marginals. Genuine higher-dimensional reconstruction remains parked.

## 1. Fixed model and success target

Use exactly `InDensityClass` in [Model.lean](../QuantyraNullCone/Model.lean): rho is smooth on an open neighborhood of the closed unit square, lies in [1/2,3/2], has Euclidean Lipschitz constant at most 2, and both coordinate marginals equal one. This is the full class K. Smoothness has no additional uniform higher-derivative bound. If a proof uses the Lipschitz closure, establish the extension explicitly; do not assert compactness or attainment for smooth K itself.

Draw n iid points with density rho. Observe only their full strict directed order: i precedes j exactly when both coordinates increase. The mathematical observation is the directed-order isomorphism class; it includes neither latent coordinates nor their two rankings, and does not identify time reversal. An implementation may enumerate vertices to run the existing checked realizer algorithm, but must prove coverage for every permitted enumeration/realizer or supply an invariant selection rule. A latent sample is available to the synthetic evaluator only.

Let G={identity, transpose}. For a bounded measurable output histogram f define

    loss(f,rho) = min_(S in G) sup_(x in [0,1]^2) |f(x)-rho(Sx)|.

One S must work over the entire square and for every simultaneous claim in a report. The output need not lie in smooth K and is not automatically a reconstructed Lorentzian metric. Retain closed-boundary coverage via an explicit half-open partition convention and the true density's continuity.

Primary theorem target: for every rho in K and supported n, a procedure using only the order, n and a preselected delta returns bands L,U with

    Pr_rho{there exists S in G such that for every x,
           L(P,x) <= rho(Sx) <= U(P,x)} >= 1-delta.

The simultaneous event must also support any reported estimator error. Numerical failure/failed certificate means a documented conservative fallback. With full-range bands and f=1, the fallback has deterministic error at most 1/2. Do not infer coverage conditional on acceptance from an unconditional accepted-output failure theorem. Report acceptance/fallback rates separately. Primary evaluation fixes delta=1/20; the proof should expose its valid delta and n domain rather than promise all parameters without support.

The no-data comparator is f=1 with error <=1/2, and bands [1/2,3/2] of width one. Current [S020 certificates](finite-data-sharpening-audit.md) beat the CDF prior radius 1/8 in three n=3072 examples, but all examined k=8 density widths and histogram error certificates remain one. This is evidence about those methods/settings, not a minimax impossibility. Existing [S024 mathematical certification](density-report-certification.md) does not make the bands informative or certify the entire Python runtime.

## 2. Work package A: prior work and a precise contribution

Complete the literature matrix before implementing a new estimator. Compare observations (coordinates, paired ranks, or only a partial order), density class, loss, boundary treatment, finite versus asymptotic probability, constants, computation and symmetry. Read the relevant theorem and proof, record exact pages/versions and mark which hypotheses transfer. Screen both rank-based copula estimation and uniform-norm density estimation, in addition to the already inspected Winkler realizer results. Search later work and citations as of execution; the current screen is not exhaustive.

Deliver `notes/finite-data-feasibility-comparison.md` with a claim-by-claim novelty/adaptation table. The strongest candidate contribution is a finite order-only guarantee accounting for realizer ambiguity and useful density uncertainty, or a justified limit for that exact observation/class/loss. A known copula estimator, a different loss, formalization alone, or an immediate consequence of an existing theorem is not silently presented as a new statistical result. If prior work already settles our exact target, record it and decide whether a bounded implementation/certification contribution merits a separately stated project.

## 3. Work package B: local-mass confidence route

Primary candidate: retain the existing original-incomparability-graph forcing certificate and replace global-CDF-to-density conversion with directly certified cell masses. The following is a proof blueprint, not a newly accepted theorem.

For the reconstructed normalized rank point r_i and unresolved degree d_i, let I_j={i:d_i<=j} and b_j=1-|I_j|/n. Existing forcing soundness supplies a single global axis alignment for all cutoffs j. On a simultaneous marginal event with error epsilon_m, the retained points should satisfy coordinate error at most s_j=j/n+epsilon_m under that alignment.

For a fixed cell R, define R^-s by erosion and R^+s by dilation, intersected with the square. Specify strict/inclusive boundaries consistently; handle empty erosions and s>=1. The candidate deterministic bracket is

    #{i in I_j : r_i in R^-s_j}/n
        <= latent empirical mass of the aligned cell R
        <= #{i in I_j : r_i in R^+s_j}/n + b_j.

Prove this bracket for every cell, cutoff and realizer on one event. The central opportunity is that observed boundary-strip counts can be smaller than a global CDF error. The empirical mass on the middle of this display is an analytical quantity, never an estimator input.

Use either (B1) finite variance-sensitive concentration for fixed cell counts, with justified variance bounds such as population cell mass <=(3/2) area(R), or (B2) exact binomial-tail inversion with conservative rational arithmetic. Inspect and verify the chosen concentration theorem, including constants and finite conditions. The middle counts are iid Bernoulli sums for fixed population cells; reconstructed points are not iid. Data-dependent trimming cannot be treated as an independent sample. Explain explicitly why the chosen simultaneous event permits optimization over j; pay a selection penalty if needed. Any grids, confidence allocations, tuning rules or additional rectangles outside that event require their own control. Transposed grids must be covered by the same event or an explicit allocation.

Allocate delta_m+delta_cell<=delta before sampling. Intersect valid lower/upper cell-mass constraints across supported j, add existing density/marginal/Lipschitz restrictions, and use the existing rational weak-duality checker where possible. Outward rounding, solver residuals, inconsistent restrictions and fallback behavior must be proved. Divide by cell area only after mass bounds are valid. Retain the existing valid cell-average-to-point expansion of 2/k, or prove any sharper replacement; do not hide this deterministic contribution to width.

Deliver `notes/finite-data-local-mass-feasibility.md`: complete finite inequalities, explicit failure budget, implementation/checker contract, a comparison with the old bound, and a list of unresolved obligations. Inspect at most these two calibration variants in the initial cycle. An asymptotic upper rate requires a proved high-probability bound on realizer ambiguity across K; favorable observed d_i in a few samples is insufficient. No improved exponent is promised by this scope.

## 4. Work package C: information limits

Define the law pi_n^rho of the actual single n-point directed order and study minimax estimation under the same loss. First seek a two-point construction inside full K: start from smooth, bounded perturbations with zero integral in each coordinate, preserving both marginals. Check positivity/range, normalization, neighborhood smoothness, the Euclidean Lipschitz constant and separation after both elements of G. An asymmetric alternative and its transpose are not distinguishable targets under this loss.

For rho_0,rho_1 with quotient separation strictly greater than 2epsilon, derive the testing-to-estimation reduction. With TV normalized to [0,1], the intended lower-bound form is

    inf_estimator max_(i=0,1) Pr_(rho_i){loss(estimator,rho_i)>=epsilon}
        >= (1-TV(pi_n^rho_0,pi_n^rho_1))/2,

with boundary inequalities and measurable decision sets verified in the final proof. State the exact range of n, epsilon and constants. Derive the appropriate consequence for 95% confidence radius; do not conflate expected risk with high-probability error or a confidence-band width lower bound without a separate reduction.

A useful first route is data processing from fully observed iid samples: establish the pushforward map to the order, bound product-sample divergence, and justify the TV/divergence inequality used. A valid lower bound for this same K and loss transfers to the less informative order observation. A theorem for a larger density class does not automatically give a lower bound on K. Such a transferred bound does not by itself demonstrate an additional cost of observing only order. Proving that extra cost would require a sharper order-law comparison. Overlapping suborders are dependent and cannot be counted as independent replicate observations.

If two points are insufficient to answer the rate question, record the missing multi-alternative packing/Fano argument as an unresolved extension; do not silently promise matching minimax rates. Compare lower and upper bounds only after matching class, loss, confidence convention and sample experiment. Deliver `notes/finite-data-information-limit.md`, labeling a proved limitation, a conditional candidate or a failed route accurately. Failure to construct a lower bound is not evidence that no obstruction exists.

## 5. Work package D: evaluation with a frozen protocol

Only execute a candidate after its mathematical coverage argument and checker contract have passed the internal source/assumption audit. The machine-readable [protocol](finite-data-feasibility-protocol.json) defines two stages: a ten-case pilot using five fixed densities at n=512,3072, followed, if warranted, by eighty fresh paired confirmation samples (five densities, two sizes, eight seeds). These are repeated synthetic experiments, each with exactly one order as estimator input.

Use flat, FGM coefficients +/-1/2 and asymmetric coefficients +/-1/4, with formulas fixed in the protocol and implemented in `tools/benchmark_finite_data.py`. Verify each family's K membership before using it. Primary mesh is k=8. Compare the frozen candidate, the existing `split-dkw` implementation on identical orders, and the no-data baseline. Known-coordinate and known-rank variants are diagnostics only. They can separate information lost in realizer recovery from calibration/regularization effects, but cannot establish order-only performance.

Preserve samples by seed and order hash, code/dependency hashes, exact rational certificates, chosen cutoffs and every fallback/failure. Measure maximum and mean point-band width, the fraction of cells narrowed, certified global error, actual error, simultaneous coverage in one global orientation, order-construction/estimation/verification time, total peak RSS and certificate bytes. The existing benchmark's Python-traced memory does not measure total RSS. Validate true cell extrema analytically for these polynomial families; a dense evaluation grid alone does not prove full-square coverage.

For width-derived error, use the band's midpoint and justify error <=half its maximum width on the simultaneous event. Do not attach that radius to a different histogram without proof. Coverage counts include fallback runs; report fallback frequency and informative-output coverage separately without claiming conditional guarantees. Provide binomial uncertainty for repeated-sample diagnostics. These simulations cannot prove uniform coverage over K.

Before confirmation, freeze one candidate version and all tuning. The protocol fixes fresh seed namespaces, preventing reuse of the published S019/S020 examples or pilot-driven cherry-picking. Any amendment gets a dated reason and is frozen before new confirmation samples are generated; do not rewrite the original protocol after looking at those results.

Deliver a new comparison runner, candidate/checker code only as needed, `evidence/finite-data/feasibility-v1/` with a complete/partial terminal manifest and raw diagnostics, and `notes/finite-data-feasibility-results.md`. These are planned paths, not currently available commands or results. Keep old reports/checkers valid. Execute the existing exhaustive graph/rational-certificate regressions and add meaningful corruption/boundary tests for any new checker obligations.

## 6. Resource bounds and stopping rules

Scope work itself runs no experiments, Lean or cloud jobs. The proposed execution retains existing input caps: n<=4096, k<=16, input JSON<=64 MiB, certificate JSON<=512 MiB. The initial comparison uses n<=3072 and k=8; sample-size or mesh expansion is a new scoped decision, not the default response to wide bands.

Proposed execution ceiling: 12 hours cumulative Python experiment time (sum of all run durations, including pilot, confirmation, oracle diagnostics and memory repeats), 10 minutes per estimator run and 4 GiB total process-tree RSS per run, including native solver memory. Confirm the selected host can enforce and measure these before execution. Stop and retain a partial outcome on resource exhaustion; never reinterpret a timeout/OOM as a mathematical impossibility. Pilot timing estimates must show that the remaining planned comparison fits; otherwise return a resource no-go without silently increasing caps. Exclude repeated memory-profile runs from independent trial counts. No new paid compute commitment is made by this specification.

The initial cycle has one literature disposition, the two local-count calibration candidates, one two-point lower-bound construction attempt and one pilot/confirmation protocol. Missing key lemmas are explicit failure outcomes. A substantially different estimator, a higher-dimensional gauge, noisy orders or a new density class requires a new scope rather than endless expansion of S031.

## 7. Continue, stop or pivot

| Outcome | Evidence required | Decision |
| --- | --- | --- |
| Practical continuation | Full-K finite coverage proof and verified checker; at n=3072, in each of the four nonconstant prespecified densities, at least 6 of 8 fresh trials have maximum point-band width <=0.90, hence a justified midpoint global radius <=0.45; all selected cases, failures and coverage diagnostics reported within resource limits | Develop the substantive method/theorem and scope GCP certification. These are operational research thresholds, not proof of typical performance or optimality. |
| Theoretical continuation | A substantial, literature-distinguished improvement of the uniform upper guarantee, or a fully proved lower bound that answers the stated accuracy/sample-size question; exact constants/range or a genuinely resolved rate gap identified | Continue the theorem/limits project even if the practical branch fails, stating its limited practical reach. A routine known lower bound is a benchmark, not automatically a paper. |
| Intermediate only | Smaller CDF radius, narrower mean bands while worst-case width stays one, good oracle/latent results, favorable sampled errors without a valid confidence theorem, or small constant changes with no meaningful consequence | Retain diagnostics; the main reconstruction target remains unmet. No automatic third-paper or certification campaign. |
| No-go / pivot | Prior work subsumes the candidate; both bounded proof routes lack the required lemma; only intermediate improvements remain after the cycle; or the resource plan cannot complete | Close S031 with the specific reason and preserved evidence. Recommend parking active development and comparing new topics. Do not call an algorithmic failure an information-theoretic impossibility. |

A lower-bound outcome must concern all estimators in the specified observation model, not merely the existing LP. A partial proof can justify a precisely bounded next lemma only if the final decision explains why it would change the research outcome; it is not a completed positive result. All three requested strands receive a disposition even if one gate stops costly numerical work.

## 8. Handoff and claims

Execution S031 is proposed and not started. Its final decision report must map every obligation above to a proof/source, an experiment/checker receipt, or an explicit failed/deferred disposition. Formal Lean work follows a selected, stable mathematical result and a separately scoped certification story. All Lean/Lake development and acceptance must run on remote GCP, using the pinned dependencies, immutable source capture, root build, exact type/axiom audits, retained logs and task-owned instance cleanup. Existing GCP acceptance applies only to existing theorems.

Open-source decentralized informal review and downstream testing remain the workflow. No specialist review, adoption milestone, DOI, journal submission or manuscript drafting is part of this feasibility scope. No higher-dimensional, noisy-order, curvature, engineering or physical-performance claim is implied.

Remaining to-do list: none for S030 specification once delivered; S031 execution remains proposed, with literature comparison, both proof routes, bounded evaluation and final decision outstanding.
